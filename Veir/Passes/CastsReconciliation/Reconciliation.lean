module

public import Veir.Pass
public import Veir.PatternRewriter.Puddle.Builders
import Veir.Passes.Matching
import Veir.Passes.DCE.dce
import Veir.PatternRewriter.Puddle.Execution

namespace Veir

/--
  We reconcile casts in `builtin.unrealized_conversion_cast` operations for `!riscv.reg` and `i64`
  types, in the `reg -> i64 -> reg` direction. `Reg.toInt` is never poison and `Int.toReg` inverts
  it at width 64, so the round trip is the identity.
-/
def isRegToI64RoundTrip (inputType interType : TypeAttr): Bool :=
 match inputType.val, interType.val with
  | .registerType _, .integerType x => x.bitwidth = 64
  | _, _ => false

/-!
 We reconcile casts in `builtin.unrealized_conversion_cast` operations for `!llvm.ptr` and `!riscv.reg` types.
 This cast assumes that the `.llvmPointerType` is bit-wide.
-/
def isRiscvRegToPtrCast (inputType interType : TypeAttr): Bool :=
 match inputType.val, interType.val with
  | .llvmPointerType _ , .registerType _ => true
  | .registerType _, .llvmPointerType _  => true
  | _, _ => false


/- We reconcile cast from `!mod_arith.int< q: iN> to iM (and back) for any M -/
def isPreservingModArithToIntCast (inputType interType : TypeAttr) : Bool :=
  match inputType.val, interType.val with
  | .modArithType _, .integerType _ => True
  | .integerType _, .modArithType _ => True
  | _, _ => false

/- We reconcile casts from `!cir.int<s|u, N>` to `iN` and from `!cir.bool` to `i1` (and back):
   the lowering keeps every bit, so the round trip is the identity. -/
def isCirToIntRoundTrip (inputType interType : TypeAttr) : Bool :=
  match inputType.val, interType.val with
  | .cirIntType it, .integerType i => i.bitwidth = it.width
  | .integerType i, .cirIntType it => i.bitwidth = it.width
  | .cirBoolType _, .integerType i => i.bitwidth = 1
  | .integerType i, .cirBoolType _ => i.bitwidth = 1
  | _, _ => false


/-- Reconciles round-trip casts of the form X->Y->X if allowed for these types by `legal X Y`.

  The pattern matches on the second cast, whose input has the intermediate type `Y`. Using the
  same type handle for the parent cast's input and the matched cast's result requires the round
  trip to return to its own input type.

  The parent cast is left in place: it is now dead, and DCE (run at the end of the pass) removes
  it. A Puddle pattern may only erase the matched operation. -/
public def reconcilePairingCast (legal : TypeAttr → TypeAttr → Bool) : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let inputType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let interType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let input ← Puddle.MatchProg.value inputType
      let parentCast ← Puddle.MatchProg.operation (.builtin .unrealized_conversion_cast)
          #[input] #[interType]
      let _ ← Puddle.MatchProg.root (.builtin .unrealized_conversion_cast)
          #[parentCast.res[0]!] #[inputType]
      Puddle.MatchProg.matchNative (inputType, interType)
          fun (inputType, interType) => legal inputType interType
      return input)
    pure
    (fun input => input)

def reconcileRegToI64 := (reconcilePairingCast isRegToI64RoundTrip).compile
def reconcileRegToPtr := (reconcilePairingCast isRiscvRegToPtrCast).compile
def reconcileModArithToInt := (reconcilePairingCast isPreservingModArithToIntCast).compile
def reconcileCirToInt := (reconcilePairingCast isCirToIntRoundTrip).compile

/-- Reconciles round-trip casts of the form !riscv.reg->iX->!riscv.reg
   using zext.b/w/h for 8/16/32-bit values, or slli+slri for other bitwidths.

  As in `reconcilePairingCastLocal`, the now-dead parent cast is left to DCE. -/
def reconcileRegIntCastLocal (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some input := matchCastOp op ctx.raw | return (ctx, none)
  /- Note that reconciliation matches on the second casting operation, so the input type of this op would be the intermediate type -/
  let interType := input.getType! ctx.raw
  let resultType := (op.getResult 0).getType! ctx.raw
  /- If the operand's parent is a cast operation -/
  let .opResult op' := input | return (ctx, none)
  let some parentInput := matchCastOp op'.op ctx.raw | return (ctx, none)
  /- And the result's type coincides with the parent operation operand's type -/
  let inputType := parentInput.getType! ctx.raw
  if resultType ≠ inputType then return (ctx, none)
  /- And the reconciliation involves the right types -/
  if inputType ≠ RegisterType.mk then return (ctx, none)
  let .integerType ⟨ interBw, _ ⟩ := interType.val | return (ctx, none)
  /- Replace the initial operation's output with a zero-extension of the parent's input -/
  match interBw with
  | 8 =>
      let (ctx, newOp) ← WfRewriter.createOp! ctx Riscv.zextb #[RegisterType.mk] #[parentInput]
        #[] #[] () none
      return (ctx, some (#[newOp], #[newOp.getResult 0]))
  | 16 =>
      let (ctx, newOp) ← WfRewriter.createOp! ctx Riscv.zexth #[RegisterType.mk] #[parentInput]
        #[] #[] () none
      return (ctx, some (#[newOp], #[newOp.getResult 0]))
  | 32 =>
      let (ctx, newOp) ← WfRewriter.createOp! ctx Riscv.zextw #[RegisterType.mk] #[parentInput]
        #[] #[] () none
      return (ctx, some (#[newOp], #[newOp.getResult 0]))
  | bw =>
      /- `i0` has no bits to preserve: the round trip is the constant zero, which neither
         `slli`/`srli` (whose 6-bit shift amount would wrap `64 - 0` to `0`) nor any other
         two-shift sequence computes. Leave such casts alone. -/
      if bw = 0 then return (ctx, none)
      /- for bitwidths with no dedicated instruction, shift left then right -/
      if bw >= 64 then none else
      let imm := BitVec.ofInt 64 (64-bw)
      let (ctx, shlOp) ← WfRewriter.createOp! ctx Riscv.slli #[RegisterType.mk] #[parentInput]
        #[] #[] (⟨imm⟩ : RISCVImmediateProperties) none
      let (ctx, srlOp) ← WfRewriter.createOp! ctx Riscv.srli #[RegisterType.mk]
        #[shlOp.getResult 0] #[] #[] (⟨imm⟩ : RISCVImmediateProperties) none
      return (ctx, some (#[shlOp, srlOp], #[srlOp.getResult 0]))


def CastReconcilePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    reconcileRegToI64.run,
    reconcileRegToPtr.run,
    reconcileModArithToInt.run,
    reconcileCirToInt.run,
    .fromLocalRewrite reconcileRegIntCastLocal]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying cast reconciliation"
  -- The patterns leave the (now dead) parent casts behind: `LocalRewritePattern` can only erase
  -- the matched operation. Clean them up here so the pass is self-contained.
  | some ctx =>
    match RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern #[eliminateDeadOp]) ctx with
    | none => throw "Error while applying DCE after cast reconciliation"
    | some ctx => pure ctx

public def CastReconcilePass : Pass OpCode :=
  { name := "reconcile-cast"
    description := "Reconcile round trips of casts that return to their own input type."
    run := fun _ => CastReconcilePass.impl }
