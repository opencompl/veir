module

public import Veir.Pass
import Veir.Passes.Matching
import Veir.Passes.DCE.dce

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
 This cast assums that the `.llvmPointerType` is bit-wide.
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


/-- Reconciles round-trip casts of the form X->Y->X if allowed for these types by `legal X Y`.

  The parent cast is left in place: it is now dead, and DCE (run at the end of the pass) removes
  it. A `LocalRewritePattern` may only erase the matched operation. -/
def reconcilePairingCastLocal (legal : TypeAttr → TypeAttr → Bool) (ctx : WfIRContext OpCode)
    (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some input := matchCastOp op ctx.raw | return (ctx, none)
  /- Note that reconciliation matches on the second casting operation, so the input type of this op would be the intermediate type -/
  let interType := input.getType! ctx.raw
  let resultType := ((op.getResult 0).get! ctx.raw).type
  /- If the operand's parent is a cast operation -/
  let .opResult op' := input | return (ctx, none)
  let some parentInput := matchCastOp op'.op ctx.raw | return (ctx, none)
  /- And the result's type coincides with the parent operation operand's type -/
  let inputType := parentInput.getType! ctx.raw
  if resultType ≠ inputType then return (ctx, none)
  /- And the reconciliation is legal -/
  if ¬ legal inputType interType then return (ctx, none)
  /- Replace the initial operation's output with the parent operation's input -/
  return (ctx, some (#[], #[parentInput]))

/-- Reconciles round-trip casts of the form !riscv.reg->iX->!riscv.reg
   using zext.b/w/h for 8/16/32-bit values, or slli+slri for other bitwidths.

  As in `reconcilePairingCastLocal`, the now-dead parent cast is left to DCE. -/
def reconcileRegIntCastLocal (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some input := matchCastOp op ctx.raw | return (ctx, none)
  /- Note that reconciliation matches on the second casting operation, so the input type of this op would be the intermediate type -/
  let interType := input.getType! ctx.raw
  let resultType := ((op.getResult 0).get! ctx.raw).type
  /- If the operand's parent is a cast operation -/
  let .opResult op' := input | return (ctx, none)
  let some parentInput := matchCastOp op'.op ctx.raw | return (ctx, none)
  /- And the result's type coincides with the parent operation operand's type -/
  let inputType := parentInput.getType! ctx.raw
  if resultType ≠ inputType then return (ctx, none)
  /- And the reconciliation involves the right types -/
  if inputType ≠ RegisterType.mk then return (ctx, none)
  let .integerType ⟨ interBw ⟩ := interType.val | return (ctx, none)
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
      let imm := IntegerAttr.mk (64-bw) (.mk 64)
      let (ctx, shlOp) ← WfRewriter.createOp! ctx Riscv.slli #[RegisterType.mk] #[parentInput]
        #[] #[] (⟨imm⟩ : RISCVImmediateProperties) none
      let (ctx, srlOp) ← WfRewriter.createOp! ctx Riscv.srli #[RegisterType.mk]
        #[shlOp.getResult 0] #[] #[] (⟨imm⟩ : RISCVImmediateProperties) none
      return (ctx, some (#[shlOp, srlOp], #[srlOp.getResult 0]))


def CastReconcilePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    .fromLocalRewrite (reconcilePairingCastLocal isRegToI64RoundTrip),
    .fromLocalRewrite (reconcilePairingCastLocal isRiscvRegToPtrCast),
    .fromLocalRewrite (reconcilePairingCastLocal isPreservingModArithToIntCast),
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
