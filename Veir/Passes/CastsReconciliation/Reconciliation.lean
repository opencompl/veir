module

public import Veir.Pass
public import Veir.PatternRewriter.Puddle.Builders
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

open Puddle in
/-- Match an unallocated-register round trip through an integer of an accepted width. -/
private def matchRegIntCast (widthMatches : Nat → Bool) :
    MatchProg.Builder (Handle OpCode .type × Handle OpCode .type × Handle OpCode .value) := do
  let regType ← MatchProg.type (Attr := RegisterType) (·.index.isNone)
  let interType ← MatchProg.type (Attr := IntegerType) (fun t => widthMatches t.bitwidth)
  let input ← MatchProg.value regType
  let parent ← MatchProg.operation (.builtin .unrealized_conversion_cast) #[input] #[interType]
  let _ ← MatchProg.root (.builtin .unrealized_conversion_cast) #[parent.res[0]!] #[regType]
  return (regType, interType, input)

open Puddle in
/-- Reconcile an 8/16/32-bit register round trip with its dedicated zero extension. -/
private def reconcileRegIntExt (width : Nat) (opcode : Riscv)
    (props : propertiesOf (OpCode.riscv opcode)) : Pattern OpCode :=
  Pattern.Builder
    (matchRegIntCast (· = width))
    (fun (regType, _, input) =>
      CreateProg.operation (.riscv opcode) #[input] #[regType] props)
    (fun op => op)

open Puddle in
/-- Reconcile other narrow register round trips with two shifts; leave the parent cast to DCE. -/
private def reconcileRegIntShift : Pattern OpCode :=
  Pattern.Builder
    -- i0 needs a constant zero, which this two-shift sequence cannot compute.
    (matchRegIntCast fun bw => bw ≠ 0 && bw ≠ 8 && bw ≠ 16 && bw ≠ 32)
    (fun (regType, interType, input) => do
      let (leftProps, rightProps) ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.riscv .slli)) ×
            Handle OpCode (.prop (.riscv .srli))) interType fun type => do
        let type ← type.cast? IntegerType
        -- Preserve the existing error on over-wide casts. The identity rule handles i64 first.
        guard (type.bitwidth < 64)
        let props : RISCVImmediateProperties := ⟨BitVec.ofNat 64 (64 - type.bitwidth)⟩
        return (props, props)
      let left ← CreateProg.operation (.riscv .slli) #[input] #[regType] (.inr leftProps)
      CreateProg.operation (.riscv .srli) #[left.res[0]!] #[regType] (.inr rightProps))
    (fun op => op)

private def reconcileRegIntCasts : Array (Puddle.CompiledPattern OpCode) :=
  #[reconcileRegIntExt 8 .zextb (), reconcileRegIntExt 16 .zexth (),
    reconcileRegIntExt 32 .zextw (), reconcileRegIntShift].map (·.compile)


def CastReconcilePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern <| #[
    reconcileRegToI64.run,
    reconcileRegToPtr.run,
    reconcileModArithToInt.run,
    reconcileCirToInt.run] ++ reconcileRegIntCasts.map (·.run)
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
