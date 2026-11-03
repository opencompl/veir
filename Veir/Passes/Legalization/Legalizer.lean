module

public import Veir.Passes.Legalization.LegalizerInfo
import Veir.PatternRewriter.Basic
import Veir.Passes.Legalization.LegalizerHelper
import Veir.Passes.Legalization.LegalizationArtifactCombiner
import Veir.PatternRewriter.Puddle.Execution

/-!
# GMIR Legalizer

This file implements the target-independent legalizer. A target builds its legalization pass by
calling `LegalizerInfo.legalize` with its target specific `LegalizerInfo`.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/Legalizer.h
-/

namespace Veir

public section

namespace LegalizerInfo

/-- Whether `opcode` is an artifact, as in LLVM's `Legalizer.cpp`. -/
private def isArtifact : GMIR → Bool
  | .g_trunc | .g_zext | .g_anyext | .g_sext | .g_merge_values | .g_unmerge_values => true
  | _ => false

/-- Whether an operand of `op` is the result of a gMIR operation that is not legal yet. -/
private def hasIllegalSource (info : LegalizerInfo) (ctx : IRContext OpCode) (op : OperationPtr) :
    Bool :=
  (op.getOperands! ctx).any fun
    | .opResult result =>
      match toDialect? GMIR (result.op.getOpType! ctx) with
      | some opcode => !(info.getAction ctx result.op opcode matches .legal)
      | none => false
    | _ => false

/--
Applies the action of the rules to `op`. Does not match legal operations or illegal ones.

An artifact is not legalized while its source is still illegal. LLVM's legalizer legalizes all
other instructions before it combines artifacts, and only legalizes the artifacts it cannot combine.
Legalizing the source first may turn it into an artifact that the artifact combiner folds away,
e.g. widening a `g_icmp` under a `g_zext` leaves `g_zext (g_trunc (g_icmp))`.
-/
private def legalizeInstrStep (info : LegalizerInfo) : LocalRewritePattern OpCode :=
  fun ctx op => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx.raw) | return (ctx, none)
    if isArtifact opcode && hasIllegalSource info ctx.raw op then return (ctx, none)
    let pattern? : Option (LocalRewritePattern OpCode) := match info.getAction ctx.raw op opcode with
      | .widenScalar typeIdx width => widenScalar? opcode typeIdx width
      | .lower => (lower? opcode).map Puddle.Pattern.interpret
      | .custom => (info.legalizeCustom opcode).map Puddle.Pattern.interpret
      | .legal | .unsupported => none
    let some pattern := pattern? | return (ctx, none)
    pattern ctx op

/-- Combines the artifact `op` away with the first `tryCombineInstruction` pattern that applies. -/
private def combineArtifactStep : LocalRewritePattern OpCode :=
  fun ctx op => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx.raw) | return (ctx, none)
    go op (tryCombineInstruction opcode) ctx
where
  go (op : OperationPtr) : List (Puddle.Pattern OpCode) → WfIRContext OpCode →
      Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr))
    | [], ctx => some (ctx, none)
    | pattern :: patterns, ctx =>
      match pattern.interpret ctx op with
      | some (ctx, none) => go op patterns ctx
      | result => result

/-- The error message for `op`, which could not be legalized with `action`. -/
private def illegalReason (ctx : IRContext OpCode) (op : OperationPtr) (opcode : GMIR)
    (action : LegalizeAction) : String :=
  let name := String.fromUTF8! (IsOpCode.name (op.getOpType! ctx))
  let types := opcode.getTypeGroupTypes! op ctx
  let reason := match action, types.find? fun type => (LLT.ofType? type).isNone with
    | .widenScalar (.type idx) _, _ => s!"widening type group {idx} is not implemented"
    | .lower, _ => "the lowering is not implemented"
    | .custom, _ => "the custom legalization does not apply"
    | _, some type => s!"unsupported type {type}"
    | _, none => "no legalization rule matches"
  s!"unable to legalize {name}: {reason}"

/-- Legalizes all GMIR operations of `ctx`. Fails if one of them remains illegal. -/
def legalize (info : LegalizerInfo) (ctx : WfIRContext OpCode) :
    Except String (WfIRContext OpCode) := do
  -- As in LLVM, an artifact is combined before it is legalized.
  -- TODO: Use a proper worklist for artifacts.
  let pattern := RewritePattern.GreedyRewritePattern
    #[.fromLocalRewrite combineArtifactStep, .fromLocalRewrite info.legalizeInstrStep]
  let some ctx := RewritePattern.applyInContext pattern ctx
    | throw "error while applying legalization"
  -- The greedy rewriter does not report the operations it could not rewrite, so we check the
  -- legality of every operation afterwards.
  ctx.raw.forOpsDepM fun op _ => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx.raw) | return
    match info.getAction ctx.raw op opcode with
    | .legal => pure ()
    | action => throw (illegalReason ctx.raw op opcode action)
  return ctx

end LegalizerInfo

end

end Veir
