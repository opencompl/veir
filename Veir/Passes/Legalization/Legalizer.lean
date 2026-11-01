module

public import Veir.Passes.Legalization.LegalizerInfo
import Veir.PatternRewriter.Driver
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

/-- Applies the action of the rules to `op`. Does not match legal operations or illegal ones. -/
private def legalizeInstrStep (info : LegalizerInfo) : LocalRewritePattern OpCode :=
  fun ctx op => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx.raw) | return (ctx, none)
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
  -- Folding can undo legalization: `g_trunc (g_constant)` from `widenConstant` folds back to the
  -- narrow constant it widened, which would then be widened again, forever.
  let some ctx := RewritePattern.applyInContext pattern ctx (fold := false)
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
