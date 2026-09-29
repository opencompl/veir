module

public import Veir.Passes.Legalization.LegalizerInfo
import Veir.PatternRewriter.Basic
import Veir.Passes.Legalization.LegalizerHelper
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
    let .widenScalar typeIdx newType := info.getAction ctx.raw op opcode | return (ctx, none)
    let some pattern := widenScalar? opcode typeIdx newType | return (ctx, none)
    pattern.interpret ctx op

/-- The error message for `op`, which could not be legalized with `action`. -/
private def illegalReason (ctx : IRContext OpCode) (op : OperationPtr) (opcode : GMIR)
    (action : LegalizeAction) : String :=
  let name := String.fromUTF8! (IsOpCode.name (op.getOpType! ctx))
  let types := opcode.getTypeGroupTypes! op ctx
  let reason := match action, types.find? fun type => (LLT.ofType? type).isNone with
    | .widenScalar typeIdx _, _ => s!"widening type group {typeIdx} is not implemented"
    | _, some type => s!"unsupported type {type}"
    | _, none => "no legalization rule matches"
  s!"unable to legalize {name}: {reason}"

/-- Legalizes all gMIR operations of `ctx`. Fails if one of them remains illegal. -/
def legalize (info : LegalizerInfo) (ctx : WfIRContext OpCode) :
    Except String (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[.fromLocalRewrite info.legalizeInstrStep]
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
