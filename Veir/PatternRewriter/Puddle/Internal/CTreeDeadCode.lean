module

public import Veir.PatternRewriter.Puddle.Internal.DriverStructure
public import Veir.PatternRewriter.Puddle.Internal.CTreeFunctionRefinement
public import Veir.Interfaces.DeadCodeInterfaces
public import Veir.Verifier
import all Veir.Verifier
import all Veir.Verifier.Basic
import all Veir.GlobalOpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.IR.Basic
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.PatternRewriter.Basic

public import Veir.PatternRewriter.CTreeDeadCode

namespace Veir
public section

/-- The module opcode establishes pointer bounds independently of verification. -/
theorem module_inBounds_of_opcode {ctx : WfIRContext OpCode} {moduleOp : OperationPtr}
    (code : moduleOp.getOpType! ctx.raw = .builtin .module) : moduleOp.InBounds ctx.raw := by
  by_cases inside : moduleOp.InBounds ctx.raw
  · exact inside
  · simp only [OperationPtr.getOpType!, OperationPtr.get!_of_not_inBounds inside] at code
    contradiction

/-- A verified builtin module owns its single body region and cannot be trivially dead. -/
theorem verified_module_numRegions {ctx : WfIRContext OpCode} {moduleOp : OperationPtr}
    (verified : ctx.Verified moduleOp)
    (code : moduleOp.getOpType! ctx.raw = .builtin .module) : moduleOp.getNumRegions! ctx.raw = 1 := by
  have localVerified := OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants verified
    (module_inBounds_of_opcode code)
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants, HasOpInfo.verifyLocalInvariants,
    OpCode.verifyLocalInvariants, Builtin.verifyLocalInvariants, OperationPtr.verifyOpCounts,
    OperationPtr.verifyNonOperandCounts, ← OperationPtr.getOpType!_eq_getOpType, code, ne_eq,
    bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, ite_not] at localVerified
  grind

/-- Erasing a trivially dead operation preserves the module root's opcode and parent header.
This structural theorem does not require the semantic erasure axiom. -/
theorem triviallyDead_erase_module_header {ctx : WfIRContext OpCode} {moduleOp op : OperationPtr}
    (verified : ctx.Verified moduleOp)
    (moduleCode : moduleOp.getOpType! ctx.raw = .builtin .module)
    (moduleNoParent : moduleOp.getParent! ctx.raw = none)
    (opIn : op.InBounds ctx.raw) (dead : op.isTriviallyDead ctx.raw) :
    let result := WfRewriter.eraseOp ctx op dead.1 dead.2.1 opIn
    moduleOp.getOpType! result.raw = .builtin .module ∧ moduleOp.getParent! result.raw = none := by
  have moduleIn := module_inBounds_of_opcode moduleCode
  have different : moduleOp ≠ op := by
    intro same
    have regionCount := verified_module_numRegions verified moduleCode
    rw [same, dead.1] at regionCount
    contradiction
  have header := Puddle.operationHeaderPreserved_of_eraseOp (regions := dead.1) (unused := dead.2.1)
    (rootIn := opIn) different moduleIn
  exact ⟨header.opcode.trans moduleCode, header.parent.trans moduleNoParent⟩

/-- Checked rewriter erasure performs exactly the corresponding context erasure. -/
theorem PatternRewriter.eraseOp_ctx {rewriter : PatternRewriter OpCode} {op : OperationPtr}
    (opIn : op.InBounds rewriter.ctx.raw) (dead : op.isTriviallyDead rewriter.ctx.raw) :
    (rewriter.eraseOp op dead.1 dead.2.1 opIn).ctx =
      WfRewriter.eraseOp rewriter.ctx op dead.1 dead.2.1 opIn := by
  simp [PatternRewriter.eraseOp]

end
end Veir
