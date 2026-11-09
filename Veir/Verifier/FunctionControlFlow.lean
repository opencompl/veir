module

public import Veir.Verifier
import all Veir.Verifier
import all Veir.GlobalOpInfo
import all Veir.Dialects.Func.OpInfo

public section
namespace Veir

/-- A verified nonterminator in a block requiring a terminator has a following operation. -/
private theorem WfIRContext.Verified.nonterminator_hasNext
    {ctx : WfIRContext OpCode} {moduleOp op : OperationPtr} {block : BlockPtr}
    (verified : ctx.Verified moduleOp) (blockIn : block.InBounds ctx.raw)
    (opParent : op.getParent! ctx.raw = some block)
    (required : BlockPtr.mayBeValidWithoutTerminator block ctx blockIn = false)
    (nonterm : HasOpInfo.isTerminator (op.getOpType! ctx.raw) = false) :
    ∃ next, op.getNextOp! ctx.raw = some next := by
  cases next : op.getNextOp! ctx.raw with
  | some following => exact ⟨following, rfl⟩
  | none =>
    change (op.getOpType! ctx.raw).isTerminator = false at nonterm
    have last : block.getLastOp! ctx.raw = some op := by grind
    have checked := verified.verifyTerminator_eq_ok blockIn
    simp only [BlockPtr.verifyTerminator, required, Bool.false_eq_true, ↓reduceIte,
      ← BlockPtr.getLastOp!_eq_getLastOp blockIn, last, nonterm] at checked
    cases checked

/-- In a verified `func.func` body a nonterminator cannot end its block. -/
theorem WfIRContext.Verified.nonterminator_hasNext_in_func
    {ctx : WfIRContext OpCode} {moduleOp function op : OperationPtr}
    {region : RegionPtr} {block : BlockPtr}
    (verified : ctx.Verified moduleOp) (blockIn : block.InBounds ctx.raw)
    (functionCode : function.getOpType! ctx.raw = .func .func)
    (regionParent : region.getParent! ctx.raw = some function)
    (blockParent : block.getParent! ctx.raw = some region)
    (opParent : op.getParent! ctx.raw = some block)
    (nonterm : HasOpInfo.isTerminator (op.getOpType! ctx.raw) = false) :
    ∃ next, op.getNextOp! ctx.raw = some next := by
  apply verified.nonterminator_hasNext blockIn opParent ?_ nonterm
  have required : region.hasNoTerminator ctx = false := by
    simp only [RegionPtr.hasNoTerminator, regionParent, functionCode]
    rfl
  simp [BlockPtr.mayBeValidWithoutTerminator, ← BlockPtr.getParent!_eq_getParent blockIn,
    blockParent, regionParent, required]

end Veir
