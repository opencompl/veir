module

public import Veir.Rewriter.Basic
public import Veir.Rewriter.LinkedList.WellFormed

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
  [HasBuffedOpCode OpInfo]

@[grind .]
theorem Rewriter.insertOp?_WellFormed
    (ctx : Sim.IRContext OpInfo) (newOp : Sim.OperationPtr) (ip : InsertPoint)
    (newOpIn : newOp.InBounds ctx)
    (ipIn : ip.InBounds ctx.spec)
    (ctxIn : ctx.spec.FieldsInBounds)
    (ipRepr : ip.IsRepr)
    (wf : ctx.spec.WellFormed)
    (heq : Rewriter.insertOp? ctx newOp ip newOpIn ipIn ctxIn ipRepr = some newCtx) :
    newCtx.spec.WellFormed := by
  simp only [Rewriter.insertOp?_def, Rewriter.insertOp?Sim] at heq
  split at heq
  · simp at heq
  · rename_i parent hParent
    have hParentIB : (ip.block ctx ipIn ipRepr).InBounds ctx :=
      InsertPoint.block_InBounds ctxIn ipIn ipRepr ipIn
    have hParentSpec : (ip.block ctx ipIn ipRepr).spec = some parent.spec :=
      Sim.OptionBlockPtr.toOption_some hParentIB hParent
    have hBlock : ip.block! ctx.spec = some parent.spec := by
      rw [InsertPoint.block!_eq_block ip ctx ipIn ipRepr]
      exact hParentSpec
    apply Sim.IRContext.wellFormed_OperationPtr_linkBetweenWithParent wf heq
      (ip := ip) <;>
      grind [Option.maybe₁_def]

end Veir
