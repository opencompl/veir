import Veir.Rewriter.WellFormed.Rewriter.Operation
import Veir.Rewriter.WellFormed.Rewriter.Value

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

theorem IRContext.wellFormed_replaceOpResults :
    ctx.WellFormed →
    fromOp ≠ toOp →
    Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo ctxInBounds =
      some newCtx →
    newCtx.WellFormed := by
  intro ctxWf neOps
  induction idx generalizing ctx
  case zero => grind [Rewriter.replaceOpResults]
  case succ idx hind =>
    simp only [Rewriter.replaceOpResults]
    grind [Option.maybe₁, Rewriter.replaceValue?_WellFormed]

theorem OpResult.hasUses_replaceOpResults_self_ge :
    ctx.WellFormed →
    fromOp ≠ toOp →
    Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo ctxInBounds =
      some newCtx →
    ∀ i ≥ idx, i < fromOp.getNumResults! ctx → i < toOp.getNumResults! ctx →
    ValuePtr.hasUses! (fromOp.getResult i) newCtx = ValuePtr.hasUses! (fromOp.getResult i) ctx := by
  intro ctxWf neOps
  induction idx generalizing ctx
  case zero => grind [Rewriter.replaceOpResults]
  case succ idx hind =>
    simp only [Rewriter.replaceOpResults]
    split; grind; rename_i ctx' hctx'
    intro hNewCtx i hi hifromOp hitoOp
    simp only [ge_iff_le] at hi
    have ctx'Wf : ctx'.WellFormed := by grind [Option.maybe₁, Rewriter.replaceValue?_WellFormed]
    have valueInBounds : (ValuePtr.opResult (fromOp.getResult i)).InBounds ctx := by grind
    have := ValuePtr.hasUses!_replaceValue_otherValue ctxWf hctx'
      (by grind) _ valueInBounds (by grind) (by grind)
    grind

theorem OpResult.hasUses_replaceOpResults_self :
    ctx.WellFormed →
    fromOp ≠ toOp →
    Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo ctxInBounds =
      some newCtx →
    ∀ i < idx, ValuePtr.hasUses! (fromOp.getResult i) newCtx = false := by
  intro ctxWf neOps
  induction idx generalizing ctx
  case zero => grind
  case succ idx hind =>
    simp only [Rewriter.replaceOpResults]
    split; grind; rename_i ctx' hctx'
    intro hNewCtx i hi
    simp only [Nat.lt_succ_iff_lt_or_eq] at hi
    have ctx'Wf : ctx'.WellFormed := by
      grind [Option.maybe₁, Rewriter.replaceValue?_WellFormed]
    cases hi
    · grind [ValuePtr.hasUses!_replaceValue_oldValue]
    · subst i
      simp only [OpResult.hasUses_replaceOpResults_self_ge ctx'Wf
        neOps hNewCtx idx (by grind) (by grind) (by grind)]
      grind [ValuePtr.hasUses!_replaceValue_oldValue]

@[grind →]
theorem OperationPtr.getNumResults!_replaceOpResults :
    Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo ctxInBounds =
      some newCtx →
    fromOp.getNumResults! newCtx = fromOp.getNumResults! ctx := by
  induction idx generalizing ctx
  case zero => grind [Rewriter.replaceOpResults]
  case succ idx hind =>
    simp only [Rewriter.replaceOpResults]
    grind

theorem OperationPtr.hasUses_replaceOpResults :
    ctx.WellFormed →
    fromOp ≠ toOp →
    Rewriter.replaceOpResults ctx fromOp toOp (fromOp.getNumResults! ctx) fromOpIB
      toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    fromOp.hasUses! newCtx = false := by
  grind [OpResult.hasUses_replaceOpResults_self,
    OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]

theorem OperationPtr.getNumRegions!_replaceOpResults :
    Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo ctxInBounds =
      some newCtx →
    fromOp.getNumRegions! newCtx = fromOp.getNumRegions! ctx := by
  induction idx generalizing ctx
  case zero => grind [Rewriter.replaceOpResults]
  case succ idx hind =>
    simp only [Rewriter.replaceOpResults]
    grind

grind_pattern OperationPtr.getNumRegions!_replaceOpResults =>
  Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo ctxInBounds, some newCtx, fromOp.getNumRegions! newCtx

theorem IRContext.fieldsInBounds_replaceOp? :
    ctx.WellFormed →
    oldOp ≠ newOp →
    oldOp.getNumRegions! ctx = 0 →
    Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar = some newCtx →
    newCtx.FieldsInBounds := by
  intro ctxWf neOps noRegions
  simp only [Rewriter.replaceOp?]
  split; grind; rename_i hNumResults
  split; grind; rename_i ctx' hctx'
  simp only [Option.some.injEq]
  intro h; subst newCtx
  have : oldOp.hasUses! ctx' = false := by grind [OperationPtr.hasUses_replaceOpResults]
  have ctx'Wf : ctx'.WellFormed := by grind [IRContext.wellFormed_replaceOpResults]
  grind [Rewriter.eraseOp_WellFormed]

theorem IRContext.wellFormed_replaceOp? :
    ctx.WellFormed →
    oldOp ≠ newOp →
    oldOp.getNumRegions! ctx = 0 →
    Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar = some newCtx →
    newCtx.WellFormed := by
  intro ctxWf neOps noRegions
  simp only [Rewriter.replaceOp?]
  split; grind; rename_i hNumResults
  split; grind; rename_i ctx' hctx'
  simp only [Option.some.injEq]
  intro hnewCtx; subst newCtx
  apply Rewriter.eraseOp_WellFormed
  · grind [IRContext.wellFormed_replaceOpResults]
  · grind
  · grind [OperationPtr.hasUses_replaceOpResults]

end Veir
