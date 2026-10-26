module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.Rewriter.GetSet
import Veir.Rewriter.WellFormed.Operation
import Veir.Rewriter.WellFormed.Value

public section

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
    grind [Option.maybe₁_def, Rewriter.replaceValue?_WellFormed]

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
    have ctx'Wf : ctx'.WellFormed := by grind [Option.maybe₁_def, Rewriter.replaceValue?_WellFormed]
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
      grind [Option.maybe₁_def, Rewriter.replaceValue?_WellFormed]
    cases hi
    · grind [ValuePtr.hasUses!_replaceValue_oldValue]
    · subst i
      simp only [OpResult.hasUses_replaceOpResults_self_ge ctx'Wf
        neOps hNewCtx idx (by grind) (by grind) (by grind)]
      grind [ValuePtr.hasUses!_replaceValue_oldValue]

theorem OperationPtr.getNumOperands!_replaceOpResults {op : OperationPtr} :
    Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo ctxInBounds =
      some newCtx →
    op.getNumOperands! newCtx = op.getNumOperands! ctx := by
  induction idx generalizing ctx
  case zero => grind [Rewriter.replaceOpResults]
  case succ idx hind =>
    simp only [Rewriter.replaceOpResults]
    grind

/--
  `replaceOpResults` replaces, in every operand, each of the first `index` results of `fromOp`
  by the result of `toOp` at the same index, and leaves every other operand as it was.
-/
theorem OperationPtr.getOperand_replaceOpResults {op : OperationPtr}
    (hCtx : IRContext.WellFormed ctx) (hne : fromOp ≠ toOp)
    (h : Rewriter.replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds =
      some newCtx)
    (opIn : op.InBounds ctx) (idxIn : idx < op.getNumOperands! ctx)
    (opIn' : op.InBounds newCtx) (idxIn' : idx < op.getNumOperands! newCtx) :
    OperationPtr.getOperand op newCtx idx opIn' idxIn' =
    let operand := OperationPtr.getOperand op ctx idx opIn idxIn
    match operand with
    | ValuePtr.opResult { op := op', index := idx' } =>
      if op' = fromOp ∧ idx' < index then ValuePtr.opResult { op := toOp, index := idx' } else operand
    | _ => operand := by
  induction index generalizing ctx with
  | zero =>
    simp only [Rewriter.replaceOpResults, Option.some.injEq] at h
    subst h
    simp only []
    split <;> simp_all
  | succ index ih =>
    simp only [Rewriter.replaceOpResults] at h
    split at h
    · simp at h
    · next c hc =>
      have hwf : IRContext.WellFormed c := by
        grind [Option.maybe₁_def, Rewriter.replaceValue?_WellFormed]
      have hneq : ((fromOp.getResult index : OpResultPtr) : ValuePtr) ≠
          ((toOp.getResult index : OpResultPtr) : ValuePtr) := by
        intro h
        have h := ValuePtr.opResult.inj h
        have := congrArg OpResultPtr.op h
        simp only [OperationPtr.getResult_op] at this
        exact hne this
      have opInC : op.InBounds c := by
        have := Rewriter.replaceValue?_inBounds (.operation op) hc
        grind
      have idxInC : idx < op.getNumOperands! c := by
        rw [OperationPtr.getNumOperands!_replaceValue? hc]; exact idxIn
      have hstep := OperationPtr.getOperand_replaceValue? (op := op) (idx := idx)
        (opInBounds := opInC) (idxInBounds := idxInC) hCtx hc hneq
      have hrest := ih hwf h opInC idxInC
      rw [hrest, hstep]
      have e₁ : ((fromOp.getResult index : OpResultPtr) : ValuePtr) =
          ValuePtr.opResult { op := fromOp, index := index } := by
        rw [OperationPtr.getResult_def]
      have e₂ : ((toOp.getResult index : OpResultPtr) : ValuePtr) =
          ValuePtr.opResult { op := toOp, index := index } := by
        rw [OperationPtr.getResult_def]
      simp only [e₁, e₂]
      generalize OperationPtr.getOperand op ctx idx opIn idxIn = v
      rcases v with ⟨op', idx'⟩ | _
      · by_cases h₁ : op' = fromOp
        · subst h₁
          by_cases h₂ : idx' = index
          · subst h₂
            simp [hne.symm]
          · by_cases h₃ : idx' < index
            · simp [h₂, h₃, show idx' < index + 1 by omega]
            · simp [h₂, h₃, show ¬ idx' < index + 1 by omega]
        · simp [h₁]
      · simp

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
  fun_induction Rewriter.replaceOpResults <;> grind

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

theorem IRContext.wellFormed_replaceOp? (ctxWf : ctx.WellFormed)
    (hNewCtx : Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar = some newCtx)
    (neOps : oldOp ≠ newOp)
    (noRegions : oldOp.getNumRegions! ctx = 0) :
    newCtx.WellFormed := by
  simp only [Rewriter.replaceOp?] at hNewCtx
  split at hNewCtx; grind; rename_i hNumResults
  split at hNewCtx; grind; rename_i ctx' hctx'
  simp only [Option.some.injEq] at hNewCtx
  subst newCtx
  apply Rewriter.eraseOp_WellFormed
  · grind [IRContext.wellFormed_replaceOpResults]
  · grind
  · grind [OperationPtr.hasUses_replaceOpResults]

theorem BlockPtr.opChain_rewriter_replaceOpResults
    (h : Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo
      ctxInBounds = some newCtx)
    (hWf : BlockPtr.OpChain block' ctx array) :
    BlockPtr.OpChain block' newCtx array := by
  induction idx generalizing ctx
  case zero => grind [Rewriter.replaceOpResults]
  case succ idx ih =>
    simp only [Rewriter.replaceOpResults] at h
    grind [Option.maybe₁_def, BlockPtr.opChain_Rewriter_replaceValue?]

theorem BlockPtr.operationList_rewriter_replaceOpResults
    (h : Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo
      ctxInBounds = some newCtx)
    (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block' newCtx newCtxWf blockInBounds' =
    BlockPtr.operationList block' ctx ctxWf (by grind) := by
  have := BlockPtr.opChain_rewriter_replaceOpResults (block' := block')
    (array := block'.operationList ctx ctxWf (by grind))
    h (by grind [BlockPtr.operationListWF])
  grind

grind_pattern BlockPtr.operationList_rewriter_replaceOpResults =>
  Rewriter.replaceOpResults ctx fromOp toOp idx fromOpIB toOpIB hNumFrom hNumTo ctxInBounds,
  some newCtx,
  block'.operationList newCtx newCtxWf blockInBounds'

theorem BlockPtr.operationList_rewriter_replaceOp?
    (hNewCtx : Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar = some newCtx)
    (ctxWf : ctx.WellFormed)
    (neOps : oldOp ≠ newOp) :
    BlockPtr.operationList block newCtx newCtxWf blockIn =
    if h : oldOp.getParent! ctx = block then
      (BlockPtr.operationList block ctx ctxWf).erase oldOp
    else
      BlockPtr.operationList block ctx (by grind) (by grind) := by
  simp only [Rewriter.replaceOp?] at hNewCtx
  split at hNewCtx; grind
  split at hNewCtx; grind
  grind [IRContext.wellFormed_replaceOpResults, BlockPtr.operationList_rewriter_eraseOp]


/--
  `replaceOp?` replaces, in every operand, each result of `oldOp` by the result of `newOp` at the
  same index, and leaves every other operand as it was.
-/
theorem OperationPtr.getOperand_replaceOp? {op : OperationPtr}
    (hCtx : IRContext.WellFormed ctx)
    (hCtx' : Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar = some ctx')
    (hne : oldOp ≠ newOp)
    (opIn : op.InBounds ctx) (idxIn : idx < op.getNumOperands! ctx)
    (opIn' : op.InBounds ctx') (idxIn' : idx < op.getNumOperands! ctx') :
    OperationPtr.getOperand op ctx' idx opIn' idxIn' =
    let operand := OperationPtr.getOperand op ctx idx opIn idxIn
    match operand with
    | ValuePtr.opResult { op := op', index := idx' } =>
      if op' = oldOp then ValuePtr.opResult { op := newOp, index := idx' } else operand
    | _ => operand := by
  simp only [Rewriter.replaceOp?] at hCtx'
  split at hCtx'
  · simp at hCtx'
  · split at hCtx'
    · simp at hCtx'
    · next c hc =>
      simp only [Option.some.injEq] at hCtx'
      subst hCtx'
      have hopne : op ≠ oldOp := by
        simp only [Rewriter.eraseOp] at opIn'
        exact OperationPtr.InBounds.ne_of_inBounds_OperationPtr_dealloc opIn'
      have opInC : op.InBounds c := by
        have := Rewriter.replaceOpResults_inBounds (ptr := .operation op) hc
        grind
      have idxInC : idx < op.getNumOperands! c := by
        rw [OperationPtr.getNumOperands!_replaceOpResults hc]; exact idxIn
      rw [OperationPtr.getOperand_Rewriter_eraseOp rfl hopne.symm opInC idxInC,
        OperationPtr.getOperand_replaceOpResults hCtx hne hc opIn idxIn opInC idxInC]
      /- An operand that is a result of `oldOp` has an index below its result count. -/
      have hval : (OperationPtr.getOperand op ctx idx opIn idxIn).InBounds ctx := by
        rw [OperationPtr.getOperand_eq_OpOperandPtr_get, ← OpOperandPtr.getValue!_eq_getValue]
        exact OpOperandPtr.value!_inBounds (by grind) (by grind)
      simp only
      generalize hv : OperationPtr.getOperand op ctx idx opIn idxIn = v at hval
      rcases v with ⟨op', idx'⟩ | _
      · by_cases hop : op' = oldOp
        · subst hop
          have : idx' < op'.getNumResults ctx (by grind) := by
            obtain ⟨_, h⟩ := OpResultPtr.inBounds_def.mp ((ValuePtr.inBounds_opResult _ _).mp hval)
            exact h
          simp [this]
        · simp [hop]
      · rfl

end Veir
