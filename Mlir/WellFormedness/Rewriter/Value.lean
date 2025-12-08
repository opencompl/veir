import Mlir.Core.Basic
import Mlir.WellFormedness.WellFormed
import Mlir.WellFormedness.UseDefChain
import Mlir.Rewriter
import Mlir.Lemmas.Rewriter

namespace Mlir


theorem Rewriter.replaceUse_WellFormedUseDefChain_newValue (ctx: IRContext) (use : OpOperandPtr)
    (useIn: use.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (value value' : ValuePtr) (array array': Array OpOperandPtr) (hvalue : value.InBounds ctx) (hvalue' : value'.InBounds ctx)
    (useOfValue' : (use.get ctx useIn).value = value')
    (hvalueNe : value ≠ value')
    (hWF : value.WellFormedUseDefChain ctx array hvalue)
    (hWF' : value'.WellFormedUseDefChain ctx array' hvalue') newValueInBounds valueInBoundsAfter :
    value.WellFormedUseDefChain (Rewriter.replaceUse ctx use value useIn newValueInBounds ctxIn) (#[use] ++ array) valueInBoundsAfter := by
  simp only [replaceUse]
  simp only [useOfValue', Ne.symm hvalueNe, ↓reduceIte]
  apply OpOperandPtr.insertIntoCurrent_WellFormedUseDefChain_self (useInBounds := by grind) (valueInBounds := by grind)
  apply OpOperandPtr.setValue_WellFormedUseDefChainMissingLink (useInBounds := by grind) (valueInBounds := by grind) (useOfOtherValue := by grind)
  apply OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other (array := array) (array' := array') (value' := value) <;> grind

theorem Rewriter.replaceUse_WellFormedUseDefChain_oldValue (ctx: IRContext) (use : OpOperandPtr)
    (useIn: use.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (value value' : ValuePtr) (array array': Array OpOperandPtr) (hvalue : value.InBounds ctx) (hvalue' : value'.InBounds ctx)
    (useOfValue' : (use.get ctx useIn).value = value)
    (hvalueNe : value ≠ value')
    (hWF : value.WellFormedUseDefChain ctx array hvalue)
    (hWF' : value'.WellFormedUseDefChain ctx array' hvalue') newValueInBounds valueInBoundsAfter :
    value.WellFormedUseDefChain (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) (array.erase use) valueInBoundsAfter := by
  simp only [replaceUse]
  simp only [useOfValue', hvalueNe, ↓reduceIte]
  apply OpOperandPtr.insertIntoCurrent_WellFormedUseDefChain_other (missingUses := Std.ExtHashSet.ofList [use]) (value' := value') (array' := array') (useOfValue' := by grind) (hvalueNe := by grind) (valueInBounds := by grind) (valueInBounds' := by grind)
  · simp [←ValuePtr.WellFormedUseDefChainMissingLink_iff_WellFormedUseDefChain]
    have : ∅ = (Std.ExtHashSet.ofList [use]).erase use := by simp; grind
    simp only [this]
    apply OpOperandPtr.setValue_WellFormedUseDefChainMissingLink_append
    any_goals grind
    apply OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_self <;> grind
  · grind [OpOperandPtr.setValue_WellFormedUseDefChainMissingLink, OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other]
  · grind

theorem Rewriter.replaceUse_WellFormedUseDefChain_otherValue (ctx: IRContext) (use : OpOperandPtr)
    (useIn: use.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (value value' : ValuePtr) (array array': Array OpOperandPtr) (hvalue : value.InBounds ctx) (hvalue' : value'.InBounds ctx)
    (useOfValue' : (use.get ctx useIn).value = value)
    (hWF : value.WellFormedUseDefChain ctx array hvalue)
    (hWF' : value'.WellFormedUseDefChain ctx array' hvalue') newValueInBounds
    value'' array'' hvalue''
    (hWF'' : ValuePtr.WellFormedUseDefChain value'' ctx array'' hvalue'') value''InBoundsAfter
    (hne : value'' ≠ value) (hne' : value'' ≠ value') (hne'' : value ≠ value') :
    value''.WellFormedUseDefChain (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) array'' value''InBoundsAfter := by
  simp only [replaceUse]
  simp only [useOfValue', hne'', ↓reduceIte]
  apply OpOperandPtr.insertIntoCurrent_WellFormedUseDefChain_other (value' := value') (array' := array') (useOfValue' := by grind) (hvalueNe := by grind) (valueInBounds := by grind) (valueInBounds' := by grind) (missingUses := Std.ExtHashSet.ofList [use])
  · apply OpOperandPtr.setValue_WellFormedUseDefChain_other
    any_goals grind
    apply OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other (array' := array) <;> grind
  · grind [ValuePtr.WellFormedUseDefChain, OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other, OpOperandPtr.setValue_WellFormedUseDefChainMissingLink]
  · grind

theorem Rewriter.replaceUse_WellFormedUseDefChain (ctx: IRContext) (use : OpOperandPtr)
    (useIn: use.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (value value' : ValuePtr) (array array': Array OpOperandPtr) (hvalue : value.InBounds ctx) (hvalue' : value'.InBounds ctx)
    (useOfValue' : (use.get ctx useIn).value = value)
    (hWF : value.WellFormedUseDefChain ctx array hvalue)
    (hWF' : value'.WellFormedUseDefChain ctx array' hvalue') newValueInBounds
    value'' array'' hvalue''
    (hWF'' : ValuePtr.WellFormedUseDefChain value'' ctx array'' hvalue'') value''InBoundsAfter :
    ∃ newArray'', value''.WellFormedUseDefChain (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) newArray'' value''InBoundsAfter := by
  by_cases h : value = value'
  · grind [replaceUse]
  · by_cases hne : value'' = value
    · subst value''
      exists array.erase use
      grind [Rewriter.replaceUse_WellFormedUseDefChain_oldValue]
    · by_cases hne' : value'' = value'
      · subst value''
        exists (#[use] ++ array')
        grind [Rewriter.replaceUse_WellFormedUseDefChain_newValue]
      · exists array''
        grind [Rewriter.replaceUse_WellFormedUseDefChain_otherValue]

@[grind .]
theorem Rewriter.replaceUse_WellFormed (ctx: IRContext) (use : OpOperandPtr) (newValue: ValuePtr)
    (useIn: use.InBounds ctx)
    (newIn: newValue.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (hWf : IRContext.WellFormed ctx) :
    (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).WellFormed := by
  by_cases h: (use.get ctx useIn).value = newValue
  case pos => grind [replaceUse]
  case neg =>
    constructor
    case inBounds => grind
    case valueUseDefChains =>
      intros valuePtr valuePtrInBounds
      let value := (use.get ctx useIn).value
      have ⟨array, harray⟩ := hWf.valueUseDefChains value (by grind)
      have ⟨newArray, hnewArray⟩ := hWf.valueUseDefChains newValue (by grind)
      have ⟨array', hArray'⟩ := hWf.valueUseDefChains valuePtr (by grind)
      apply Rewriter.replaceUse_WellFormedUseDefChain (value := value) (array := array) (array' := newArray) (array'' := array') <;> grind
    case blockUseDefChains =>
      intros blockPtr blockPtrInBounds
      have ⟨array, harray⟩ := hWf.blockUseDefChains blockPtr (by grind)
      exists array
      apply IRContext.BlockPtr_UseDefChainWellFormed_unchanged (ctx := ctx) <;> grind [replaceUse]
    case opChain =>
      intros blockPtr blockPtrInBounds
      have ⟨chain, hchain⟩ := hWf.opChain blockPtr (by grind)
      exists chain
      apply IRContext.OperationChainWellFormed_unchanged (ctx := ctx) <;> grind
    case blockChain =>
      intros regionPtr regionPtrInBounds
      have ⟨chain, hchain⟩ := hWf.blockChain regionPtr (by grind)
      exists chain
      apply IRContext.BlockChainWellFormed_unchanged (ctx := ctx) <;> grind
    case operations =>
      intros opPtr opPtrInBounds
      apply IRContext.Operation_WellFormed_unchanged (ctx := ctx) <;> grind [IRContext.WellFormed]
    case blocks =>
      intros blockPtr blockPtrInBounds
      apply IRContext.Block_WellFormed_unchanged (ctx := ctx) <;> grind [IRContext.WellFormed]
    case regions =>
      intros regionPtr regionPtrInBounds
      apply IRContext.Region_WellFormed_unchanged (ctx := ctx) <;> grind [IRContext.WellFormed]

theorem Rewriter.replaceValue?_WellFormed (ctx: IRContext) (oldValue: ValuePtr) (newValue: ValuePtr)
    (oldIn: oldValue.InBounds ctx)
    (newIn: newValue.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (depth: Nat) -- Fix this
    (hctx : IRContext.WellFormed ctx) :
    (Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth).maybe₁ IRContext.WellFormed := by
  simp only [Option.maybe₁]
  induction depth generalizing ctx
  case zero => simp [replaceValue?]
  case succ depth ih =>
    simp only [replaceValue?]
    grind

theorem Rewriter.replaceValue_WellFormedUseDefChain_otherValue :
    value.WellFormedUseDefChain ctx array valueInBounds →
    oldValue.WellFormedUseDefChain ctx oldArray oldValueInBounds →
    newValue.WellFormedUseDefChain ctx newArray newValueInBounds →
    value ≠ oldValue →
    value ≠ newValue →
    oldValue ≠ newValue →
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx' →
    value.WellFormedUseDefChain ctx' array valueInBoundsAfter := by
  induction depth generalizing ctx oldArray newArray
  case zero => simp [replaceValue?]
  case succ depth ih =>
    simp only [replaceValue?]
    split
    · grind
    · rename_i firstUse heq
      intros
      apply ih
        (ctx := replaceUse ctx firstUse newValue (by grind) (by grind) (by grind))
        (oldArray := oldArray.erase firstUse)
        (newArray := #[firstUse] ++ newArray)
      all_goals grind [ValuePtr.WellFormedUseDefChain,
                       Rewriter.replaceUse_WellFormedUseDefChain_otherValue,
                       Rewriter.replaceUse_WellFormedUseDefChain_oldValue,
                       Rewriter.replaceUse_WellFormedUseDefChain_newValue]

theorem Rewriter.replaceValue_WellFormedUseDefChain_oldValue :
    oldValue.WellFormedUseDefChain ctx oldArray oldValueInBounds →
    newValue.WellFormedUseDefChain ctx newArray newValueInBounds →
    oldValue ≠ newValue →
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx' →
    oldValue.WellFormedUseDefChain ctx' #[] valueInBoundsAfter := by
  induction depth generalizing ctx oldArray newArray
  case zero => simp [replaceValue?]
  case succ depth ih =>
    simp only [replaceValue?]
    split
    · intros
      have : oldArray = #[] := by grind [ValuePtr.WellFormedUseDefChain]
      grind [ValuePtr.WellFormedUseDefChain]
    · rename_i firstUse heq
      intros
      apply ih
        (ctx := replaceUse ctx firstUse newValue (by grind) (by grind) (by grind))
        (oldArray := oldArray.erase firstUse)
        (newArray := #[firstUse] ++ newArray)
      all_goals grind [ValuePtr.WellFormedUseDefChain,
                       Rewriter.replaceUse_WellFormedUseDefChain_otherValue,
                       Rewriter.replaceUse_WellFormedUseDefChain_oldValue,
                       Rewriter.replaceUse_WellFormedUseDefChain_newValue]

theorem Array.append_eq_erase_append_insertHead {α : Type} [BEq α] [LawfulBEq α] {arrayHead : α} {array arrayTail otherArray}:
    array = #[arrayHead] ++ arrayTail →
    array.reverse ++ otherArray = (array.erase arrayHead).reverse ++ (#[arrayHead] ++ otherArray) := by
  intros
  subst array
  grind [Array.erase_head_concat]

seal HAppend.hAppend in -- TODO: remove after we use modules?
theorem Rewriter.replaceValue_WellFormedUseDefChain_newValue :
    oldValue.WellFormedUseDefChain ctx oldArray oldValueInBounds →
    newValue.WellFormedUseDefChain ctx newArray newValueInBounds →
    oldValue ≠ newValue →
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx' →
    newValue.WellFormedUseDefChain ctx' (oldArray.reverse ++ newArray) valueInBoundsAfter := by
  induction depth generalizing ctx oldArray newArray
  case zero => simp [replaceValue?]
  case succ depth ih =>
    simp only [replaceValue?]
    split
    · intros
      have : oldArray = #[] := by grind [ValuePtr.WellFormedUseDefChain]
      grind [ValuePtr.WellFormedUseDefChain]
    · rename_i firstUse heq
      intros
      have : oldArray[0]? = some firstUse := by grind [ValuePtr.WellFormedUseDefChain]
      have ⟨oldArrayTail, hOldArrayTail⟩ : ∃ oldArrayTail, oldArray = #[firstUse] ++ oldArrayTail := by (
        apply Array.head_tail_if_firstElem_nonnull; grind
      )
      simp only [Array.append_eq_erase_append_insertHead (hOldArrayTail)]
      apply ih (ctx := replaceUse ctx firstUse newValue (by grind) (by grind) (by grind))
      · apply Rewriter.replaceUse_WellFormedUseDefChain_oldValue (array' := newArray) <;> grind [ValuePtr.WellFormedUseDefChain]
      · apply Rewriter.replaceUse_WellFormedUseDefChain_newValue (array' := oldArray) (value' := oldValue) <;> grind [ValuePtr.WellFormedUseDefChain]
      all_goals grind

theorem OperationPtr.getOperand_replaceValue?
    (hCtx : IRContext.WellFormed ctx)
    (hCtx' : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx') :
    oldValue ≠ newValue →
    OperationPtr.getOperand op ctx' idx opInBounds idxInBounds =
    let value := OperationPtr.getOperand op ctx idx
    if value = oldValue then newValue else value := by
  intros
  simp only
  simp only [OperationPtr.getOperand_eq_OpOperandPtr_get] at *
  let oldValueArray := oldValue.useDefArray ctx (by grind) (by grind)
  let newValueArray := newValue.useDefArray ctx (by grind) (by grind)
  split
  · have : { op := op, index := idx } ∈ oldValueArray := by grind [ValuePtr.useDefArray_contains_operand_use]
    have := @Rewriter.replaceValue_WellFormedUseDefChain_newValue oldValue newValue ctx
      (depth := depth) (newArray := newValueArray) (oldArray := oldValueArray)
    grind [ValuePtr.WellFormedUseDefChain]
  · by_cases h : op.getOperand ctx idx = newValue
    · simp only [OperationPtr.getOperand_eq_OpOperandPtr_get] at h
      have := @Rewriter.replaceValue_WellFormedUseDefChain_newValue oldValue newValue ctx
        (depth := depth) (newArray := newValueArray) (oldArray := oldValueArray)
      grind [ValuePtr.WellFormedUseDefChain]
    · let operand := { op := op, index := idx : OpOperandPtr}
      let value := (operand.get ctx (by grind)).value
      let valueArray := value.useDefArray ctx (by grind) (by grind)
      simp only [OperationPtr.getOperand_eq_OpOperandPtr_get] at h
      have : { op := op, index := idx } ∉ oldValueArray := by grind [ValuePtr.useDefArray_contains_operand_use]
      have : value.InBounds ctx := by grind
      have := @Rewriter.replaceValue_WellFormedUseDefChain_otherValue value oldValue newValue ctx
        (depth := depth) (array := valueArray) (newArray := newValueArray) (oldArray := oldValueArray)
      have : operand ∈ valueArray := by grind [ValuePtr.useDefArray_contains_operand_use]
      grind [ValuePtr.WellFormedUseDefChain]

theorem OperationPtr.getOperand_replaceOp?
    (hCtx : IRContext.WellFormed ctx)
    (hCtx' : Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn depth = some ctx') :
    oldOp ≠ newOp →
    OperationPtr.getOperand op ctx' idx opInBounds idxInBounds =
    let operand := OperationPtr.getOperand op ctx idx (by sorry) (by sorry)
    match operand with
    | ValuePtr.opResult {op := op', index := idx'} =>
      if op' = oldOp then
        ValuePtr.opResult {op := newOp, index := idx'}
      else
        operand
    | _ => operand := by
  sorry

theorem BlockPtr.operationList_replaceOp?
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array)
    (hnewCtx : Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn depth = some newCtx) :
      BlockPtr.operationList blockPtr newCtx ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.erase oldOp
      else
        array := by
  sorry

-- /--
-- info: 'Mlir.Rewriter.replaceValue?_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms Rewriter.replaceValue?_WellFormed
-- TODO


end Mlir
