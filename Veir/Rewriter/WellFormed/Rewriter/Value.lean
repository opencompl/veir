import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.LinkedList.GetSet
import Veir.Rewriter.LinkedList.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSetInBounds

namespace Veir


theorem Rewriter.replaceUse_DefUse_newValue
    {value value' : ValuePtr}
    (useIn: use.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (useOfValue' : (use.get! ctx).value = value')
    (hvalueNe : value ≠ value')
    (hWF : value.DefUse ctx array)
    (hWF' : value'.DefUse ctx array') {newValueInBounds} :
    value.DefUse (Rewriter.replaceUse ctx use value useIn newValueInBounds ctxIn)
      (#[use] ++ array) := by
  simp only [replaceUse, ←OpOperandPtr.get!_eq_get]
  simp only [useOfValue', Ne.symm hvalueNe, ↓reduceIte]
  apply ValuePtr.defUse_insertIntoCurrent_self_empty
  apply ValuePtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
    (useInBounds := by grind) (useOfOtherValue := by grind)
  apply ValuePtr.defUse_removeFromCurrent_other
    (array := array) (array' := array') (value' := value') (missingUses' := ∅) <;> grind [ValuePtr.DefUse]

theorem Rewriter.replaceUse_DefUse_oldValue
    {value value' : ValuePtr}
    (useIn: use.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (useOfValue' : (use.get! ctx).value = value)
    (hvalueNe : value ≠ value')
    (hWF : value.DefUse ctx array)
    (hWF' : value'.DefUse ctx array') {newValueInBounds} :
    value.DefUse (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)
      (array.erase use) := by
  simp only [replaceUse, ←OpOperandPtr.get!_eq_get]
  simp only [useOfValue', hvalueNe, ↓reduceIte]
  apply ValuePtr.defUse_insertIntoCurrent_other
    (missingUses' := Std.ExtHashSet.ofList [use]) (use := use) (value' := value') (array' := array') (value := value)
    (valueNe := by grind) (hvalue := by grind)
  · apply ValuePtr.DefUse.OpOperandPtr_setValue_other_empty <;>
      grind [ValuePtr.defUse_removeFromCurrent_self, ValuePtr.DefUse]
  · apply ValuePtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
    · grind
    · grind [ValuePtr.defUse_removeFromCurrent_other, ValuePtr.DefUse]

theorem Rewriter.replaceUse_DefUse_otherValue
    (ctxIn: ctx.FieldsInBounds)
    (useOfValue' : (use.get! ctx).value = value)
    (hWF : value.DefUse ctx array)
    (hWF' : value'.DefUse ctx array')
    (hWF'' : ValuePtr.DefUse value'' ctx array'')
    (hne : value'' ≠ value) (hne' : value'' ≠ value') (hne'' : value ≠ value') :
    value''.DefUse (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)
      array'' := by
  simp only [replaceUse, ←OpOperandPtr.get!_eq_get]
  simp only [useOfValue', hne'', ↓reduceIte]
  apply ValuePtr.defUse_insertIntoCurrent_other
    (missingUses' := Std.ExtHashSet.ofList [use]) (use := use) (value := value'') (value' := value') (array' := array')
    (valueNe := by grind) (hvalue := by grind)
  · apply ValuePtr.DefUse.OpOperandPtr_setValue_other_of_value_ne
    any_goals grind
    apply ValuePtr.defUse_removeFromCurrent_other (value' := value) (array' := array) (missingUses' := ∅)
        <;> grind [ValuePtr.DefUse]
  · apply ValuePtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
    · grind
    · apply ValuePtr.defUse_removeFromCurrent_other (value' := value) (array' := array) (missingUses' := ∅)
        <;> grind [ValuePtr.DefUse]

theorem Rewriter.replaceUse_DefUse (ctx: IRContext) (use : OpOperandPtr)
    (useIn: use.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (value value' : ValuePtr) (array array': Array OpOperandPtr)
    (useOfValue' : (use.get ctx useIn).value = value)
    (hWF : value.DefUse ctx array)
    (hWF' : value'.DefUse ctx array') newValueInBounds
    value'' array''
    (hWF'' : ValuePtr.DefUse value'' ctx array'') :
    ∃ newArray'', value''.DefUse (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) newArray'' := by
  by_cases h : value = value'
  · grind [replaceUse]
  · by_cases hne : value'' = value
    · subst value''
      exists array.erase use
      grind [Rewriter.replaceUse_DefUse_oldValue]
    · by_cases hne' : value'' = value'
      · subst value''
        exists (#[use] ++ array')
        grind [Rewriter.replaceUse_DefUse_newValue]
      · exists array''
        grind [Rewriter.replaceUse_DefUse_otherValue]

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
    case valueDefUseChains =>
      intros valuePtr valuePtrInBounds
      let value := (use.get ctx useIn).value
      have ⟨array, harray⟩ := hWf.valueDefUseChains value (by grind)
      have ⟨newArray, hnewArray⟩ := hWf.valueDefUseChains newValue (by grind)
      have ⟨array', hArray'⟩ := hWf.valueDefUseChains valuePtr (by grind)
      apply Rewriter.replaceUse_DefUse
        (value := value) (array := array) (array' := newArray) (array'' := array') <;> grind
    case blockDefUseChains =>
      intros blockPtr blockPtrInBounds
      have ⟨array, harray⟩ := hWf.blockDefUseChains blockPtr (by grind)
      exists array
      apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind [replaceUse]
    case opChain =>
      intros blockPtr blockPtrInBounds
      have ⟨chain, hchain⟩ := hWf.opChain blockPtr (by grind)
      exists chain
      apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind
    case blockChain =>
      intros regionPtr regionPtrInBounds
      have ⟨chain, hchain⟩ := hWf.blockChain regionPtr (by grind)
      exists chain
      apply RegionPtr.BlockChainWellFormed_unchanged (ctx := ctx) <;> grind
    case operations =>
      intros opPtr opPtrInBounds
      apply Operation.WellFormed_unchanged (ctx := ctx) <;> sorry -- missing GetSet lemmas
    case blocks =>
      intros blockPtr blockPtrInBounds
      apply Block.WellFormed_unchanged (ctx := ctx) <;> grind [IRContext.WellFormed]
    case regions =>
      intros regionPtr regionPtrInBounds
      apply Region.WellFormed_unchanged (ctx := ctx) <;> sorry -- missing GetSet lemmas

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

theorem Rewriter.replaceValue_DefUse_otherValue :
    value.DefUse ctx array →
    oldValue.DefUse ctx oldArray →
    newValue.DefUse ctx newArray →
    value ≠ oldValue →
    value ≠ newValue →
    oldValue ≠ newValue →
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx' →
    value.DefUse ctx' array := by
  induction depth generalizing ctx oldArray newArray
  case zero => simp [replaceValue?]
  case succ depth ih =>
    simp only [replaceValue?]
    split
    · grind
    · rename_i firstUse heq
      simp [← ValuePtr.getFirstUse!_eq_getFirstUse] at heq
      intros hWF holdWF hnewWF oldNe newNe oldNewNe hctx'
      apply ih
        (ctx := replaceUse ctx firstUse newValue (by grind) (by grind) (by grind))
        (oldArray := oldArray.erase firstUse)
        (newArray := #[firstUse] ++ newArray)
      · apply Rewriter.replaceUse_DefUse_otherValue
          (array := oldArray) (array' := newArray) (value := oldValue) <;> grind [ValuePtr.DefUse]
      · apply Rewriter.replaceUse_DefUse_oldValue (array' := newArray) <;>
          grind [ValuePtr.DefUse]
      · apply Rewriter.replaceUse_DefUse_newValue (array' := oldArray) (value' := oldValue) <;>
          grind [ValuePtr.DefUse]
      all_goals grind

theorem Rewriter.replaceValue_DefUse_oldValue :
    oldValue.DefUse ctx oldArray →
    newValue.DefUse ctx newArray →
    oldValue ≠ newValue →
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx' →
    oldValue.DefUse ctx' #[] := by
  induction depth generalizing ctx oldArray newArray
  case zero => simp [replaceValue?]
  case succ depth ih =>
    simp only [replaceValue?]
    split
    · intros
      have : oldArray = #[] := by grind [ValuePtr.DefUse]
      grind [ValuePtr.DefUse]
    · rename_i firstUse heq
      intros
      apply ih
        (ctx := replaceUse ctx firstUse newValue (by grind) (by grind) (by grind))
        (oldArray := oldArray.erase firstUse)
        (newArray := #[firstUse] ++ newArray)
      · apply Rewriter.replaceUse_DefUse_oldValue (array' := newArray) <;>
          grind [ValuePtr.DefUse]
      · apply Rewriter.replaceUse_DefUse_newValue (array' := oldArray) (value' := oldValue) <;>
          grind [ValuePtr.DefUse]
      all_goals grind [ValuePtr.DefUse]

theorem Array.append_eq_erase_append_insertHead {α : Type} [BEq α] [LawfulBEq α] {arrayHead : α} {array arrayTail otherArray}:
    array = #[arrayHead] ++ arrayTail →
    array.reverse ++ otherArray = (array.erase arrayHead).reverse ++ (#[arrayHead] ++ otherArray) := by
  grind [Array.erase_head_concat]

seal HAppend.hAppend in -- TODO: remove after we use modules?
theorem Rewriter.replaceValue_DefUse_newValue :
    oldValue.DefUse ctx oldArray →
    newValue.DefUse ctx newArray →
    oldValue ≠ newValue →
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx' →
    newValue.DefUse ctx' (oldArray.reverse ++ newArray) := by
  induction depth generalizing ctx oldArray newArray
  case zero => simp [replaceValue?]
  case succ depth ih =>
    simp only [replaceValue?]
    split
    · intros
      have : oldArray = #[] := by grind [ValuePtr.DefUse]
      grind [ValuePtr.DefUse]
    · rename_i firstUse heq
      intros
      have : oldArray[0]? = some firstUse := by sorry --grind [ValuePtr.DefUse]
      have ⟨oldArrayTail, hOldArrayTail⟩ : ∃ oldArrayTail, oldArray = #[firstUse] ++ oldArrayTail := by
        apply Array.head_tail_if_firstElem_nonnull; grind
      simp only [Array.append_eq_erase_append_insertHead (hOldArrayTail)]
      apply ih (ctx := replaceUse ctx firstUse newValue (by grind) (by grind) (by grind))
      · apply Rewriter.replaceUse_DefUse_oldValue (array' := newArray) <;>
          sorry --grind [ValuePtr.DefUse]
      · apply Rewriter.replaceUse_DefUse_newValue (array' := oldArray) (value' := oldValue) <;>
          sorry -- grind [ValuePtr.DefUse]
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
  let oldValueArray := oldValue.defUseArray ctx (by grind) (by grind)
  let newValueArray := newValue.defUseArray ctx (by grind) (by grind)
  split
  · have : op.getOpOperand idx ∈ oldValueArray := by
      grind [ValuePtr.defUseArray_contains_operand_use]
    have := @Rewriter.replaceValue_DefUse_newValue oldValue newValue ctx
      (depth := depth) (newArray := newValueArray) (oldArray := oldValueArray)
    grind [ValuePtr.DefUse]
  · by_cases h : op.getOperand ctx idx = newValue
    · simp only [OperationPtr.getOperand_eq_OpOperandPtr_get] at h
      have := @Rewriter.replaceValue_DefUse_newValue oldValue newValue ctx
        (depth := depth) (newArray := newValueArray) (oldArray := oldValueArray)
      grind [ValuePtr.DefUse]
    · let operand := op.getOpOperand idx
      let value := (operand.get ctx (by grind)).value
      let valueArray := value.defUseArray ctx (by grind) (by grind)
      simp only [OperationPtr.getOperand_eq_OpOperandPtr_get] at h
      have : op.getOpOperand idx ∉ oldValueArray := by grind [ValuePtr.defUseArray_contains_operand_use]
      have : value.InBounds ctx := by grind
      have := @Rewriter.replaceValue_DefUse_otherValue value oldValue newValue ctx
        (depth := depth) (array := valueArray) (newArray := newValueArray) (oldArray := oldValueArray)
      have : operand ∈ valueArray := by grind [ValuePtr.defUseArray_contains_operand_use]
      grind [ValuePtr.DefUse]

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
-- info: 'Veir.Rewriter.replaceValue?_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms Rewriter.replaceValue?_WellFormed
-- TODO


end Veir
