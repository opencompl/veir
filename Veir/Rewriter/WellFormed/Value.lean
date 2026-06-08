module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.GetSet
import Veir.Rewriter.LinkedList.GetSet
import Veir.Rewriter.LinkedList.WellFormed

public section

namespace Veir

/-! ## Rewriter.replaceUse -/

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

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
  apply ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_self_empty
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
    (hWF' : value'.DefUse ctx array') (newValueInBounds) :
    value.DefUse (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)
      (array.erase use) := by
  simp only [replaceUse, ←OpOperandPtr.get!_eq_get]
  simp only [useOfValue', hvalueNe, ↓reduceIte]
  apply ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_other
    (missingUses' := Std.ExtHashSet.ofList [use]) (use := use) (value' := value') (array' := array') (value := value)
    (valueNe := by grind) (hvalue := by grind)
  · apply ValuePtr.DefUse.OpOperandPtr_setValue_other_empty <;>
      grind [ValuePtr.defUse_removeFromCurrent_self, ValuePtr.DefUse]
  · apply ValuePtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
    · grind
    · grind [ValuePtr.defUse_removeFromCurrent_other, ValuePtr.DefUse]

theorem ValuePtr.defUseArray_Rewriter_replaceUse_oldValue
    {oldValue newValue : ValuePtr}
    {use : OpOperandPtr}
    (useIn : use.InBounds ctx)
    (ctxWf: ctx.WellFormed)
    (useOfValue' : (use.get! ctx).value = oldValue)
    (hvalueNe : oldValue ≠ newValue) {newValueInBounds} {ctx'Wf : (Rewriter.replaceUse ctx use newValue useIn newValueInBounds ctxIn).WellFormed} {oldValueBounds} :
    ValuePtr.defUseArray oldValue (Rewriter.replaceUse ctx use newValue useIn newValueInBounds ctxIn) ctx'Wf oldValueBounds =
    (ValuePtr.defUseArray oldValue ctx ctxWf (by grind)).erase use := by
  have ⟨array, harray⟩ := ctxWf.valueDefUseChains oldValue (by grind)
  simp only [Std.ExtHashSet.filter_empty] at harray
  have ⟨array', harray'⟩ := ctxWf.valueDefUseChains newValue (by grind)
  simp only [Std.ExtHashSet.filter_empty] at harray'
  have := Rewriter.replaceUse_DefUse_oldValue useIn ctxWf.inBounds useOfValue' hvalueNe harray harray' (by grind)
  grind [ValuePtr.defUseArrayWF]

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
  apply ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_other
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

theorem Rewriter.replaceUse_DefUse (ctx: IRContext OpInfo) (use : OpOperandPtr)
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
theorem Rewriter.replaceUse_WellFormed (ctx: IRContext OpInfo) (use : OpOperandPtr) (newValue: ValuePtr)
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
      simp only [Std.ExtHashSet.filter_empty]
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
      apply RegionPtr.blockChain_unchanged (ctx := ctx) <;> grind
    case operations =>
      intros opPtr opPtrInBounds
      apply OperationPtr.WellFormed_unchanged (ctx := ctx) <;> grind [IRContext.WellFormed]
    case blocks =>
      intros blockPtr blockPtrInBounds
      apply BlockPtr.WellFormed_unchanged (ctx := ctx) <;> grind [IRContext.WellFormed]
    case regions =>
      intros regionPtr regionPtrInBounds
      apply RegionPtr.WellFormed_unchanged (ctx := ctx) <;> grind [IRContext.WellFormed]

/-! ## Rewriter.replaceValue? -/

theorem Rewriter.replaceValue?_WellFormed (ctx: IRContext OpInfo) (oldValue: ValuePtr) (newValue: ValuePtr)
    (oldIn: oldValue.InBounds ctx)
    (newIn: newValue.InBounds ctx)
    (ctxIn: ctx.FieldsInBounds)
    (depth: Nat) -- Fix this
    (hctx : IRContext.WellFormed ctx) :
    (Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth).maybe₁ IRContext.WellFormed := by
  simp only [Option.maybe₁_def]
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

theorem ValuePtr.hasUses!_replaceValue_oldValue :
    ctx.WellFormed →
    oldValue ≠ newValue →
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx' →
    oldValue.hasUses! ctx' = false := by
  intro ctxWf neValues hctx'
  have ⟨oldArray, hOldArray⟩ := ctxWf.valueDefUseChains oldValue (by grind)
  have ⟨newArray, hNewArray⟩ := ctxWf.valueDefUseChains newValue (by grind)
  simp only [Std.ExtHashSet.filter_empty] at hOldArray hNewArray
  have := Rewriter.replaceValue_DefUse_oldValue hOldArray hNewArray neValues hctx'
  have := this.firstElem
  grind [ValuePtr.hasUses!_def]

theorem ValuePtr.hasUses!_replaceValue_otherValue :
    ctx.WellFormed →
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx' →
    oldValue ≠ newValue →
    ∀ value, value.InBounds ctx →
    value ≠ oldValue → value ≠ newValue →
    value.hasUses! ctx' = value.hasUses! ctx := by
  intro ctxWf hctx' neValues value valueInBounds valueNeold valueNeNew
  have ⟨array, hArray⟩ := ctxWf.valueDefUseChains value (by grind)
  have ⟨oldArray, hOldArray⟩ := ctxWf.valueDefUseChains oldValue (by grind)
  have ⟨newArray, hNewArray⟩ := ctxWf.valueDefUseChains newValue (by grind)
  simp only [Std.ExtHashSet.filter_empty] at hOldArray hNewArray hArray
  have := Rewriter.replaceValue_DefUse_otherValue hArray hOldArray hNewArray (by grind)
    (by grind) (by grind) hctx'
  have := this.firstElem
  have := hArray.firstElem
  grind [ValuePtr.hasUses!_def]

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
      intro oldValueDefUse newValueDefUse oldNe hctx'
      have : oldArray[0]? = some firstUse := by grind [ValuePtr.DefUse.firstElem]
      have ⟨oldArrayTail, hOldArrayTail⟩ : ∃ oldArrayTail, oldArray = #[firstUse] ++ oldArrayTail := by
        apply Array.head_tail_if_firstElem_nonnull; grind
      simp only [Array.append_eq_erase_append_insertHead (hOldArrayTail)]
      apply ih (ctx := replaceUse ctx firstUse newValue (by grind) (by grind) (by grind))
      · apply Rewriter.replaceUse_DefUse_oldValue (array' := newArray) <;>
          grind [ValuePtr.DefUse.allUsesInChain, ValuePtr.DefUse.useValue]
      · apply Rewriter.replaceUse_DefUse_newValue (array' := oldArray) (value' := oldValue) <;>
          grind [ValuePtr.DefUse.allUsesInChain, ValuePtr.DefUse.useValue]
      all_goals grind

set_option maxHeartbeats 250000
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
  let oldValueArray := oldValue.defUseArray ctx hCtx (by grind)
  let newValueArray := newValue.defUseArray ctx hCtx (by grind)
  split
  · have : op.getOpOperand idx ∈ oldValueArray := by
      grind [ValuePtr.defUseArray_contains_operand_use]
    have := @Rewriter.replaceValue_DefUse_newValue _ _ ctx oldValue newValue
      (depth := depth) (newArray := newValueArray) (oldArray := oldValueArray)
    have : oldValue.DefUse ctx oldValueArray := by grind [ValuePtr.defUseArrayWF]
    have : newValue.DefUse ctx newValueArray := by grind [ValuePtr.defUseArrayWF]
    grind [ValuePtr.DefUse]
  · by_cases h : op.getOperand ctx idx = newValue
    · simp only [OperationPtr.getOperand_eq_OpOperandPtr_get] at h
      have := @Rewriter.replaceValue_DefUse_newValue _ _ ctx oldValue newValue
        (depth := depth) (newArray := newValueArray) (oldArray := oldValueArray)
      grind [ValuePtr.DefUse, ValuePtr.defUseArrayWF]
    · let operand := op.getOpOperand idx
      let value := (operand.get ctx (by grind)).value
      let valueArray := value.defUseArray ctx hCtx (by grind)
      simp only [OperationPtr.getOperand_eq_OpOperandPtr_get] at h
      have : op.getOpOperand idx ∉ oldValueArray := by grind [ValuePtr.defUseArray_contains_operand_use]
      have : value.InBounds ctx := by grind
      have := @Rewriter.replaceValue_DefUse_otherValue _ _ ctx value oldValue newValue
        (depth := depth) (array := valueArray) (newArray := newValueArray) (oldArray := oldValueArray)
      have : operand ∈ valueArray := by grind [ValuePtr.defUseArray_contains_operand_use]
      grind [ValuePtr.DefUse, ValuePtr.defUseArrayWF]

set_option warn.sorry false in
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

set_option warn.sorry false in
theorem BlockPtr.operationList_replaceOp?
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array)
    (hnewCtx : Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn depth = some newCtx) :
      BlockPtr.operationList blockPtr newCtx ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.erase oldOp
      else
        array := by
  sorry

/--
info: 'Veir.Rewriter.replaceValue?_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.replaceValue?_WellFormed

/-! ## Rewriter.setType

`Rewriter.setType` only updates the `type` field of a value (an op result or a block argument).
It touches no indices, owners, use links, parents, or def-use/op/block chains, and
`IRContext.WellFormed` imposes no constraint on the `type` field, so it preserves
well-formedness. Every chain is therefore "unchanged" by the rewrite. -/

theorem BlockPtr.opChain_rewriter_setType
    (hWf : BlockPtr.OpChain block ctx array missingOps) :
    BlockPtr.OpChain block (Rewriter.setType ctx value newType hvalue) array missingOps := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind [Rewriter.setType]

theorem ValuePtr.defUse_rewriter_setType
    (hWf : ValuePtr.DefUse value' ctx array missingUses) :
    ValuePtr.DefUse value' (Rewriter.setType ctx value newType hvalue) array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind [Rewriter.setType]

theorem BlockPtr.defUse_rewriter_setType
    (hWf : BlockPtr.DefUse block ctx array missingUses) :
    BlockPtr.DefUse block (Rewriter.setType ctx value newType hvalue) array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind [Rewriter.setType]

theorem RegionPtr.blockChain_rewriter_setType
    (hWf : RegionPtr.BlockChain region ctx array) :
    RegionPtr.BlockChain region (Rewriter.setType ctx value newType hvalue) array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx) hWf <;> grind [Rewriter.setType]

theorem IRContext.wellFormed_rewriter_setType
    {value : ValuePtr} {newType : TypeAttr} {hvalue : value.InBounds ctx} :
    ctx.WellFormed → (Rewriter.setType ctx value newType hvalue).WellFormed := by
  intro wf
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := wf
  constructor
  case inBounds => grind [Rewriter.setType_fieldsInBounds]
  case valueDefUseChains =>
    intros val hval
    have ⟨array, harray⟩ := h₂ val (by grind)
    exists array
    grind [ValuePtr.defUse_rewriter_setType]
  case blockDefUseChains =>
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    grind [BlockPtr.defUse_rewriter_setType]
  case opChain =>
    intros block hblock
    have ⟨array, harray⟩ := h₄ block (by grind)
    exists array
    grind [BlockPtr.opChain_rewriter_setType]
  case blockChain =>
    intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    grind [RegionPtr.blockChain_rewriter_setType]
  case operations =>
    intros op hop
    have : op.InBounds ctx := by grind
    apply OperationPtr.WellFormed_unchanged (ctx := ctx) (h₆ op this) <;> grind [Rewriter.setType]
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    apply BlockPtr.WellFormed_unchanged (ctx := ctx) (h₇ bl this) <;> grind [Rewriter.setType]
  case regions =>
    intros reg hreg
    have : reg.InBounds ctx := by grind
    apply RegionPtr.WellFormed_unchanged (ctx := ctx) (h₈ reg this) <;> grind [Rewriter.setType]

/--
info: 'Veir.IRContext.wellFormed_rewriter_setType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms IRContext.wellFormed_rewriter_setType

end Veir
