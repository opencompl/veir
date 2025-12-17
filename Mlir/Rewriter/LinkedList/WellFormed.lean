import Mlir.Core.Basic
import Mlir.Core.WellFormed
import Mlir.Rewriter.LinkedList.GetSet
import Std.Data.HashSet
import Std.Data.ExtHashSet

namespace Mlir

attribute [local grind ext] OpOperand

/--
 - This is a weakened version of `ValuePtr.WellFormedUseDefChain` that allows for some uses
 - to be missing from the use-def chain. This is used to formalize the intermediate states
 - during rewriting and operation creation where some uses may not yet be linked into the chain.
 -/
structure ValuePtr.WellFormedUseDefChainMissingLink
    (value : ValuePtr) (ctx : IRContext) (array : Array OpOperandPtr)
    (hvalue : value.InBounds ctx)
    (missingUses : Std.ExtHashSet OpOperandPtr) : Prop where
  arrayInBounds (h : use ∈ array) : use.InBounds ctx
  firstElem : array[0]? = value.getFirstUse! ctx
  firstUseBack (heq : value.getFirstUse! ctx = some firstUse) :
    (firstUse.get! ctx).back = .valueFirstUse value
  allUsesInChain (use : OpOperandPtr) (huse : use.InBounds ctx) :
    (use.get! ctx).value = value → (use ∈ array ↔ use ∉ missingUses)
  useValue (hin : use ∈ array) : (use.get! ctx).value = value
  nextElems (hi : i < array.size) :
    (array[i].get! ctx).nextUse = array[i + 1]?
  prevNextUse (iPos : i > 0) (iInBounds : i < array.size) :
    (array[i].get! ctx).back = OpOperandPtrPtr.operandNextUse array[i - 1]
  missingUsesInBounds (hin : use ∈ missingUses) : use.InBounds ctx
  missingUsesValue (hin : use ∈ missingUses) : (use.get! ctx).value = value

attribute [grind →] ValuePtr.WellFormedUseDefChainMissingLink.missingUsesInBounds

@[simp, grind =]
theorem ValuePtr.WellFormedUseDefChainMissingLink_iff_WellFormedUseDefChain
    (value : ValuePtr) (ctx : IRContext) (array : Array OpOperandPtr)
    (hvalue : value.InBounds ctx) :
    (ValuePtr.WellFormedUseDefChainMissingLink value ctx array hvalue ∅) ↔
    ValuePtr.WellFormedUseDefChain value ctx array hvalue := by
  constructor <;> intros <;>
  constructor <;> grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChainMissingLink]

theorem ValuePtr.WellFormedUseDefChainMissingLink_unchanged
    (hWf : valuePtr.WellFormedUseDefChainMissingLink ctx array valuePtrInBounds missingUses)
    (valuePtrInBounds' : valuePtr.InBounds ctx')
    (hSameFirstUse : valuePtr.getFirstUse! ctx = valuePtr.getFirstUse! ctx')
    (hPreservesInBounds : ∀ (usePtr : OpOperandPtr),
      usePtr.InBounds ctx →
      (usePtr.get! ctx).value = valuePtr → usePtr.InBounds ctx')
    (hSameUseFields : ∀ (usePtr : OpOperandPtr),
      usePtr.InBounds ctx → (usePtr.get! ctx).value = valuePtr →
      (usePtr.get! ctx') = (usePtr.get! ctx))
    (hPreservesInBounds' : ∀ (usePtr : OpOperandPtr),
      usePtr.InBounds ctx' →
      (usePtr.get! ctx').value = valuePtr →
      usePtr.InBounds ctx)
    (hSameUseFields' : ∀ (usePtr : OpOperandPtr),
      usePtr.InBounds ctx' →
      (usePtr.get! ctx').value = valuePtr →
      (usePtr.get! ctx) = (usePtr.get! ctx')) :
    valuePtr.WellFormedUseDefChainMissingLink ctx' array (by grind) missingUses := by
  constructor <;> grind [ValuePtr.WellFormedUseDefChainMissingLink]

/- OpOperandPtr.setValue -/

theorem ValuePtr.WellFormedUseDefChainMissingLink_OpOperandPtr_setValue_of_WellFormedUseDefChainMissingLink
    {use : OpOperandPtr} (useInBounds : use.InBounds ctx)
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ value) :
    value.WellFormedUseDefChainMissingLink ctx array valueInBounds missingUses →
    value.WellFormedUseDefChainMissingLink (use.setValue ctx value) array (by grind) (missingUses.insert use) := by
  intros hWF
  constructor <;> grind [ValuePtr.WellFormedUseDefChainMissingLink]

theorem ValuePtr.WellFormedUseDefChainMissingLink_OpOperandPtr_setValue_of_WellFormedUseDefChain
    {use : OpOperandPtr} (useInBounds : use.InBounds ctx)
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ value) :
    value.WellFormedUseDefChain ctx array valueInBounds →
    value.WellFormedUseDefChainMissingLink (use.setValue ctx value) array (by grind) (Std.ExtHashSet.ofList [use]) := by
  intros hWF
  constructor <;> grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChainMissingLink]

/- OpOperandPtr.insertIntoCurrent -/

theorem ValuePtr.WellFormedUseDefChainMissingLink.ValuePtr_getFirstUse_ne_of_value_ne
    {use use' : OpOperandPtr}
    (valueNe : (use.get! ctx).value ≠ (use'.get! ctx).value)
    {valueInBounds}
    (hWF : (use.get! ctx).value.WellFormedUseDefChainMissingLink ctx array valueInBounds missingUses) :
    (use.get! ctx).value.getFirstUse! ctx ≠ some use' := by
  grind [ValuePtr.WellFormedUseDefChainMissingLink]

theorem OpOperandPtr.get!_insertIntoCurrent_of_value_ne
    (ctxInBounds : ctx.FieldsInBounds) {use use' : OpOperandPtr}
    {useInBounds : use.InBounds ctx}
    (useOfOtherValue : (use.get! ctx).value ≠ (use'.get! ctx).value) array valueInBounds missingUses
    (hWF : (use.get! ctx).value.WellFormedUseDefChainMissingLink ctx array valueInBounds missingUses) :
    use'.get! (insertIntoCurrent ctx use useInBounds ctxInBounds) = use'.get! ctx := by
  grind [ValuePtr.WellFormedUseDefChainMissingLink.ValuePtr_getFirstUse_ne_of_value_ne]

theorem ValuePtr.WellFormedUseDefChainMissingLink_insertIntoCurrent_self
    {value : ValuePtr} {valueInBounds} {hvalue : use ∈ missingUses}
    (hWF: value.WellFormedUseDefChainMissingLink ctx array valueInBounds missingUses) :
    value.WellFormedUseDefChainMissingLink (use.insertIntoCurrent ctx (by grind) ctxInBounds) (#[use] ++ array) (by grind) (missingUses.erase use) := by
  have : (use.get! ctx).value = value := by grind [ValuePtr.WellFormedUseDefChainMissingLink.missingUsesValue]
  constructor
  case prevNextUse =>
    simp only [gt_iff_lt, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    simp only [OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent]
    intros i
    cases i <;> grind [ValuePtr.WellFormedUseDefChainMissingLink]
  case nextElems =>
    simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    grind [ValuePtr.WellFormedUseDefChainMissingLink]
  all_goals grind [ValuePtr.WellFormedUseDefChainMissingLink]

theorem ValuePtr.WellFormedUseDefChain_insertIntoCurrent_self
    {value : ValuePtr} (valueInBounds)
    (hWF: value.WellFormedUseDefChainMissingLink ctx array valueInBounds (Std.ExtHashSet.ofList [use])) :
    value.WellFormedUseDefChain (use.insertIntoCurrent ctx (by grind [ValuePtr.WellFormedUseDefChainMissingLink]) ctxInBounds) (#[use] ++ array) (by grind) := by
  have : ∅ = (Std.ExtHashSet.ofList [use]).erase use := by grind
  simp [←ValuePtr.WellFormedUseDefChainMissingLink_iff_WellFormedUseDefChain]
  grind [ValuePtr.WellFormedUseDefChainMissingLink_insertIntoCurrent_self]

theorem ValuePtr.WellFormedUseDefChainMissingLink_insertIntoCurrent_other
    {value value' : ValuePtr} (valueNe : value ≠ value') {valueInBounds valueInBounds'} {hvalue : use ∈ missingUses'}
    (hWF : value.WellFormedUseDefChainMissingLink ctx array valueInBounds missingUses)
    (hWF' : value'.WellFormedUseDefChainMissingLink ctx array' valueInBounds' missingUses') :
    value.WellFormedUseDefChainMissingLink (use.insertIntoCurrent ctx (by grind) ctxInBounds) array (by grind) missingUses := by
  apply ValuePtr.WellFormedUseDefChainMissingLink_unchanged (ctx := ctx) <;> try grind [ValuePtr.WellFormedUseDefChainMissingLink, ValuePtr.WellFormedUseDefChain]

theorem ValuePtr.WellFormedUseDefChain_insertIntoCurrent_other
    {value value' : ValuePtr} (valueNe : value ≠ value') {valueInBounds valueInBounds'} {hvalue : use ∈ missingUses'}
    (hWF : value.WellFormedUseDefChain ctx array valueInBounds)
    (hWF' : value'.WellFormedUseDefChainMissingLink ctx array' valueInBounds' missingUses') :
    value.WellFormedUseDefChain (use.insertIntoCurrent ctx (by grind) ctxInBounds) array (by grind) := by
  apply IRContext.ValuePtr_UseDefChainWellFormed_unchanged (ctx := ctx) <;> try grind [ValuePtr.WellFormedUseDefChainMissingLink, ValuePtr.WellFormedUseDefChain]


-- OLD LEMMAS

theorem OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse
    (operandPtrInBounds : operandPtr.InBounds ctx) (valuePtrIn : ValuePtr.InBounds valuePtr ctx)
    (valuePtrWF : valuePtr.WellFormedUseDefChainMissingLink ctx array (by grind) missingUses)
    (operandValueWF : (operandPtr.get! ctx).value.WellFormedUseDefChain ctx array' (by grind)) :
      valuePtr.getFirstUse! (OpOperandPtr.removeFromCurrent ctx operandPtr operandPtrInBounds ctxInBounds) =
        if valuePtr.getFirstUse! ctx = some operandPtr then
          (operandPtr.get! ctx).nextUse
        else
          valuePtr.getFirstUse! ctx := by
  split
  · grind [ValuePtr.WellFormedUseDefChainMissingLink, ValuePtr.WellFormedUseDefChain_back_eq_of_getFirstUse]
  · grind [ValuePtr.WellFormedUseDefChain_getFirstUse!_eq_of_back_eq_valueFirstUse]

set_option maxHeartbeats 400000

theorem OpOperandPtr.OpOperandPtr_get_removeFromCurrent_different_value
    (ctxInBounds : ctx.FieldsInBounds) {use use' : OpOperandPtr}
    (useInBounds : use.InBounds ctx)
    (use'InBounds: use'.InBounds ctx)
    (useOfOtherValue : (use.get! ctx).value ≠ (use'.get! ctx).value) {valueInBounds}
    (hWF : (use.get! ctx).value.WellFormedUseDefChain ctx array valueInBounds) :
    use'.get! (removeFromCurrent ctx use useInBounds ctxInBounds) = use'.get ctx (by grind) := by
  simp only [removeFromCurrent]
  simp only [←OpOperandPtr.get!_eq_get]
  split <;> grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_of_mem]

theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_back_same_value
    (useInBounds : OpOperandPtr.InBounds use ctx)
    (useOfValue : (use.get! ctx).value = value) array valueInBounds
    (hWF : value.WellFormedUseDefChain ctx array valueInBounds)
    i (iPos : i > 0) (iInBounds : i < (array.erase use).size) useInBounds ctxInBounds (iInBounds' : (array.erase use)[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (((array.erase use)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds)).back = OpOperandPtrPtr.operandNextUse (array.erase use)[i - 1] := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  have useInArray : use ∈ array := by grind [ValuePtr.WellFormedUseDefChain]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  subst use
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
        grind [Array.erase_eq_eraseIdx_of_idxOf, ValuePtr.WellFormedUseDefChain_array_erase_array_index]
  have hNextUse : (array[useIdx].get! ctx).nextUse = array[useIdx + 1]? := by
    grind [ValuePtr.WellFormedUseDefChain]
  simp only [hNextUse]
  by_cases i = useIdx
  · subst useIdx
    split <;> grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_eraseIdx_of_ge]
  · by_cases i < useIdx
    · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_array_injective]
    · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_array_injective]

theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_nextUse
    (useInBounds : OpOperandPtr.InBounds use ctx)
    (useOfValue : (use.get! ctx).value = value)
    (hWF : value.WellFormedUseDefChain ctx array valueInBounds)
    {i} (iInBounds : i < (array.erase use).size)
    (iInBounds' : (array.erase use)[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (((array.erase use)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds)).nextUse = (array.erase use)[i + 1]? := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  have useInArray : use ∈ array := by grind [ValuePtr.WellFormedUseDefChain]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  subst use
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
    grind [Array.erase_eq_eraseIdx_of_idxOf, ValuePtr.WellFormedUseDefChain_array_erase_array_index]
  have hNextUse : (array[useIdx].get! ctx).nextUse = array[useIdx + 1]? := by
    grind [ValuePtr.WellFormedUseDefChain]
  simp only [hNextUse]
  by_cases i < useIdx
  · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_array_injective]
  · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_array_injective]


theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_self
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) (value : ValuePtr)
    (useOfValue : (use.get! ctx).value = value) array valueInBounds :
    value.WellFormedUseDefChain ctx array valueInBounds →
    value.WellFormedUseDefChainMissingLink (use.removeFromCurrent ctx (by grind) (by grind)) (array.erase use) (by grind) (Std.ExtHashSet.ofList [use]) := by
  intros hWF
  constructor
  case firstUseBack =>
    intros firstUse heq
    simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
    simp (disch := grind) [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse (missingUses := ∅) (array := array) (array' := array)] at heq
    split
    · rename_i h
      simp only [h, ite_eq_left_iff] at heq
      by_cases value.getFirstUse ctx (by grind) = some use
      · grind [ValuePtr.WellFormedUseDefChain]
      · grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_of_mem]
    · grind [ValuePtr.WellFormedUseDefChain]
  case arrayInBounds => grind [ValuePtr.WellFormedUseDefChain]
  case firstElem =>
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse (array := array) (array' := array) (missingUses := ∅)]
    · have useInArray : use ∈ array := by grind [ValuePtr.WellFormedUseDefChain]
      have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
      subst use
      have := ValuePtr.WellFormedUseDefChain_array_erase_array_index hWF useIdx (by grind)
      simp [Array.erase_eq_eraseIdx_of_idxOf this useIdxInBounds]
      cases useIdx <;> grind [ValuePtr.WellFormedUseDefChain]
    · grind
    · grind
    · grind
  case allUsesInChain =>
    intros use' use'InBounds huse'Value
    simp only [Std.ExtHashSet.ofList_singleton, Std.ExtHashSet.mem_insert, beq_iff_eq,
      Std.ExtHashSet.not_mem_empty, or_false]
    by_cases use = use' <;> rename_i hUse
    · subst use
      simp only [not_true_eq_false, iff_false]
      grind [Array.getElem?_of_mem, ValuePtr.WellFormedUseDefChain_array_erase_mem_self]
    · grind [ValuePtr.WellFormedUseDefChain]
  case useValue => grind [ValuePtr.WellFormedUseDefChain]
  case prevNextUse => grind [OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_back_same_value, Array.mem_of_mem_erase, ValuePtr.WellFormedUseDefChain]
  case nextElems => grind [OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_nextUse, Array.mem_of_mem_erase, ValuePtr.WellFormedUseDefChain]
  case missingUsesInBounds => grind [ValuePtr.WellFormedUseDefChain]
  case missingUsesValue => grind [ValuePtr.WellFormedUseDefChain]

theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other_back
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds)
    (useOfValue : (use.get ctx useInBounds).value ≠ value') array valueInBounds array' valueInBounds'
    (hWF' : value'.WellFormedUseDefChain ctx array valueInBounds)
    (hWF : (use.get ctx useInBounds).value.WellFormedUseDefChain ctx array' valueInBounds')
    (i : Nat) (iPos : i > 0) (iInBounds : i < array.size) useInBounds (_ : array[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (array[i].get! (removeFromCurrent ctx use useInBounds ctxInBounds)).back = OpOperandPtrPtr.operandNextUse array[i - 1] := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  suffices (use.get ctx (by grind)).nextUse ≠ some array[i] by grind [ValuePtr.WellFormedUseDefChain]
  have : use ∈ array' := by grind [ValuePtr.WellFormedUseDefChain]
  cases h: (use.get ctx (by grind)).nextUse
  case none => grind
  case some nextUse =>
    simp only [ne_eq, Option.some.injEq]
    intro heq
    subst nextUse
    grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_of_mem]


@[grind .]
theorem ValuePtr.WellFormedUseDefChain_back_value_firstUse_eq
    (ctx : IRContext) (array : Array OpOperandPtr)
    (use : OpOperandPtr) (useInBounds : use.InBounds ctx) valueInBounds
    (hWF : (use.get ctx useInBounds).value.WellFormedUseDefChain ctx array valueInBounds) value :
    (use.get ctx useInBounds).back = OpOperandPtrPtr.valueFirstUse value →
    value = (use.get ctx useInBounds).value := by
  grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_of_mem]

@[grind .]
theorem ValuePtr.WellFormedUseDefChain_back_value_nextUse_eq
    (ctx : IRContext) (array : Array OpOperandPtr)
    (use : OpOperandPtr) (useInBounds : use.InBounds ctx) valueInBounds
    (hWF : (use.get ctx useInBounds).value.WellFormedUseDefChain ctx array valueInBounds) nextUse :
    (use.get ctx useInBounds).back = OpOperandPtrPtr.operandNextUse nextUse →
    ∀ nextUseInBounds, (nextUse.get ctx nextUseInBounds).value = (use.get ctx useInBounds).value := by
  grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_of_mem]

theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other_nextUse
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds)
    (useOfValue : (use.get ctx useInBounds).value ≠ value') array valueInBounds array' valueInBounds'
    (hWF' : value'.WellFormedUseDefChain ctx array valueInBounds)
    (hWF : (use.get ctx useInBounds).value.WellFormedUseDefChain ctx array' valueInBounds')
    (i : Nat) (iInBounds : i < array.size) useInBounds (_ : array[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (array[i].get! (removeFromCurrent ctx use useInBounds ctxInBounds)).nextUse = array[i + 1]? := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  cases h: (use.get! ctx).back
  case operandNextUse nextUse =>
    simp only [OpOperandPtrPtr.operandNextUse.injEq]
    have : (use.get ctx (by grind)).back.InBounds ctx := by grind
    have : nextUse.InBounds ctx := by grind
    have : (nextUse.get ctx (by grind)).value = (use.get ctx (by grind)).value := by grind [ValuePtr.WellFormedUseDefChain]
    split <;> grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_of_mem]
  case valueFirstUse val =>
    simp only [reduceCtorEq, ↓reduceIte]
    grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_of_mem]


theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) (value': ValuePtr)
    (useOfValue : (use.get! ctx).value ≠ value') array array' valueInBounds valueInBounds' :
    value'.WellFormedUseDefChain ctx array valueInBounds →
    (use.get! ctx).value.WellFormedUseDefChain ctx array' valueInBounds' →
    value'.WellFormedUseDefChain (use.removeFromCurrent ctx (by grind) (by grind)) array (by grind) := by
  intros hWF hWF'
  constructor
  case firstUseBack =>
    intros firstUse heq
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse (array := array) (array' := array') (missingUses := ∅)] at heq
    · rw [OpOperandPtr.OpOperandPtr_get_removeFromCurrent_different_value (array := array')] <;> grind [ValuePtr.WellFormedUseDefChain]
    · grind
    · grind
    · grind
  case arrayInBounds => grind [ValuePtr.WellFormedUseDefChain]
  case firstElem =>
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse (array := array) (array' := array') (missingUses := ∅)]
    · have : value'.getFirstUse ctx (by grind) ≠ some use := by grind [ValuePtr.WellFormedUseDefChain]
      grind [ValuePtr.WellFormedUseDefChain]
    · grind
    · grind
    · grind
  case allUsesInChain => grind [ValuePtr.WellFormedUseDefChain]
  case useValue => grind [ValuePtr.WellFormedUseDefChain]
  case prevNextUse =>
    intros
    apply OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other_back (value' := value') (array := array) (array' := array') <;> grind [ValuePtr.WellFormedUseDefChain]
  case nextElems =>
    intros
    apply OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other_nextUse (value' := value') (array := array) (array' := array') <;> grind [ValuePtr.WellFormedUseDefChain]

-- value.WellFormedUseDefChain (use.setValue ... ⋯ value') (array.erase use) ⋯

theorem OpOperandPtr.setValue_WellFormedUseDefChainMissingLink_append
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx) (value value': ValuePtr)
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ value')
    array valueInBounds :
    use ∈ missingUses →
    value.WellFormedUseDefChainMissingLink ctx array valueInBounds missingUses →
    value.WellFormedUseDefChainMissingLink (use.setValue ctx value') array (by grind) (missingUses.erase use) := by
  intros useNotMissing hWF
  constructor <;> grind [ValuePtr.WellFormedUseDefChainMissingLink]

theorem OpOperandPtr.setValue_WellFormedUseDefChain_other
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx) (value : ValuePtr)
    (useOfOtherValue' : (use.get ctx useInBounds).value ≠ value')
    (valueNe : value ≠ value') array valueInBounds :
    value'.WellFormedUseDefChain ctx array valueInBounds →
    value'.WellFormedUseDefChain (use.setValue ctx value) array (by grind) := by
  intro hWF
  apply IRContext.ValuePtr_UseDefChainWellFormed_unchanged (ctx := ctx) <;> grind

theorem ValuePtr.WellFormedUseDefChain_array_mem_erase
    (hWF : ValuePtr.WellFormedUseDefChain value ctx array valueInBounds) :
    use ∉ array.erase use := by
  intros hcontra
  have := Array.Mem.val hcontra
  simp only [Array.toList_erase] at this
  grind [ValuePtr.WellFormedUseDefChain_array_toList_Nodup]

end Mlir
