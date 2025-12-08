import Mlir.Core.Basic
import Mlir.WellFormedness.WellFormed
import Mlir.Rewriter
import Std.Data.HashSet
import Std.Data.ExtHashSet

namespace Mlir

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
  firstElem : array[0]? = value.getFirstUse ctx
  firstUseBack (heq : value.getFirstUse ctx = some firstUse) :
    (firstUse.get ctx).back = .valueFirstUse value
  allUsesInChain (use : OpOperandPtr) (huse : use.InBounds ctx) :
    (use.get ctx).value = value → (use ∈ array ↔ use ∉ missingUses)
  useValue (hin : use ∈ array) : (use.get ctx).value = value
  nextElems (hi : i < array.size) :
    (array[i].get ctx).nextUse = array[i + 1]?
  prevNextUse (iPos : i > 0) (iInBounds : i < array.size) :
    (array[i].get ctx).back = OpOperandPtrPtr.operandNextUse array[i - 1]
  missingUsesInBounds (hin : use ∈ missingUses) : use.InBounds ctx
  missingUsesValue (hin : use ∈ missingUses) : (use.get ctx (by grind)).value = value

@[simp, grind =]
theorem ValuePtr.WellFormedUseDefChainMissingLink_iff_WellFormedUseDefChain
    (value : ValuePtr) (ctx : IRContext) (array : Array OpOperandPtr)
    (hvalue : value.InBounds ctx) :
    (ValuePtr.WellFormedUseDefChainMissingLink value ctx array hvalue ∅) ↔
    ValuePtr.WellFormedUseDefChain value ctx array hvalue := by
  constructor <;> intros <;>
  constructor <;> grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChainMissingLink]

theorem OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse
    ctx ctxInBounds (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx) (valuePtr : ValuePtr) valuePtrIn
    (valuePtrWF : valuePtr.WellFormedUseDefChainMissingLink ctx array (by grind) missingUses)
    (operandValueWF : (operandPtr.get ctx (by grind)).value.WellFormedUseDefChain ctx array' (by grind)) :
      valuePtr.getFirstUse (OpOperandPtr.removeFromCurrent ctx operandPtr operandPtrInBounds ctxInBounds) valuePtrIn =
        if valuePtr.getFirstUse ctx (by grind) = some operandPtr then
          (operandPtr.get ctx (by grind)).nextUse
        else
          valuePtr.getFirstUse ctx (by grind) := by
  simp only [removeFromCurrent]
  split
  · simp only [←ValuePtr.getFirstUse!_eq_getFirstUse]
    split <;> grind [ValuePtr.WellFormedUseDefChainMissingLink]
  · rename_i h
    simp only [←ValuePtr.getFirstUse!_eq_getFirstUse]
    split
    · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_ValuePtr_back_FirstUse]
    · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_ValuePtr_back_FirstUse]


set_option maxHeartbeats 400000

theorem OpOperandPtr.OpOperandPtr_get_removeFromCurrent_different_value
    (ctx : IRContext) (ctxInBounds : ctx.FieldsInBounds) (use use' : OpOperandPtr)
    useInBounds use'InBounds
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ (use'.get ctx use'InBounds).value) array valueInBounds
    (hWF : (use.get ctx useInBounds).value.WellFormedUseDefChain ctx array valueInBounds) useInBounds' :
    use'.get (removeFromCurrent ctx use useInBounds ctxInBounds) useInBounds' = use'.get ctx (by grind) := by
  simp only [removeFromCurrent]
  simp only [←OpOperandPtr.get!_eq_get]
  split <;> grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_of_mem]

theorem OpOperandPtr.OpOperandPtr_get_insertIntoCurrent_different_value
    (ctx : IRContext) (ctxInBounds : ctx.FieldsInBounds) (use use' : OpOperandPtr)
    useInBounds use'InBounds
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ (use'.get ctx use'InBounds).value) array valueInBounds missingUses
    (hWF : (use.get ctx useInBounds).value.WellFormedUseDefChainMissingLink ctx array valueInBounds missingUses) useInBounds' :
    use'.get (insertIntoCurrent ctx use useInBounds ctxInBounds) useInBounds' = use'.get ctx (by grind) := by
  simp only [insertIntoCurrent]
  simp only [←OpOperandPtr.get!_eq_get]
  split
  · grind
  · rename_i nextPtr hNextPtr
    -- simp only [get!_OpOperandPtr_setBack, get_ValuePtr_setFirstUse, get_OpOperandPtr_setNextUse, get_OpOperandPtr_setBack, get!_ValuePtr_setFirstUse, get!_OpOperandPtr_setNextUse]
    -- simp only [ValuePtr.getFirstUse_OpOperandPtr_setBack] at hNextPtr
    have : (nextPtr.get ctx (by grind)).value = (use.get ctx (by grind)).value := by grind [ValuePtr.WellFormedUseDefChainMissingLink]
    have : use' ≠ nextPtr := by grind
    rw [OpOperandPtr.get!_OpOperandPtr_setBack] <;> grind

theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_back_same_value
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (value : ValuePtr)
    (useOfValue : (use.get ctx useInBounds).value = value) array valueInBounds
    (hWF : value.WellFormedUseDefChain ctx array valueInBounds)
    i (iPos : i > 0) (iInBounds : i < (array.erase use).size) useInBounds ctxInBounds (iInBounds' : (array.erase use)[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (((array.erase use)[i]).get (removeFromCurrent ctx use useInBounds ctxInBounds) iInBounds').back = OpOperandPtrPtr.operandNextUse (array.erase use)[i - 1] := by
  simp only [OpOperandPtr.removeFromCurrent_OpOperandPtr_get_back]
  have useInArray : use ∈ array := by grind [ValuePtr.WellFormedUseDefChain]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  subst use
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
        grind [Array.erase_eq_eraseIdx_of_idxOf, ValuePtr.WellFormedUseDefChain_array_erase_array_index]
  have hNextUse : (array[useIdx].get ctx (by grind)).nextUse = array[useIdx + 1]? := by
    grind [ValuePtr.WellFormedUseDefChain]
  simp only [hNextUse]
  by_cases i = useIdx
  · subst useIdx
    split <;> grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_eraseIdx_of_ge]
  · by_cases i < useIdx
    · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_array_injective]
    · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_array_injective]

theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_nextUse
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (value : ValuePtr)
    (useOfValue : (use.get ctx useInBounds).value = value) array valueInBounds
    (hWF : value.WellFormedUseDefChain ctx array valueInBounds)
    i (iInBounds : i < (array.erase use).size) useInBounds ctxInBounds (iInBounds' : (array.erase use)[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (((array.erase use)[i]).get (removeFromCurrent ctx use useInBounds ctxInBounds) iInBounds').nextUse = (array.erase use)[i + 1]? := by
  simp only [OpOperandPtr.removeFromCurrent_OpOperandPtr_get_nextUse]
  have useInArray : use ∈ array := by grind [ValuePtr.WellFormedUseDefChain]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  subst use
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
    grind [Array.erase_eq_eraseIdx_of_idxOf, ValuePtr.WellFormedUseDefChain_array_erase_array_index]
  have hNextUse : (array[useIdx].get ctx (by grind)).nextUse = array[useIdx + 1]? := by
    grind [ValuePtr.WellFormedUseDefChain]
  simp only [hNextUse]
  by_cases i < useIdx
  · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_array_injective]
  · grind [ValuePtr.WellFormedUseDefChain, ValuePtr.WellFormedUseDefChain_array_injective]


theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_self
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) (value : ValuePtr)
    (useOfValue : (use.get ctx useInBounds).value = value) array valueInBounds :
    value.WellFormedUseDefChain ctx array valueInBounds →
    value.WellFormedUseDefChainMissingLink (use.removeFromCurrent ctx (by grind) (by grind)) (array.erase use) (by grind) (Std.ExtHashSet.ofList [use]) := by
  intros hWF
  constructor
  case firstUseBack =>
    intros firstUse heq
    simp only [OpOperandPtr.removeFromCurrent_OpOperandPtr_get_back]
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
      have := ValuePtr.WellFormedUseDefChain_array_erase_array_index value ctx array (by grind) (by grind) useIdx (by grind)
      simp [Array.erase_eq_eraseIdx_of_idxOf this useIdxInBounds]
      cases useIdx <;> grind [ValuePtr.WellFormedUseDefChain]
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
  case prevNextUse => grind [OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_back_same_value]
  case nextElems => grind [OpOperandPtr.removeFromCurrent_WellFormedUseDefChainMissingLink_nextUse]
  case missingUsesInBounds => grind [ValuePtr.WellFormedUseDefChain]
  case missingUsesValue => grind [ValuePtr.WellFormedUseDefChain]

theorem OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other_back
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds)
    (useOfValue : (use.get ctx useInBounds).value ≠ value') array valueInBounds array' valueInBounds'
    (hWF' : value'.WellFormedUseDefChain ctx array valueInBounds)
    (hWF : (use.get ctx useInBounds).value.WellFormedUseDefChain ctx array' valueInBounds')
    (i : Nat) (iPos : i > 0) (iInBounds : i < array.size) useInBounds (arrayIInBounds : array[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (array[i].get (removeFromCurrent ctx use useInBounds ctxInBounds) arrayIInBounds).back = OpOperandPtrPtr.operandNextUse array[i - 1] := by
  simp only [removeFromCurrent_OpOperandPtr_get_back]
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
    (i : Nat) (iInBounds : i < array.size) useInBounds (arrayIInBounds : array[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (array[i].get (removeFromCurrent ctx use useInBounds ctxInBounds) arrayIInBounds).nextUse = array[i + 1]? := by
  simp only [removeFromCurrent_OpOperandPtr_get_nextUse]
  cases h: (use.get ctx (by grind)).back
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
    (useOfValue : (use.get ctx useInBounds).value ≠ value') array array' valueInBounds valueInBounds' :
    value'.WellFormedUseDefChain ctx array valueInBounds →
    (use.get ctx useInBounds).value.WellFormedUseDefChain ctx array' valueInBounds' →
    value'.WellFormedUseDefChain (use.removeFromCurrent ctx (by grind) (by grind)) array (by grind) := by
  intros hWF hWF'
  constructor
  case firstUseBack =>
    intros firstUse heq
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse (array := array) (array' := array') (missingUses := ∅)] at heq
    · rw [OpOperandPtr.OpOperandPtr_get_removeFromCurrent_different_value (array := array')] <;> grind [ValuePtr.WellFormedUseDefChain]
    · grind
    · grind
  case arrayInBounds => grind [ValuePtr.WellFormedUseDefChain]
  case firstElem =>
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse (array := array) (array' := array') (missingUses := ∅)]
    · have : value'.getFirstUse ctx (by grind) ≠ some use := by grind [ValuePtr.WellFormedUseDefChain]
      grind [ValuePtr.WellFormedUseDefChain]
    · grind
    · grind
  case allUsesInChain => grind [ValuePtr.WellFormedUseDefChain]
  case useValue => grind [ValuePtr.WellFormedUseDefChain]
  case prevNextUse =>
    intros
    apply OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other_back (value' := value') (array := array) (array' := array') <;> grind
  case nextElems =>
    intros
    apply OpOperandPtr.removeFromCurrent_WellFormedUseDefChain_other_nextUse (value' := value') (array := array) (array' := array') <;> grind


theorem OpOperandPtr.setValue_WellFormedUseDefChainMissingLink
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx) (value : ValuePtr)
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ value) array valueInBounds :
    value.WellFormedUseDefChain ctx array valueInBounds →
    value.WellFormedUseDefChainMissingLink (use.setValue ctx value) array (by grind) (Std.ExtHashSet.ofList [use]) := by
  intros hWF
  constructor
  case firstUseBack => grind [ValuePtr.WellFormedUseDefChain]
  case arrayInBounds => grind [ValuePtr.WellFormedUseDefChain]
  case firstElem =>
    simp only [←ValuePtr.getFirstUse!_eq_getFirstUse]
    grind [ValuePtr.WellFormedUseDefChain]
  case allUsesInChain => grind [ValuePtr.WellFormedUseDefChain]
  case useValue => grind [ValuePtr.WellFormedUseDefChain]
  case prevNextUse => grind [ValuePtr.WellFormedUseDefChain]
  case nextElems => grind [ValuePtr.WellFormedUseDefChain]
  case missingUsesInBounds => grind [ValuePtr.WellFormedUseDefChain]
  case missingUsesValue => grind [ValuePtr.WellFormedUseDefChain]

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

theorem OpOperandPtr.insertIntoCurrent_WellFormedUseDefChain_self
    (ctx : IRContext) ctxInBounds (use : OpOperandPtr) (useInBounds : use.InBounds ctx) (value : ValuePtr)
    array valueInBounds :
    value.WellFormedUseDefChainMissingLink ctx array valueInBounds (Std.ExtHashSet.ofList [use]) →
    value.WellFormedUseDefChain (use.insertIntoCurrent ctx (by grind) ctxInBounds) (#[use] ++ array) (by grind) := by
  intros hWF
  have : (use.get ctx useInBounds).value = value := by grind [ValuePtr.WellFormedUseDefChainMissingLink]
  constructor
  case firstUseBack =>
    let this := OpOperandPtr.get!_insertIntoCurrent (operand' := use) ctx ctxInBounds useInBounds useInBounds ctxInBounds (by grind [ValuePtr.WellFormedUseDefChainMissingLink])
    simp only [↓reduceDIte] at this
    grind
  case arrayInBounds => grind [ValuePtr.WellFormedUseDefChainMissingLink]
  case firstElem => grind
  case allUsesInChain => grind [ValuePtr.WellFormedUseDefChainMissingLink]
  case useValue => grind [ValuePtr.WellFormedUseDefChainMissingLink]
  case prevNextUse =>
    simp only [gt_iff_lt, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    simp (disch := grind) only [OpOperandPtr.OpOperandPtr_getBack_insertIntoCurrent]
    intros i iPos iInBounds
    cases i
    case zero => grind
    case succ i =>
      simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.le_add_left, Array.getElem_append_right, Nat.add_one_sub_one]
      cases i
      case zero =>
        simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
          Nat.lt_add_one, Array.getElem_append_left, List.getElem_toArray, List.getElem_cons_zero,
          ite_eq_left_iff]
        grind [ValuePtr.WellFormedUseDefChainMissingLink]
      case succ i =>
        simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
          Nat.le_add_left, Array.getElem_append_right, Nat.add_one_sub_one]
        grind [ValuePtr.WellFormedUseDefChainMissingLink]
  case nextElems =>
    simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    intros i iInBounds
    let this := @OpOperandPtr.OpOperandPtr_getNext_insertIntoCurrent ctx (by grind) ((#[use] ++ array)[i]'(by grind)) use (by grind) (by grind) (by grind [ValuePtr.WellFormedUseDefChainMissingLink])
    simp only [this]
    cases i
    case zero => grind [ValuePtr.WellFormedUseDefChainMissingLink]
    case succ i =>
      simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.le_add_left, Array.getElem_append_right, Nat.add_one_sub_one]
      have : array[i] ≠ use := by grind [ValuePtr.WellFormedUseDefChainMissingLink]
      simp only [this, ↓reduceIte]
      have : (#[use] ++ array)[i + 1 + 1]? = array[i + 1]? := by grind
      simp only [this]
      grind [ValuePtr.WellFormedUseDefChainMissingLink]

theorem OpOperandPtr.insertIntoCurrent_WellFormedUseDefChain_other
    (ctx : IRContext) ctxInBounds (use : OpOperandPtr) (useInBounds : use.InBounds ctx) (value value': ValuePtr)
    (useOfValue' : (use.get ctx useInBounds).value = value') (hvalueNe : value ≠ value') valueInBounds valueInBounds' :
    value.WellFormedUseDefChain ctx array valueInBounds →
    value'.WellFormedUseDefChainMissingLink ctx array' valueInBounds' missingUses →
    value.WellFormedUseDefChain (use.insertIntoCurrent ctx (by grind) ctxInBounds) array (by grind) := by
  intros hWF hWF'
  apply IRContext.ValuePtr_UseDefChainWellFormed_unchanged (ctx := ctx) <;> try grind [OpOperandPtr.OpOperandPtr_get_insertIntoCurrent_different_value]

end Mlir
