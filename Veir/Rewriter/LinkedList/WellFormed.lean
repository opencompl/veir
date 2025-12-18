import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.LinkedList.GetSet
import Std.Data.HashSet
import Std.Data.ExtHashSet

namespace Veir

attribute [local grind ext] OpOperand

/- OpOperandPtr.insertIntoCurrent -/

theorem OpOperandPtr.get!_insertIntoCurrent_of_value_ne
    (ctxInBounds : ctx.FieldsInBounds) {use use' : OpOperandPtr}
    {useInBounds : use.InBounds ctx}
    (useOfOtherValue : (use.get! ctx).value ≠ (use'.get! ctx).value) array missingUses
    (hWF : (use.get! ctx).value.DefUse ctx array missingUses) :
    use'.get! (insertIntoCurrent ctx use useInBounds ctxInBounds) = use'.get! ctx := by
  grind [ValuePtr.DefUse.ValuePtr_getFirstUse_ne_of_value_ne]

theorem ValuePtr.defUse_insertIntoCurrent_self
    {value : ValuePtr} {hvalue : use ∈ missingUses}
    (hWF: value.DefUse ctx array missingUses) :
    value.DefUse (use.insertIntoCurrent ctx (by grind) ctxInBounds) (#[use] ++ array) (missingUses.erase use) := by
  have : (use.get! ctx).value = value := by grind [ValuePtr.DefUse.missingUsesValue]
  constructor
  case prevNextUse =>
    simp only [gt_iff_lt, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    simp only [OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent]
    intros i
    cases i <;> grind [ValuePtr.DefUse]
  case nextElems =>
    simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    grind [ValuePtr.DefUse]
  all_goals grind [ValuePtr.DefUse]

theorem ValuePtr.defUse_insertIntoCurrent_self_empty
    {value : ValuePtr}
    (hWF: value.DefUse ctx array (Std.ExtHashSet.ofList [use])) :
    value.DefUse (use.insertIntoCurrent ctx (by grind [ValuePtr.DefUse.missingUsesInBounds]) ctxInBounds) (#[use] ++ array) := by
  have : ∅ = (Std.ExtHashSet.ofList [use]).erase use := by grind
  grind [ValuePtr.defUse_insertIntoCurrent_self]

theorem ValuePtr.defUse_insertIntoCurrent_other
    {value value' : ValuePtr} (valueNe : value ≠ value') {hvalue : use ∈ missingUses'}
    (hWF : value.DefUse ctx array missingUses)
    (hWF' : value'.DefUse ctx array' missingUses') :
    value.DefUse (use.insertIntoCurrent ctx (by grind) ctxInBounds) array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind [ValuePtr.DefUse]

theorem BlockPtr.defUse_OpOperandPtr_insertIntoCurrent
    {block : BlockPtr} {blockInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : block.DefUse ctx array blockInBounds) :
    block.DefUse (use.insertIntoCurrent ctx useInBounds ctxInBounds) array (by grind) := by
  apply BlockPtr.DefUse_unchanged (ctx := ctx) <;> grind

theorem BlockPtr.operationChainWellFormed_OpOperandPtr_insertIntoCurrent
    {block : BlockPtr} {blockInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : block.OperationChainWellFormed ctx array blockInBounds) :
    block.OperationChainWellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds) array (by grind) := by
  apply BlockPtr.OperationChainWellFormed_unchanged (ctx := ctx) <;> grind

theorem RegionPtr.blockChainWellFormed_OpOperandPtr_insertIntoCurrent
    {region : RegionPtr} {regionInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : region.BlockChainWellFormed ctx array regionInBounds) :
    region.BlockChainWellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds) array (by grind) := by
  apply RegionPtr.BlockChainWellFormed_unchanged (ctx := ctx) <;> grind

theorem Operation.wellFormed_OpOperandPtr_insertIntoCurrent
    {opPtr : OperationPtr} {opInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : (opPtr.get! ctx).WellFormed ctx opPtr opInBounds) :
    (opPtr.get! (use.insertIntoCurrent ctx useInBounds ctxInBounds)).WellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds) opPtr (by grind) := by
  apply Operation.WellFormed_unchanged (ctx := ctx) <;> grind

theorem Block.wellFormed_OpOperandPtr_insertIntoCurrent
    {blockPtr : BlockPtr} {blockInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : (blockPtr.get! ctx).WellFormed ctx blockPtr blockInBounds) :
    (blockPtr.get! (use.insertIntoCurrent ctx useInBounds ctxInBounds)).WellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds) blockPtr (by grind) := by
  apply Block.WellFormed_unchanged (ctx := ctx) <;> grind

theorem Region.wellFormed_OpOperandPtr_insertIntoCurrent
    {regionPtr : RegionPtr} (regionInBounds : regionPtr.InBounds ctx) {use : OpOperandPtr} {useInBounds}
    (hWF : (RegionPtr.get! regionPtr ctx).WellFormed ctx regionPtr) :
    (RegionPtr.get! regionPtr (use.insertIntoCurrent ctx useInBounds ctxInBounds)).WellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds) regionPtr := by
  apply Region.WellFormed_unchanged (ctx := ctx) <;> grind

-- OLD LEMMAS

theorem OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse
    {valuePtr : ValuePtr} (operandPtrInBounds : operandPtr.InBounds ctx)
    (valuePtrWF : valuePtr.DefUse ctx array missingUses)
    (operandValueWF : (operandPtr.get! ctx).value.DefUse ctx array') :
      valuePtr.getFirstUse! (OpOperandPtr.removeFromCurrent ctx operandPtr operandPtrInBounds ctxInBounds) =
        if valuePtr.getFirstUse! ctx = some operandPtr then
          (operandPtr.get! ctx).nextUse
        else
          valuePtr.getFirstUse! ctx := by
  split
  · grind [ValuePtr.DefUse, ValuePtr.DefUse_back_eq_of_getFirstUse]
  · grind [ValuePtr.DefUse_getFirstUse!_eq_of_back_eq_valueFirstUse]

set_option maxHeartbeats 400000

theorem OpOperandPtr.OpOperandPtr_get_removeFromCurrent_different_value
    (ctxInBounds : ctx.FieldsInBounds) {use use' : OpOperandPtr}
    (useInBounds : use.InBounds ctx)
    (use'InBounds: use'.InBounds ctx)
    (useOfOtherValue : (use.get! ctx).value ≠ (use'.get! ctx).value)
    (hWF : (use.get! ctx).value.DefUse ctx array) :
    use'.get! (removeFromCurrent ctx use useInBounds ctxInBounds) = use'.get ctx (by grind) := by
  simp only [removeFromCurrent]
  simp only [←OpOperandPtr.get!_eq_get]
  split <;> grind [ValuePtr.DefUse, Array.getElem?_of_mem]

theorem OpOperandPtr.removeFromCurrent_DefUse_back_same_value
    (useInBounds : OpOperandPtr.InBounds use ctx)
    (useOfValue : (use.get! ctx).value = value) array
    (hWF : value.DefUse ctx array)
    i (iPos : i > 0) (iInBounds : i < (array.erase use).size) useInBounds ctxInBounds (iInBounds' : (array.erase use)[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (((array.erase use)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds)).back = OpOperandPtrPtr.operandNextUse (array.erase use)[i - 1] := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  have useInArray : use ∈ array := by grind [ValuePtr.DefUse]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  subst use
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
        grind [Array.erase_eq_eraseIdx_of_idxOf, ValuePtr.DefUse_array_erase_array_index]
  have hNextUse : (array[useIdx].get! ctx).nextUse = array[useIdx + 1]? := by
    grind [ValuePtr.DefUse]
  simp only [hNextUse]
  by_cases i = useIdx
  · subst useIdx
    split <;> grind [ValuePtr.DefUse, Array.getElem?_eraseIdx_of_ge]
  · by_cases i < useIdx
    · grind [ValuePtr.DefUse, ValuePtr.DefUse_array_injective]
    · grind [ValuePtr.DefUse, ValuePtr.DefUse_array_injective]

theorem OpOperandPtr.removeFromCurrent_DefUse_nextUse
    (useInBounds : OpOperandPtr.InBounds use ctx)
    (useOfValue : (use.get! ctx).value = value)
    (hWF : value.DefUse ctx array)
    {i} (iInBounds : i < (array.erase use).size)
    (iInBounds' : (array.erase use)[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (((array.erase use)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds)).nextUse = (array.erase use)[i + 1]? := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  have useInArray : use ∈ array := by grind [ValuePtr.DefUse]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  subst use
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
    grind [Array.erase_eq_eraseIdx_of_idxOf, ValuePtr.DefUse_array_erase_array_index]
  have hNextUse : (array[useIdx].get! ctx).nextUse = array[useIdx + 1]? := by
    grind [ValuePtr.DefUse]
  simp only [hNextUse]
  by_cases i < useIdx
  · grind [ValuePtr.DefUse, ValuePtr.DefUse_array_injective]
  · grind [ValuePtr.DefUse, ValuePtr.DefUse_array_injective]


theorem OpOperandPtr.removeFromCurrent_DefUse_self
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) (value : ValuePtr)
    (useOfValue : (use.get! ctx).value = value) array :
    value.DefUse ctx array →
    value.DefUse (use.removeFromCurrent ctx (by grind) (by grind)) (array.erase use) (Std.ExtHashSet.ofList [use]) := by
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
      · grind [ValuePtr.DefUse]
      · grind [ValuePtr.DefUse, Array.getElem?_of_mem]
    · grind [ValuePtr.DefUse]
  case arrayInBounds => grind [ValuePtr.DefUse]
  case firstElem =>
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse (array := array) (array' := array) (missingUses := ∅)]
    · have useInArray : use ∈ array := by grind [ValuePtr.DefUse]
      have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
      subst use
      have := ValuePtr.DefUse_array_erase_array_index hWF useIdx (by grind)
      simp [Array.erase_eq_eraseIdx_of_idxOf this useIdxInBounds]
      cases useIdx <;> grind [ValuePtr.DefUse]
    · grind
    · grind
  case allUsesInChain =>
    intros use' use'InBounds huse'Value
    simp only [Std.ExtHashSet.ofList_singleton, Std.ExtHashSet.mem_insert, beq_iff_eq,
      Std.ExtHashSet.not_mem_empty, or_false]
    by_cases use = use' <;> rename_i hUse
    · subst use
      simp only [not_true_eq_false, iff_false]
      grind [Array.getElem?_of_mem, ValuePtr.DefUse_array_erase_mem_self]
    · grind [ValuePtr.DefUse]
  case prevNextUse => grind [OpOperandPtr.removeFromCurrent_DefUse_back_same_value, Array.mem_of_mem_erase, ValuePtr.DefUse]
  case nextElems => grind [OpOperandPtr.removeFromCurrent_DefUse_nextUse, Array.mem_of_mem_erase, ValuePtr.DefUse]
  all_goals grind [ValuePtr.DefUse]

theorem OpOperandPtr.removeFromCurrent_DefUse_other_back
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds)
    (useOfValue : (use.get ctx useInBounds).value ≠ value') array array'
    (hWF' : value'.DefUse ctx array)
    (hWF : (use.get ctx useInBounds).value.DefUse ctx array')
    (i : Nat) (iPos : i > 0) (iInBounds : i < array.size) useInBounds (_ : array[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (array[i].get! (removeFromCurrent ctx use useInBounds ctxInBounds)).back = OpOperandPtrPtr.operandNextUse array[i - 1] := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  suffices (use.get ctx (by grind)).nextUse ≠ some array[i] by grind [ValuePtr.DefUse]
  have : use ∈ array' := by grind [ValuePtr.DefUse]
  cases h: (use.get ctx (by grind)).nextUse
  case none => grind
  case some nextUse =>
    simp only [ne_eq, Option.some.injEq]
    intro heq
    subst nextUse
    grind [ValuePtr.DefUse, Array.getElem?_of_mem]


@[grind .]
theorem ValuePtr.DefUse_back_value_firstUse_eq
    (ctx : IRContext) (array : Array OpOperandPtr)
    (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (hWF : (use.get ctx useInBounds).value.DefUse ctx array) value :
    (use.get ctx useInBounds).back = OpOperandPtrPtr.valueFirstUse value →
    value = (use.get ctx useInBounds).value := by
  grind [ValuePtr.DefUse, Array.getElem?_of_mem]

@[grind .]
theorem ValuePtr.DefUse_back_value_nextUse_eq
    (ctx : IRContext) (array : Array OpOperandPtr)
    (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (hWF : (use.get ctx useInBounds).value.DefUse ctx array) nextUse :
    (use.get ctx useInBounds).back = OpOperandPtrPtr.operandNextUse nextUse →
    ∀ nextUseInBounds, (nextUse.get ctx nextUseInBounds).value = (use.get ctx useInBounds).value := by
  grind [ValuePtr.DefUse, Array.getElem?_of_mem]

theorem OpOperandPtr.removeFromCurrent_DefUse_other_nextUse
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds)
    (useOfValue : (use.get ctx useInBounds).value ≠ value') array array'
    (hWF' : value'.DefUse ctx array)
    (hWF : (use.get ctx useInBounds).value.DefUse ctx array')
    (i : Nat) (iInBounds : i < array.size) useInBounds (_ : array[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (array[i].get! (removeFromCurrent ctx use useInBounds ctxInBounds)).nextUse = array[i + 1]? := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  cases h: (use.get! ctx).back
  case operandNextUse nextUse =>
    simp only [OpOperandPtrPtr.operandNextUse.injEq]
    have : (use.get ctx (by grind)).back.InBounds ctx := by grind
    have : nextUse.InBounds ctx := by grind
    have : (nextUse.get ctx (by grind)).value = (use.get ctx (by grind)).value := by grind [ValuePtr.DefUse]
    split <;> grind [ValuePtr.DefUse, Array.getElem?_of_mem]
  case valueFirstUse val =>
    simp only [reduceCtorEq, ↓reduceIte]
    grind [ValuePtr.DefUse, Array.getElem?_of_mem]


theorem OpOperandPtr.removeFromCurrent_DefUse_other
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) (value': ValuePtr)
    (useOfValue : (use.get! ctx).value ≠ value') array array' :
    value'.DefUse ctx array →
    (use.get! ctx).value.DefUse ctx array' →
    value'.DefUse (use.removeFromCurrent ctx (by grind) (by grind)) array := by
  intros hWF hWF'
  constructor
  case firstUseBack =>
    intros firstUse heq
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse (array := array) (array' := array') (missingUses := ∅)] at heq
    · rw [OpOperandPtr.OpOperandPtr_get_removeFromCurrent_different_value (array := array')] <;> grind [ValuePtr.DefUse]
    · grind
    · grind
  case arrayInBounds => grind [ValuePtr.DefUse]
  case firstElem =>
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse (array := array) (array' := array') (missingUses := ∅)]
    · have : value'.getFirstUse ctx (by grind) ≠ some use := by grind [ValuePtr.DefUse]
      grind [ValuePtr.DefUse]
    · grind
    · grind
  case allUsesInChain => grind [ValuePtr.DefUse]
  case useValue => grind [ValuePtr.DefUse]
  case prevNextUse =>
    intros
    apply OpOperandPtr.removeFromCurrent_DefUse_other_back (value' := value') (array := array) (array' := array') <;> grind [ValuePtr.DefUse]
  case nextElems =>
    intros
    apply OpOperandPtr.removeFromCurrent_DefUse_other_nextUse (value' := value') (array := array) (array' := array') <;> grind [ValuePtr.DefUse]
  all_goals grind

-- value.DefUse (use.setValue ... ⋯ value') (array.erase use) ⋯

theorem OpOperandPtr.setValue_DefUse_append
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx) (value value': ValuePtr)
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ value') array :
    use ∈ missingUses →
    value.DefUse ctx array missingUses →
    value.DefUse (use.setValue ctx value') array (missingUses.erase use) := by
  intros useNotMissing hWF
  constructor <;> grind [ValuePtr.DefUse]

theorem OpOperandPtr.setValue_DefUse_other
    (ctx : IRContext) (use : OpOperandPtr) (useInBounds : use.InBounds ctx) (value : ValuePtr)
    (useOfOtherValue' : (use.get ctx useInBounds).value ≠ value')
    (valueNe : value ≠ value') array :
    value'.DefUse ctx array missingUses →
    value'.DefUse (use.setValue ctx value) array missingUses := by
  intro hWF
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem ValuePtr.DefUse_array_mem_erase
    (hWF : ValuePtr.DefUse value ctx array valueInBounds) :
    use ∉ array.erase use := by
  intros hcontra
  have := Array.Mem.val hcontra
  simp only [Array.toList_erase] at this
  grind [ValuePtr.DefUse_array_toList_Nodup]

end Veir
