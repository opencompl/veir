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

/- OpOperandPtr.removeFromCurrent -/

theorem OpOperandPtr.back!_array_getElem_removeFromCurrent_eq_of_DefUse
    (useOfValue : (OpOperandPtr.get! use ctx).value = value)
    (hWF : value.DefUse ctx array missingUses) (useInArray: use ∈ array)
    {i} (iPos : i > 0) (iInBounds : i < (array.erase use).size)
    (iInBounds' : (array.erase use)[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (((array.erase use)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds)).back = OpOperandPtrPtr.operandNextUse (array.erase use)[i - 1] := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  subst use
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
        grind [ValuePtr.DefUse.erase_getElem_array_eq_eraseIdx]
  have hNextUse : (array[useIdx].get! ctx).nextUse = array[useIdx + 1]? := by grind [ValuePtr.DefUse]
  simp only [hNextUse]
  by_cases i = useIdx
  · subst useIdx
    split <;> grind [ValuePtr.DefUse, Array.getElem?_eraseIdx_of_ge]
  · by_cases i < useIdx <;> grind [ValuePtr.DefUse, ValuePtr.DefUse_array_injective]

theorem OpOperandPtr.nextUse!_array_getElem_removeFromCurrent_eq_of_DefUse
    (useInBounds : OpOperandPtr.InBounds use ctx)
    (useOfValue : (use.get! ctx).value = value)
    (hWF : value.DefUse ctx array missingUses) (useInArray: use ∈ array)
    {i} (iInBounds : i < (array.erase use).size)
    (iInBounds' : (array.erase use)[i].InBounds (removeFromCurrent ctx use useInBounds ctxInBounds)) :
    (((array.erase use)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds)).nextUse = (array.erase use)[i + 1]? := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  have useInArray : use ∈ array := by grind [ValuePtr.DefUse]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  subst use
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
    grind [ValuePtr.DefUse.erase_getElem_array_eq_eraseIdx]
  have hNextUse : (array[useIdx].get! ctx).nextUse = array[useIdx + 1]? := by
    grind [ValuePtr.DefUse]
  simp only [hNextUse]
  by_cases i < useIdx <;> grind [ValuePtr.DefUse, ValuePtr.DefUse_array_injective]

theorem OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse
    {valuePtr : ValuePtr}
    (valuePtrWF : valuePtr.DefUse ctx array missingUses)
    (operandValueWF : (operandPtr.get! ctx).value.DefUse ctx array' missingUses')
    (operandInArray : operandPtr ∈ array') :
    valuePtr.getFirstUse! (OpOperandPtr.removeFromCurrent ctx operandPtr operandPtrInBounds ctxInBounds) =
      if valuePtr.getFirstUse! ctx = some operandPtr then
        (operandPtr.get! ctx).nextUse
      else
        valuePtr.getFirstUse! ctx := by
  simp only [ValuePtr.getFirstUse!_OpOperandPtr_removeFromCurrent]
  congr 1
  simp [ValuePtr.DefUse_getFirstUse!_eq_iff_back_eq_valueFirstUse operandValueWF (by grind) valuePtrWF]

theorem ValuePtr.DefUse.getElem?_zero_erase_array_eq
    (useInBounds : OpOperandPtr.InBounds use ctx)
    (hWF : ValuePtr.DefUse value ctx array missingUses) (useInArray: use ∈ array)
    {i} (iInBounds : i < (array.erase use).size) :
    (array.erase use)[0]? = value.getFirstUse! (use.removeFromCurrent ctx useInBounds ctxInBounds) := by
  grind [Array.getElem_of_mem, ValuePtr.DefUse, ValuePtr.DefUse.erase_getElem_array_eq_eraseIdx]

theorem ValuePtr.defUse_removeFromCurrent_self
    {value : ValuePtr} {hvalue : use ∈ array}
    (hWF: value.DefUse ctx array missingUses) :
    value.DefUse (use.removeFromCurrent ctx (by grind) ctxInBounds) (array.erase use) (missingUses.insert use) := by
  have hUseValue : (use.get! ctx).value = value := by grind [ValuePtr.DefUse.useValue]
  constructor
  case prevNextUse =>
    grind [OpOperandPtr.back!_array_getElem_removeFromCurrent_eq_of_DefUse, Array.mem_of_mem_erase, ValuePtr.DefUse]
  case nextElems =>
    grind [OpOperandPtr.nextUse!_array_getElem_removeFromCurrent_eq_of_DefUse, Array.mem_of_mem_erase, ValuePtr.DefUse]
  case firstElem =>
    grind [ValuePtr.DefUse.getElem?_zero_erase_array_eq, Array.mem_of_mem_erase, ValuePtr.DefUse]
  case firstUseBack =>
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse hWF (by simp [hUseValue]; exact hWF) (by grind)]
    intros firstUse
    split
    · grind [ValuePtr.DefUse]
    · simp [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
      intros heq
      simp only [ValuePtr.DefUse.nextUse!_ne_of_getFirstUse!_eq hWF hvalue
            (by simp [hUseValue]; exact hWF) heq,
        ↓reduceIte]
      grind [ValuePtr.DefUse]
  case allUsesInChain =>
    intros use' use'InBounds hvalue'
    by_cases h: use = use' <;> grind [ValuePtr.DefUse]
  all_goals grind [ValuePtr.DefUse]

theorem ValuePtr.defUse_removeFromCurrent_other
    {value value' : ValuePtr} (valueNe : value ≠ value') {hvalue : use ∈ array'}
    (hWF : value.DefUse ctx array missingUses)
    (hWF' : value'.DefUse ctx array' missingUses') :
    value.DefUse (use.removeFromCurrent ctx (by grind) ctxInBounds) array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> try grind [ValuePtr.DefUse]
  · simp [ValuePtr.getFirstUse!_OpOperandPtr_removeFromCurrent]
    intros h
    have : (use.get! ctx).value = value' := by grind [ValuePtr.DefUse]
    grind [ValuePtr.DefUse.value!_eq_of_back!_eq_valueFirstUse]

theorem BlockPtr.defUse_OpOperandPtr_removeFromCurrent
    {block : BlockPtr} {blockInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : block.DefUse ctx array blockInBounds) :
    block.DefUse (use.removeFromCurrent ctx useInBounds ctxInBounds) array (by grind) := by
  apply BlockPtr.DefUse_unchanged (ctx := ctx) <;> grind

theorem BlockPtr.operationChainWellFormed_OpOperandPtr_removeFromCurrent
    {block : BlockPtr} {blockInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : block.OperationChainWellFormed ctx array blockInBounds) :
    block.OperationChainWellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds) array (by grind) := by
  apply BlockPtr.OperationChainWellFormed_unchanged (ctx := ctx) <;> grind

theorem RegionPtr.blockChainWellFormed_OpOperandPtr_removeFromCurrent
    {region : RegionPtr} {regionInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : region.BlockChainWellFormed ctx array regionInBounds) :
    region.BlockChainWellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds) array (by grind) := by
  apply RegionPtr.BlockChainWellFormed_unchanged (ctx := ctx) <;> grind

theorem Operation.wellFormed_OpOperandPtr_removeFromCurrent
    {opPtr : OperationPtr} {opInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : (opPtr.get! ctx).WellFormed ctx opPtr opInBounds) :
    (opPtr.get! (use.removeFromCurrent ctx useInBounds ctxInBounds)).WellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds) opPtr (by grind) := by
  apply Operation.WellFormed_unchanged (ctx := ctx) <;> grind

theorem Block.wellFormed_OpOperandPtr_removeFromCurrent
    {blockPtr : BlockPtr} {blockInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : (blockPtr.get! ctx).WellFormed ctx blockPtr blockInBounds) :
    (blockPtr.get! (use.removeFromCurrent ctx useInBounds ctxInBounds)).WellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds) blockPtr (by grind) := by
  apply Block.WellFormed_unchanged (ctx := ctx) <;> grind

theorem Region.wellFormed_OpOperandPtr_removeFromCurrent
    {regionPtr : RegionPtr} (regionInBounds : regionPtr.InBounds ctx) {use : OpOperandPtr} {useInBounds}
    (hWF : (RegionPtr.get! regionPtr ctx).WellFormed ctx regionPtr) :
    (RegionPtr.get! regionPtr (use.removeFromCurrent ctx useInBounds ctxInBounds)).WellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds) regionPtr := by
  apply Region.WellFormed_unchanged (ctx := ctx) <;> grind

end Veir
