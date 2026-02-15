module

public import Veir.IR.Basic
public import Veir.IR.Fields
import Veir.IR.GetSet
import Veir.IR.InBounds
import Veir.IR.Grind
import Veir.ForLean
import Std.Data.ExtHashSet

public section

namespace Veir

/--
  A def-use chain for an SSA value.
  The def-use chain is represented as an ordered array of operands, where
  each operand corresponds to a use of the value. The first element of the
  array is the first use of the value.
  Each operand in the array points to the next use of the value, forming a
  linked list.
-/
structure ValuePtr.DefUse
    (value : ValuePtr) (ctx : IRContext) (array : Array OpOperandPtr)
    (missingUses : Std.ExtHashSet OpOperandPtr := ∅) : Prop where
  valueInBounds : value.InBounds ctx
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

attribute [grind →] ValuePtr.DefUse.valueInBounds
attribute [grind →] ValuePtr.DefUse.missingUsesInBounds
attribute [grind →] ValuePtr.DefUse.arrayInBounds

theorem ValuePtr.DefUse.unchanged
    (hWf : valuePtr.DefUse ctx array missingUses)
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
    valuePtr.DefUse ctx' array missingUses := by
  constructor <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse.ValuePtr_getFirstUse_ne_of_value_ne
    {use use' : OpOperandPtr}
    (valueNe : (use.get! ctx).value ≠ (use'.get! ctx).value)
    (hWF : (use.get! ctx).value.DefUse ctx array missingUses) :
    (use.get! ctx).value.getFirstUse! ctx ≠ some use' := by
  grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse_getFirstUse!_value_eq_of_back_eq_valueFirstUse
    {firstUse : OpOperandPtr} (hFirstUse : firstUse.InBounds ctx)
    (hvalueFirstUse : (firstUse.get! ctx).value.DefUse ctx array)
    (heq : (firstUse.get! ctx).back = .valueFirstUse value') :
    (firstUse.get! ctx).value.getFirstUse! ctx = some firstUse := by
  grind [ValuePtr.DefUse, Array.getElem?_of_mem]

theorem ValuePtr.DefUse.value!_eq_of_back!_eq_valueFirstUse
    {firstUse : OpOperandPtr}
    (hDefUse : (firstUse.get! ctx).value.DefUse ctx array missingUses)
    (hInArray : firstUse ∈ array) :
    (firstUse.get! ctx).back = .valueFirstUse value →
    (firstUse.get! ctx).value = value := by
  have inArray : firstUse ∈ array := by grind [ValuePtr.DefUse]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem inArray
  cases i <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse
    {firstUse : OpOperandPtr}
    (hvalueFirstUse : (firstUse.get! ctx).value.DefUse ctx array missingUses)
    (hInArray : firstUse ∈ array)
    (heq : (firstUse.get! ctx).back = .valueFirstUse value) :
    value.getFirstUse! ctx = some firstUse := by
  have : (firstUse.get! ctx).value = value := by grind [ValuePtr.DefUse.value!_eq_of_back!_eq_valueFirstUse]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem hInArray
  cases i <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse_back_eq_of_getFirstUse
    {firstUse : OpOperandPtr}
    (hvalueFirstUse : value.DefUse ctx array missingUses)
    (h : value.getFirstUse! ctx = some firstUse) :
    (firstUse.get! ctx).back = .valueFirstUse value := by
  have : (firstUse.get! ctx).value = value := by grind [ValuePtr.DefUse]
  grind [ValuePtr.DefUse, Array.getElem?_of_mem]

theorem ValuePtr.DefUse_getFirstUse!_eq_iff_back_eq_valueFirstUse
    {firstUse : OpOperandPtr}
    (hDefUse : (firstUse.get! ctx).value.DefUse ctx array missingUses)
    (hFirstUse : firstUse ∈ array)
    (hDefUse' : value'.DefUse ctx array' missingUses') :
    (firstUse.get! ctx).back = .valueFirstUse value' ↔
    value'.getFirstUse! ctx = some firstUse := by
  constructor
  · grind [ValuePtr.DefUse, ValuePtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse]
  · grind [ValuePtr.DefUse, ValuePtr.DefUse_back_eq_of_getFirstUse]

theorem ValuePtr.DefUse_array_injective
    (hWF : ValuePtr.DefUse value ctx array hvalue) :
    ∀ (i j : Nat) iInBounds jInBounds, i ≠ j →
    array[i]'iInBounds ≠ array[j]'jInBounds := by
  intros i
  induction i
  · grind [ValuePtr.DefUse]
  · rintro (_|⟨_⟩) <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse_array_toList_Nodup
    (hWF : ValuePtr.DefUse value ctx array hvalue) :
    array.toList.Nodup := by
  simp only [List.nodup_iff_pairwise_ne]
  simp only [List.pairwise_iff_getElem]
  grind [ValuePtr.DefUse_array_injective]

@[grind .]
theorem ValuePtr.DefUse.array_mem_erase_self
    (hWF : ValuePtr.DefUse value ctx array hvalue) :
    use ∈ array → use ∉ array.erase use := by
  have := ValuePtr.DefUse_array_toList_Nodup hWF
  rw [← Array.toArray_toList (xs := array)]
  grind [List.Nodup.not_mem_erase]

theorem ValuePtr.DefUse.array_mem_erase_getElem_self
    (hWF : ValuePtr.DefUse value ctx array hvalue) :
    ∀ (i : Nat) (iInBounds : i < array.size),
    array[i] ∉ array.erase array[i] := by
  have := ValuePtr.DefUse_array_toList_Nodup hWF
  rw [← Array.toArray_toList (xs := array)]
  grind [List.Nodup.not_mem_erase]

theorem ValuePtr.DefUse_array_erase_array_index
    (hWF : ValuePtr.DefUse value ctx array hvalue) :
    ∀ (i : Nat) (iInBounds : i < array.size),
    array.idxOf array[i] = i := by
  have := ValuePtr.DefUse_array_toList_Nodup hWF
  rw [← Array.toArray_toList (xs := array)]
  grind  [List.idxOf_getElem]

@[grind .]
theorem ValuePtr.DefUse.erase_getElem_array_eq_eraseIdx :
    ValuePtr.DefUse value ctx array missingUses →
    (array.erase (array[i]'iInBounds)) = array.eraseIdx i iInBounds := by
  grind [Array.erase_eq_eraseIdx_of_idxOf, ValuePtr.DefUse_array_erase_array_index]

@[grind .]
theorem ValuePtr.DefUse.value!_eq_value!_of_nextUse!_eq {use : OpOperandPtr}
    (useInArray : use ∈ array)
    (useDefUse : (use.get! ctx).value.DefUse ctx array missingUses) :
    (use.get! ctx).nextUse = some use' →
    (use.get! ctx).value = (use'.get! ctx).value := by
  intros huse'
  have : use ∈ array := by grind
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  grind [ValuePtr.DefUse]

@[grind .]
theorem ValuePtr.DefUse.value!_eq_value!_of_back!_eq_operandNextUse
    {use : OpOperandPtr}
    (useInArray : use ∈ array)
    (useDefUse : (use.get! ctx).value.DefUse ctx array missingUses) :
    (use.get! ctx).back = .operandNextUse use' →
    (use.get! ctx).value = (use'.get! ctx).value := by
  intros huse'
  have : use ∈ array := by grind
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse.nextUse!_ne_of_getFirstUse!_eq {value : ValuePtr} {use : OpOperandPtr}
    (valueDefUse : ValuePtr.DefUse value ctx array missingUses)
    (useInArray : use ∈ array')
    (useDefUse : (use.get! ctx).value.DefUse ctx array' missingUses') :
    value.getFirstUse! ctx = some firstUse →
    (use.get! ctx).nextUse ≠ some firstUse := by
  intros hFirstUse hNextUse
  have : (use.get! ctx).value = (firstUse.get! ctx).value := by grind
  have : (use.get! ctx).value = value := by grind [ValuePtr.DefUse]
  subst value
  have : firstUse = array[0]'(by grind [ValuePtr.DefUse]) := by grind [ValuePtr.DefUse]
  have ⟨j, jInBounds, hj⟩ := Array.getElem_of_mem useInArray
  grind [ValuePtr.DefUse]

@[grind .]
theorem ValuePtr.DefUse.OpOperandPtr_setValue_self_of_value!_ne_self
    {use : OpOperandPtr} {useInBounds}
    (useOfOtherValue : (use.get! ctx).value ≠ value) :
    value.DefUse ctx array missingUses →
    value.DefUse (use.setValue ctx value useInBounds) array (missingUses.insert use) := by
  intros hWF
  constructor <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
    {use : OpOperandPtr} {useInBounds} (useOfOtherValue : (use.get! ctx).value ≠ value) :
    value.DefUse ctx array →
    value.DefUse (use.setValue ctx value useInBounds) array (Std.ExtHashSet.ofList [use]) := by
  intros hWF
  constructor <;> grind [ValuePtr.DefUse]

@[grind .]
theorem ValuePtr.DefUse.OpOperandPtr_setValue_other_of_mem_missingUses
    {use : OpOperandPtr} {value value' : ValuePtr} {useInBounds}
    (useOfOtherValue : (use.get! ctx).value ≠ value') {array} :
    use ∈ missingUses →
    value.DefUse ctx array missingUses →
    value.DefUse (use.setValue ctx value' useInBounds) array (missingUses.erase use) := by
  intros useNotMissing hWF
  constructor <;> grind [ValuePtr.DefUse]

@[grind .]
theorem ValuePtr.DefUse.OpOperandPtr_setValue_other_empty
    {use : OpOperandPtr} {value value' : ValuePtr} {useInBounds}
    (useOfOtherValue : (use.get! ctx).value ≠ value') {array} :
    value.DefUse ctx array (Std.ExtHashSet.ofList [use]) →
    value.DefUse (use.setValue ctx value' useInBounds) array := by
  intros hWF
  constructor <;> grind [ValuePtr.DefUse]

@[grind .]
theorem ValuePtr.DefUse.OpOperandPtr_setValue_other_of_value_ne
    {ctx : IRContext} {use : OpOperandPtr} {useInBounds} (value : ValuePtr)
    (useOfOtherValue' : (use.get ctx useInBounds).value ≠ value')
    (valueNe : value ≠ value') {array} :
    value'.DefUse ctx array missingUses →
    value'.DefUse (use.setValue ctx value useInBounds) array missingUses := by
  intro hWF
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind

section BlockPtr.DefUse

structure BlockPtr.DefUse (blockPtr : BlockPtr) (ctx : IRContext)
    (array : Array BlockOperandPtr) (missingUses : Std.ExtHashSet BlockOperandPtr := ∅) : Prop where
  blockInBounds : blockPtr.InBounds ctx
  arrayInBounds (h : use ∈ array) : use.InBounds ctx
  firstElem : array[0]? = (blockPtr.get! ctx).firstUse
  nextElems (hi : i < array.size) : ((array[i]'(by grind)).get! ctx).nextUse = array[i + 1]?
  useValue use (hu : use ∈ array) : (use.get! ctx).value = blockPtr
  firstUseBack (heq : (blockPtr.get! ctx).firstUse = some firstUse) :
    (firstUse.get! ctx).back = BlockOperandPtrPtr.blockFirstUse blockPtr
  backNextUse i (iPos : i > 0) (iInBounds : i < array.size) :
    (array[i].get! ctx).back = BlockOperandPtrPtr.blockOperandNextUse array[i - 1]
  allUsesInChain (use : BlockOperandPtr) (useInBounds : use.InBounds ctx) :
    (use.get! ctx).value = blockPtr → (use ∈ array ↔ use ∉ missingUses)
  missingUsesInBounds (hin : use ∈ missingUses) : use.InBounds ctx
  missingUsesValue (hin : use ∈ missingUses) : (use.get! ctx).value = blockPtr

attribute [local grind] BlockPtr.DefUse
attribute [grind →] BlockPtr.DefUse.blockInBounds
attribute [grind →] BlockPtr.DefUse.missingUsesInBounds
attribute [grind →] BlockPtr.DefUse.missingUsesValue
attribute [grind →] BlockPtr.DefUse.arrayInBounds

theorem BlockPtr.DefUse.unchanged
    (hWf : blockPtr.DefUse ctx array missingUses)
    (blockPtrInBounds' : blockPtr.InBounds ctx')
    (hSameFirstUse : (blockPtr.get! ctx).firstUse = (blockPtr.get! ctx').firstUse)
    (hPreservesInBounds : ∀ (usePtr : BlockOperandPtr),
      usePtr.InBounds ctx →
      (usePtr.get! ctx).value = blockPtr → usePtr.InBounds ctx')
    (hSameUseFields : ∀ (usePtr : BlockOperandPtr),
      usePtr.InBounds ctx → (usePtr.get! ctx).value = blockPtr →
      (usePtr.get! ctx') = (usePtr.get! ctx))
    (hPreservesInBounds' : ∀ (usePtr : BlockOperandPtr),
      usePtr.InBounds ctx' →
      (usePtr.get! ctx').value = blockPtr →
      usePtr.InBounds ctx)
    (hSameUseFields' : ∀ (usePtr : BlockOperandPtr),
      usePtr.InBounds ctx' →
      (usePtr.get! ctx').value = blockPtr →
      (usePtr.get! ctx) = (usePtr.get! ctx')) :
    blockPtr.DefUse ctx' array missingUses := by
  constructor <;> grind

theorem BlockPtr.DefUse.getFirstUse_ne_of_value_ne
    {use use' : BlockOperandPtr}
    (valueNe : (use.get! ctx).value ≠ (use'.get! ctx).value)
    (hWF : (use.get! ctx).value.DefUse ctx array missingUses) :
    ((use.get! ctx).value.get! ctx).firstUse ≠ some use' := by
  grind

theorem BlockPtr.DefUse.getFirstUse!_value_eq_of_back_eq_valueFirstUse
    {firstUse : BlockOperandPtr} (hFirstUse : firstUse.InBounds ctx)
    (hvalueFirstUse : (firstUse.get! ctx).value.DefUse ctx array)
    (heq : (firstUse.get! ctx).back = .blockFirstUse block) :
    ((firstUse.get! ctx).value.get! ctx).firstUse = some firstUse := by
  have : firstUse ∈ array := by grind [BlockPtr.DefUse]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind

theorem BlockPtr.DefUse.value!_eq_of_back!_eq_valueFirstUse
    {firstUse : BlockOperandPtr}
    (hDefUse : (firstUse.get! ctx).value.DefUse ctx array missingUses)
    (hInArray : firstUse ∈ array) :
    (firstUse.get! ctx).back = .blockFirstUse block →
    (firstUse.get! ctx).value = block := by
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem hInArray
  cases i <;> grind

theorem BlockPtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse
    {firstUse : BlockOperandPtr}
    (hvalueFirstUse : (firstUse.get! ctx).value.DefUse ctx array missingUses)
    (hInArray : firstUse ∈ array)
    (heq : (firstUse.get! ctx).back = .blockFirstUse block) :
    (block.get! ctx).firstUse = some firstUse := by
  have : (firstUse.get! ctx).value = block := by grind [BlockPtr.DefUse.value!_eq_of_back!_eq_valueFirstUse]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem hInArray
  cases i <;> grind [Array.getElem?_of_mem]

theorem BlockPtr.DefUse_back_eq_of_getFirstUse
    {firstUse : BlockOperandPtr}
    (hvalueFirstUse : block.DefUse ctx array missingUses)
    (h : (block.get! ctx).firstUse = some firstUse) :
    (firstUse.get! ctx).back = .blockFirstUse block := by
  have : (firstUse.get! ctx).value = block := by grind
  grind [Array.getElem?_of_mem]

theorem BlockPtr.DefUse_getFirstUse!_eq_iff_back_eq_valueFirstUse
    {firstUse : BlockOperandPtr}
    (hDefUse : (firstUse.get! ctx).value.DefUse ctx array missingUses)
    (hFirstUse : firstUse ∈ array)
    (hDefUse' : block'.DefUse ctx array' missingUses') :
    (firstUse.get! ctx).back = .blockFirstUse block' ↔
    (block'.get! ctx).firstUse = some firstUse := by
  constructor
  · grind [BlockPtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse]
  · grind [BlockPtr.DefUse_back_eq_of_getFirstUse]

theorem BlockPtr.DefUse_array_injective
    (hWF : BlockPtr.DefUse block ctx array missingUses) :
    ∀ (i j : Nat) iInBounds jInBounds, i ≠ j →
    array[i]'iInBounds ≠ array[j]'jInBounds := by
  intros i
  induction i
  · grind
  · rintro ⟨_|_⟩ <;> grind

theorem BlockPtr.DefUse_array_toList_Nodup
    (hWF : BlockPtr.DefUse block ctx array missingUses) :
    array.toList.Nodup := by
  simp only [List.nodup_iff_pairwise_ne]
  simp only [List.pairwise_iff_getElem]
  grind [DefUse_array_injective]

@[grind .]
theorem BlockPtr.DefUse.array_mem_erase_self
    (hWF : BlockPtr.DefUse value ctx array missingUses) :
    use ∈ array → use ∉ array.erase use := by
  have := DefUse_array_toList_Nodup hWF
  rw [← Array.toArray_toList (xs := array)]
  grind [List.Nodup.not_mem_erase]

theorem BlockPtr.DefUse.array_mem_erase_getElem_self
    (hWF : BlockPtr.DefUse value ctx array missingUses) :
    ∀ (i : Nat) (iInBounds : i < array.size),
    array[i] ∉ array.erase array[i] := by
  have := DefUse_array_toList_Nodup hWF
  rw [← Array.toArray_toList (xs := array)]
  grind [List.Nodup.not_mem_erase]

theorem BlockPtr.DefUse_array_erase_array_index
    (hWF : BlockPtr.DefUse value ctx array hvalue) :
    ∀ (i : Nat) (iInBounds : i < array.size),
    array.idxOf array[i] = i := by
  have := DefUse_array_toList_Nodup hWF
  rw [← Array.toArray_toList (xs := array)]
  grind [List.idxOf_getElem]

@[grind .]
theorem BlockPtr.DefUse.erase_getElem_array_eq_eraseIdx :
    BlockPtr.DefUse value ctx array missingUses →
    (array.erase (array[i]'iInBounds)) = array.eraseIdx i iInBounds := by
  grind [Array.erase_eq_eraseIdx_of_idxOf, BlockPtr.DefUse_array_erase_array_index]

@[grind .]
theorem BlockPtr.DefUse.value!_eq_value!_of_nextUse!_eq {use : BlockOperandPtr}
    (useInArray : use ∈ array)
    (useDefUse : (use.get! ctx).value.DefUse ctx array missingUses) :
    (use.get! ctx).nextUse = some use' →
    (use.get! ctx).value = (use'.get! ctx).value := by
  intros huse'
  have : use ∈ array := by grind
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  grind

@[grind .]
theorem BlockPtr.DefUse.value!_eq_value!_of_back!_eq_operandNextUse
    {use : BlockOperandPtr}
    (useInArray : use ∈ array)
    (useDefUse : (use.get! ctx).value.DefUse ctx array missingUses) :
    (use.get! ctx).back = .blockOperandNextUse use' →
    (use.get! ctx).value = (use'.get! ctx).value := by
  intros huse'
  have : use ∈ array := by grind
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind

theorem BlockPtr.DefUse.nextUse!_ne_of_getFirstUse!_eq {value : BlockPtr} {use : BlockOperandPtr}
    (valueDefUse : BlockPtr.DefUse value ctx array missingUses)
    (useInArray : use ∈ array')
    (useDefUse : (use.get! ctx).value.DefUse ctx array' missingUses') :
    (value.get! ctx).firstUse = some firstUse →
    (use.get! ctx).nextUse ≠ some firstUse := by
  intros hFirstUse hNextUse
  have : (use.get! ctx).value = (firstUse.get! ctx).value := by grind
  have : (use.get! ctx).value = value := by grind
  subst value
  have : firstUse = array[0]'(by grind) := by grind
  have ⟨j, jInBounds, hj⟩ := Array.getElem_of_mem useInArray
  grind

@[grind .]
theorem BlockPtr.DefUse.OpOperandPtr_setValue_self_of_value!_ne_self
    {use : BlockOperandPtr} {useInBounds}
    (useOfOtherValue : (use.get! ctx).value ≠ value) :
    value.DefUse ctx array missingUses →
    value.DefUse (use.setValue ctx value useInBounds) array (missingUses.insert use) := by
  intros hWF
  constructor <;> grind

theorem BlockPtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
    {use : BlockOperandPtr} {useInBounds} (useOfOtherValue : (use.get! ctx).value ≠ value) :
    value.DefUse ctx array →
    value.DefUse (use.setValue ctx value useInBounds) array (Std.ExtHashSet.ofList [use]) := by
  intros hWF
  constructor <;> grind

@[grind .]
theorem BlockPtr.DefUse.OpOperandPtr_setValue_other_of_mem_missingUses
    {use : BlockOperandPtr} {block block' : BlockPtr} {useInBounds}
    (useOfOtherValue : (use.get! ctx).value ≠ block') {array} :
    use ∈ missingUses →
    block.DefUse ctx array missingUses →
    block.DefUse (use.setValue ctx block' useInBounds) array (missingUses.erase use) := by
  intros useNotMissing hWF
  constructor <;> grind

@[grind .]
theorem BlockPtr.DefUse.OpOperandPtr_setValue_other_empty
    {use : BlockOperandPtr} {block block' : BlockPtr} {useInBounds}
    (useOfOtherValue : (use.get! ctx).value ≠ block') {array} :
    block.DefUse ctx array (Std.ExtHashSet.ofList [use]) →
    block.DefUse (use.setValue ctx block' useInBounds) array := by
  intros hWF
  constructor <;> grind

@[grind .]
theorem BlockPtr.DefUse.OpOperandPtr_setValue_other_of_value_ne
    {ctx : IRContext} {use : BlockOperandPtr} {useInBounds} (block : BlockPtr)
    (useOfOtherValue' : (use.get ctx useInBounds).value ≠ block')
    (valueNe : block ≠ block') {array} :
    block'.DefUse ctx array missingUses →
    block'.DefUse (use.setValue ctx block useInBounds) array missingUses := by
  intro hWF
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind

end BlockPtr.DefUse

/--
  An operation chain owned by a block.
  An operation chain is a doubly linked list of operations within a block, where each
  operation points to the next and previous operations in the block. The block itself
  points to the first and last operations in the chain.
  The operation chain is represented as an ordered array of operation pointers, where
  the first element of the array is the first operation in the block, and the last
  element is the last operation in the block.
  Each operation that has the block as its parent must be included in the operation chain,
  unless it is included in the `missingOps` set.
-/
structure BlockPtr.OpChain (block : BlockPtr) (ctx : IRContext) (array : Array OperationPtr)
    (missingOps : Std.ExtHashSet OperationPtr := ∅) : Prop where
  blockInBounds : block.InBounds ctx
  arrayInBounds (h : op ∈ array) : op.InBounds ctx
  missingOpInBounds (hin : op ∈ missingOps) : op.InBounds ctx
  opParent (h : op ∈ array) : (op.get! ctx).parent = some block
  missingOpValue (hin : op ∈ missingOps) : (op.get! ctx).parent = block
  allOpsInChain (op : OperationPtr) (opInBounds : op.InBounds ctx) :
    (op.get! ctx).parent = some block → (op ∈ array ↔ op ∉ missingOps)
  first : (block.get! ctx).firstOp = array[0]?
  last : (block.get! ctx).lastOp = array[array.size-1]?
  prevFirst (h : (block.get! ctx).firstOp = some firstOp) :
    (firstOp.get! ctx).prev = none
  prev i (h₁: i > 0) (h₂ : i < array.size) :
    (array[i].get! ctx).prev = some array[i - 1]
  next (hi : i < array.size) :
    (array[i].get! ctx).next = array[i + 1]?


attribute [grind →] BlockPtr.OpChain.blockInBounds

@[grind .]
theorem BlockPtr.OpChain_unique :
    BlockPtr.OpChain block ctx array →
    BlockPtr.OpChain block ctx array' →
    array = array' := by
  intros hWf hWf'
  apply Array.ext_getElem?
  intros i
  induction i <;> grind [BlockPtr.OpChain]

theorem BlockPtr.OpChain.firstOp_eq_none_iff_lastOp_eq_none :
    BlockPtr.OpChain block ctx array missingOps →
    ((block.get! ctx).firstOp = none ↔ (block.get! ctx).lastOp = none) := by
  grind [BlockPtr.OpChain]

theorem BlockPtr.OpChain.prev!_eq_none_iff_firstOp!_eq_self {op : OperationPtr}
    (hopInBounds : op.InBounds ctx)
    (hchain : BlockPtr.OpChain block ctx array)
    (hop : (op.get! ctx).parent = some block) :
    ((op.get! ctx).prev = none ↔ (block.get! ctx).firstOp = some op) := by
  constructor
  · intro hprev
    have opInArray : op ∈ array := by grind [BlockPtr.OpChain]
    have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem opInArray
    have : i = 0 := by grind [BlockPtr.OpChain]
    grind [BlockPtr.OpChain]
  · grind [BlockPtr.OpChain]

@[grind .]
theorem BlockPtr.OpChain.parent!_firstOp_eq
    (hChain : BlockPtr.OpChain block ctx array missingOps)
    {firstOp : OperationPtr} :
    (block.get! ctx).firstOp = some firstOp →
    (firstOp.get! ctx).parent = some block := by
  grind [BlockPtr.OpChain]

@[grind .]
theorem BlockPtr.OpChain.parent!_lastOp_eq
    (hChain : BlockPtr.OpChain block ctx array missingOps)
    {lastOp : OperationPtr} :
    (block.get! ctx).lastOp = some lastOp →
    (lastOp.get! ctx).parent = some block := by
  grind [BlockPtr.OpChain]

@[grind .]
theorem BlockPtr.OpChain.parent!_prevOp_eq
    {op prevOp : OperationPtr}
    (hChain : BlockPtr.OpChain block ctx array)
    (opInBounds : op.InBounds ctx) :
    (op.get! ctx).parent = some block →
    (op.get! ctx).prev = some prevOp →
    (prevOp.get! ctx).parent = some block := by
  intros hParent hPrev
  have : op ∈ array := by grind [BlockPtr.OpChain]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind [BlockPtr.OpChain]

@[grind .]
theorem BlockPtr.OpChain.parent!_nextOp_eq
    {op nextOp : OperationPtr}
    (hChain : BlockPtr.OpChain block ctx array)
    (opInBounds : op.InBounds ctx) :
    (op.get! ctx).parent = some block →
    (op.get! ctx).next = some nextOp →
    (nextOp.get! ctx).parent = some block := by
  intros hParent hPext
  have : op ∈ array := by grind [BlockPtr.OpChain]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind [BlockPtr.OpChain]

structure RegionPtr.BlockChain (region : RegionPtr) (ctx : IRContext) (array : Array BlockPtr) : Prop where
  inBounds : region.InBounds ctx
  arrayInBounds (h : bl ∈ array) : bl.InBounds ctx
  opParent (h : bl ∈ array) : (bl.get! ctx).parent = some block
  first : (region.get! ctx).firstBlock = array[0]?
  last : (region.get! ctx).lastBlock = array[array.size-1]?
  prevFirst (h : (region.get! ctx).firstBlock = some fbl) :
    (fbl.get! ctx).prev = none
  prev i (h₁: i > 0) (h₂ : i < array.size) :
    (array[i].get! ctx).prev = some array[i - 1]
  next (hi : i < array.size) :
    (array[i].get! ctx).next = array[i + 1]?
  allBlocksInChain (bl : BlockPtr) (blInBoundsl : bl.InBounds ctx) :
    (bl.get! ctx).parent = some region → bl ∈ array

attribute [grind →] RegionPtr.BlockChain.inBounds

-- TODO: weird to have op and opPtr
structure Operation.WellFormed (op : Operation) (ctx : IRContext) (opPtr : OperationPtr) hop : Prop where
  inBounds : Operation.FieldsInBounds opPtr ctx hop
  result_index i (iInBounds : i < opPtr.getNumResults! ctx) : ((opPtr.getResult i).get! ctx).index = i
  result_owner i (iInBounds : i < opPtr.getNumResults! ctx) :
    ((opPtr.getResult i).get! ctx).owner = opPtr
  operand_owner i (iInBounds : i < opPtr.getNumOperands! ctx) : ((opPtr.getOpOperand i).get! ctx).owner = opPtr
  blockOperand_owner i (iInBounds : i < opPtr.getNumSuccessors! ctx) : ((opPtr.getBlockOperand i).get! ctx).owner = opPtr
  regions_unique i (iInBounds : i < opPtr.getNumRegions! ctx) j (jInBounds : j < opPtr.getNumRegions! ctx) :
    i ≠ j → opPtr.getRegion ctx i ≠ opPtr.getRegion ctx j
  region_parent region (regionInBounds : region.InBounds ctx) :
    (∃ i, i < opPtr.getNumRegions! ctx ∧ opPtr.getRegion! ctx i = region) ↔
    (region.get! ctx).parent = some opPtr
  opChain_of_parent_none : (opPtr.get! ctx).parent = none →
    (opPtr.get! ctx).prev = none ∧ (opPtr.get! ctx).next = none

structure Block.WellFormed (block : Block) (ctx : IRContext) (blockPtr : BlockPtr) hbl : Prop where
  inBounds : Block.FieldsInBounds blockPtr ctx hbl
  argument i (iInBounds : i < blockPtr.getNumArguments! ctx) : ((blockPtr.getArgument i).get! ctx).index = i
  argument_owners i (iInBounds : i < blockPtr.getNumArguments! ctx) : ((blockPtr.getArgument i).get! ctx).owner = blockPtr

structure Region.WellFormed (region : Region) (ctx : IRContext) (regionPtr : RegionPtr) where
  inBounds : region.FieldsInBounds ctx
  parent_op {op} (heq : region.parent = some op) : ∃ i, i < op.getNumRegions! ctx → op.getRegion! ctx i = regionPtr

structure IRContext.WellFormed (ctx : IRContext)
  (missingOperandUses : Std.ExtHashSet OpOperandPtr := ∅)
  (missingSuccessorUses : Std.ExtHashSet BlockOperandPtr := ∅) : Prop where
  inBounds : ctx.FieldsInBounds
  valueDefUseChains (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∃ array, ValuePtr.DefUse valuePtr ctx array (missingOperandUses.filter (fun use => (use.get! ctx).value = valuePtr))
  blockDefUseChains (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    ∃ array, BlockPtr.DefUse blockPtr ctx array (missingSuccessorUses.filter (fun use => (use.get! ctx).value = blockPtr))
  opChain (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    ∃ array, BlockPtr.OpChain blockPtr ctx array
  blockChain (regionPtr : RegionPtr) (regionPtrInBounds : regionPtr.InBounds ctx) :
    ∃ array, RegionPtr.BlockChain regionPtr ctx array
  operations (opPtr : OperationPtr) (opPtrInBounds : opPtr.InBounds ctx) :
    (opPtr.get! ctx).WellFormed ctx opPtr opPtrInBounds
  blocks (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    (blockPtr.get! ctx).WellFormed ctx blockPtr blockPtrInBounds
  regions (regionPtr : RegionPtr) (regionPtrInBounds : regionPtr.InBounds ctx) :
    (regionPtr.get! ctx).WellFormed ctx regionPtr

attribute [grind →] IRContext.WellFormed.inBounds

theorem BlockPtr.OpChain_unchanged
    (hWf : blockPtr.OpChain ctx array missingOps)
    (blockPtrInBounds' : blockPtr.InBounds ctx')
    (hSameFirstOp : (blockPtr.get! ctx).firstOp = (blockPtr.get! ctx').firstOp)
    (hSameLastOp : (blockPtr.get! ctx).lastOp = (blockPtr.get! ctx').lastOp)
    (hSameOpFields : ∀ (opPtr : OperationPtr),
      opPtr.InBounds ctx →
      (opPtr.get! ctx).parent = some blockPtr →
        opPtr.InBounds ctx' ∧
        (opPtr.get! ctx').parent = (opPtr.get! ctx).parent ∧
        (opPtr.get! ctx').prev = (opPtr.get! ctx).prev ∧
        (opPtr.get! ctx').next = (opPtr.get! ctx).next)
    (hSameOpFields' : ∀ (opPtr : OperationPtr),
      opPtr.InBounds ctx' →
      (opPtr.get! ctx').parent = some blockPtr →
        opPtr.InBounds ctx ∧
        (opPtr.get! ctx).parent = (opPtr.get! ctx').parent) :
    blockPtr.OpChain ctx' array missingOps := by
  constructor <;> grind [BlockPtr.OpChain]

theorem BlockPtr.OpChain_array_injective
    (hWF : BlockPtr.OpChain block ctx array missingOps) :
    ∀ (i j : Nat) iInBounds jInBounds, i ≠ j → array[i]'iInBounds ≠ array[j]'jInBounds := by
  intros i
  induction i
  case zero => grind [BlockPtr.OpChain]
  case succ i ih =>
    intros j
    cases j
    case zero => grind [BlockPtr.OpChain]
    case succ j =>
      intros iInBounds jInBounds hNe
      grind [BlockPtr.OpChain]

theorem BlockPtr.OpChain_array_toList_Nodup
    (hWF : BlockPtr.OpChain block ctx array missingOps) :
    array.toList.Nodup := by
  simp only [List.nodup_iff_pairwise_ne]
  simp only [List.pairwise_iff_getElem]
  grind [BlockPtr.OpChain_array_injective]

@[grind .]
theorem BlockPtr.OpChain.array_mem_erase
    (hWF : BlockPtr.OpChain block ctx array missingOps) :
    op ∈ array.erase op' ↔ op ∈ array ∧ op ≠ op' := by
  have := BlockPtr.OpChain_array_toList_Nodup hWF
  rw [← Array.toArray_toList (xs := array)]
  grind [List.Nodup.not_mem_erase]

@[grind .]
theorem BlockPtr.OpChain.idxOf_getElem_array
    (hWF : BlockPtr.OpChain block ctx array missingOps) :
    ∀ (i : Nat) (iInBounds : i < array.size),
    array.idxOf array[i] = i := by
  have := BlockPtr.OpChain_array_toList_Nodup hWF
  rw [← Array.toArray_toList (xs := array)]
  grind  [List.idxOf_getElem]

@[grind .]
theorem BlockPtr.OpChain.erase_getElem_array_eq_eraseIdx
    (hWF : BlockPtr.OpChain block ctx array missingOps) :
    (array.erase (array[i]'iInBounds)) = array.eraseIdx i iInBounds := by
  grind [Array.erase_eq_eraseIdx_of_idxOf, BlockPtr.OpChain.idxOf_getElem_array]

theorem RegionPtr.blockChain_unchanged
    (hWf : regionPtr.BlockChain ctx array)
    (regionPtrInBounds' : regionPtr.InBounds ctx')
    (hSameFirst : (regionPtr.get! ctx).firstBlock = (regionPtr.get! ctx').firstBlock)
    (hSameLast : (regionPtr.get! ctx).lastBlock = (regionPtr.get! ctx').lastBlock)
    (hSameBlockFields : ∀ (blockPtr : BlockPtr),
      blockPtr.InBounds ctx →
      (blockPtr.get! ctx).parent = some regionPtr →
        blockPtr.InBounds ctx' ∧
        (blockPtr.get! ctx').parent = (blockPtr.get! ctx).parent ∧
        (blockPtr.get! ctx').prev = (blockPtr.get! ctx).prev ∧
        (blockPtr.get! ctx').next = (blockPtr.get! ctx).next)
    (hSameBlockFields' : ∀ (blockPtr : BlockPtr),
      blockPtr.InBounds ctx' →
      (blockPtr.get! ctx').parent = some regionPtr →
        blockPtr.InBounds ctx ∧
        (blockPtr.get! ctx).parent = (blockPtr.get! ctx').parent) :
    regionPtr.BlockChain ctx' array := by
  constructor <;> grind [RegionPtr.BlockChain]

theorem Operation.WellFormed_unchanged
    (hWf : (opPtr.get ctx opPtrInBounds).WellFormed ctx opPtr opPtrInBounds)
    (hInBounds' : Operation.FieldsInBounds opPtr ctx' opPtrInBounds')
    (hSameNumOperands :
      opPtr.getNumOperands! ctx = opPtr.getNumOperands! ctx')
    (hSameOperandOwner :
      ∀ i, i < opPtr.getNumOperands! ctx →
      ((opPtr.getOpOperand i).get! ctx).owner = ((opPtr.getOpOperand i).get! ctx').owner)
    (hSameNumBlockOperands :
      opPtr.getNumSuccessors! ctx = opPtr.getNumSuccessors! ctx')
    (hSameBlockOperandOwner :
      ∀ i, i < opPtr.getNumSuccessors! ctx →
      ((opPtr.getBlockOperand i).get! ctx).owner = ((opPtr.getBlockOperand i).get! ctx').owner)
    (hSameNumResults :
      opPtr.getNumResults! ctx = opPtr.getNumResults! ctx')
    (hSameResultIndex :
      ∀ i, i < opPtr.getNumResults ctx opPtrInBounds →
      ((opPtr.getResult i).get! ctx).index = ((opPtr.getResult i).get! ctx').index)
    (hSameResultOwner :
      ∀ i, i < opPtr.getNumResults ctx opPtrInBounds →
      ((opPtr.getResult i).get! ctx).owner = ((opPtr.getResult i).get! ctx').owner)
    (hSameParent : (opPtr.get! ctx).parent = (opPtr.get! ctx').parent)
    (hSamePrev : (opPtr.get! ctx).prev = (opPtr.get! ctx').prev)
    (hSameNext : (opPtr.get! ctx).next = (opPtr.get! ctx').next)
    (hSameRegionParents :
      ∀ (regionPtr : RegionPtr), regionPtr.InBounds ctx →
        (regionPtr.get! ctx).parent = some opPtr →
        regionPtr.InBounds ctx' ∧ (regionPtr.get! ctx).parent = (regionPtr.get! ctx').parent)
    (hSameRegionParents' :
      ∀ (regionPtr : RegionPtr), regionPtr.InBounds ctx' →
        (regionPtr.get! ctx').parent = some opPtr →
        regionPtr.InBounds ctx ∧ (regionPtr.get! ctx).parent = (regionPtr.get! ctx').parent)
    (hSameNumRegions :
      opPtr.getNumRegions! ctx = opPtr.getNumRegions! ctx')
    (hSameRegions :
      ∀ i, i < opPtr.getNumRegions! ctx → opPtr.getRegion! ctx i = opPtr.getRegion! ctx' i) :
    (opPtr.get! ctx').WellFormed ctx' opPtr opPtrInBounds' := by
  constructor <;> grind [Operation.WellFormed, Operation.FieldsInBounds]

theorem Block.WellFormed_unchanged
    (hWf : (blockPtr.get! ctx).WellFormed ctx blockPtr blockPtrInBounds)
    (hInBounds' : Block.FieldsInBounds blockPtr ctx' blockPtrInBounds')
    (hSameNumArguments : blockPtr.getNumArguments! ctx = blockPtr.getNumArguments! ctx')
    (hSameArgumentOwner :
      ∀ i, i < blockPtr.getNumArguments! ctx →
      ((blockPtr.getArgument i).get! ctx).owner = ((blockPtr.getArgument i).get! ctx').owner)
    (hSameArgumentIndex :
      ∀ i, i < blockPtr.getNumArguments ctx →
      ((blockPtr.getArgument i).get! ctx).index = ((blockPtr.getArgument i).get! ctx').index) :
    (blockPtr.get! ctx').WellFormed ctx' blockPtr blockPtrInBounds' := by
  constructor <;> grind [Block.WellFormed]

theorem Region.WellFormed_unchanged
    (hWf : (RegionPtr.get! regionPtr ctx).WellFormed ctx regionPtr)
    (hInBounds' : (regionPtr.get! ctx').FieldsInBounds ctx')
    (hSameParentOp : (regionPtr.get! ctx).parent = (regionPtr.get! ctx').parent)
    (hSameNumRegions :
      ∀ parent, (regionPtr.get! ctx).parent = some parent →
      parent.getNumRegions! ctx = parent.getNumRegions! ctx')
    (hSameRegions :
      ∀ parent, (regionPtr.get! ctx).parent = some parent →
      ∀ i, i < parent.getNumRegions! ctx →
      parent.getRegion! ctx i = parent.getRegion! ctx' i) :
    (regionPtr.get! ctx').WellFormed ctx' regionPtr := by
  constructor <;> grind [Region.WellFormed]

noncomputable def BlockPtr.operationList (block : BlockPtr) (ctx : IRContext) (hctx : ctx.WellFormed) (hblock : block.InBounds ctx) : Array OperationPtr :=
  (hctx.opChain block hblock).choose

theorem BlockPtr.operationListWF {hctx : IRContext.WellFormed ctx} :
    BlockPtr.OpChain block ctx (BlockPtr.operationList block ctx hctx hblock) :=
  Exists.choose_spec (hctx.opChain block hblock)

@[grind =]
theorem BlockPtr.operationList_iff_BlockPtr_OpChain :
    BlockPtr.OpChain block ctx array ↔
    BlockPtr.operationList block ctx hctx hblock = array := by
  grind [BlockPtr.operationListWF]

theorem BlockPtr.operationList.mem :
    (op.get ctx opInBounds).parent = some block ↔
    op ∈ BlockPtr.operationList block ctx hctx hblock := by
  grind [BlockPtr.OpChain, BlockPtr.operationListWF]

noncomputable def ValuePtr.defUseArray (value : ValuePtr) (ctx : IRContext) (hctx : ctx.WellFormed missingUses missingBlockUses) (hvalue : value.InBounds ctx) : Array OpOperandPtr :=
  (hctx.valueDefUseChains value hvalue).choose

@[grind .]
theorem ValuePtr.defUseArrayWF {hctx : IRContext.WellFormed ctx missingUses missingBlockUses} :
    ValuePtr.DefUse value ctx (ValuePtr.defUseArray value ctx hctx hvalue) (missingUses.filter (fun use => (use.get! ctx).value = value)) := by
  grind [ValuePtr.defUseArray, IRContext.WellFormed]

theorem ValuePtr.defUseArray_contains_operand_use {hctx : IRContext.WellFormed ctx} :
    (operand.get ctx operandInBounds).value = value ↔
    operand ∈ ValuePtr.defUseArray value ctx hctx hvalue := by
  grind [ValuePtr.DefUse, ValuePtr.defUseArrayWF]

theorem OperationPtr.getParent_prev_eq
    (opInBounds : OperationPtr.InBounds opPtr ctx)
    (hopParent : (OperationPtr.get! opPtr ctx).parent = some block)
    (hblock : BlockPtr.OpChain block ctx array)
    (hprev : (OperationPtr.get! opPtr ctx).prev = some prevOp) :
    (prevOp.get! ctx).parent = some block := by
  grind [BlockPtr.OpChain, Array.getElem?_of_mem]

theorem BlockPtr.OpChain_prev_ne
    (hop : OperationPtr.InBounds op ctx)
    (hctx : ctx.WellFormed)
    (hparent : (op.get! ctx).parent = some block) :
    block.OpChain ctx array →
    (op.get! ctx).prev ≠ some op := by
  intros hNe
  have := hctx.inBounds
  have ⟨array, harray⟩ := hctx.opChain block (by grind)
  have : op ∈ array := by grind [BlockPtr.OpChain]
  intro heq
  have ⟨i, hi⟩ := Array.getElem_of_mem this
  have : array[i]'(by grind) = op := by grind
  have : i > 0 := by grind [BlockPtr.OpChain]
  have := harray.prev i (by grind) (by grind)
  have : op = array[i - 1]'(by grind) := by grind
  grind [BlockPtr.OpChain_array_injective]

theorem BlockPtr.OpChain_next_ne
    (hop : OperationPtr.InBounds op ctx) (hctx : ctx.WellFormed)
    (hparent : (op.get ctx hop).parent = some block) :
    block.OpChain ctx array →
    (op.get ctx hop).next ≠ some op := by
  intros hNe
  have := hctx.inBounds
  have ⟨array, harray⟩ := hctx.opChain block (by grind)
  have : op ∈ array := by grind [BlockPtr.OpChain]
  intro heq
  have ⟨i, hi⟩ := Array.getElem?_of_mem this
  have : array[i + 1]? = some op := by grind [BlockPtr.OpChain]
  grind [BlockPtr.OpChain_array_injective]

theorem ValuePtr.DefUse.hasUses_iff
    (hWF : ValuePtr.DefUse value ctx array missingUses) :
    value.hasUses ctx ↔ array ≠ #[] := by
  grind [DefUse, hasUses_def]

theorem ValuePtr.DefUse.getFirstUse!_none_iff
    (hWF : ValuePtr.DefUse value ctx array missingUses) :
    value.getFirstUse! ctx = none ↔ array = #[] := by
  grind [DefUse]

theorem IRContext.WellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some
    {ctx : IRContext} {op prevOp : OperationPtr} (hop : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    (op.get! ctx).prev = some prevOp →
    (prevOp.get! ctx).next = some op := by
  cases hparent : (op.get! ctx).parent
  case none =>
    grind [IRContext.WellFormed, BlockPtr.OpChain, Operation.WellFormed]
  case some parent =>
    intro hprev
    have ⟨array, harray⟩ := wf.opChain parent (by grind)
    grind [Array.getElem?_of_mem, BlockPtr.OpChain]

theorem IRContext.WellFormed.OperationPtr_prev!_eq_some_of_next!_eq_some
    {ctx : IRContext} {op nextOp : OperationPtr} (hop : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    (op.get! ctx).next = some nextOp →
    (nextOp.get! ctx).prev = some op := by
  cases hparent : (op.get! ctx).parent
  case none =>
    grind [IRContext.WellFormed, BlockPtr.OpChain, Operation.WellFormed]
  case some parent =>
    intro hprev
    have ⟨array, harray⟩ := wf.opChain parent (by grind)
    grind [Array.getElem?_of_mem, BlockPtr.OpChain]

theorem IRContext.WellFormed.OperationPtr_parent!_ne_none_of_next!_ne_none
    {ctx : IRContext} {op : OperationPtr} (hop : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    (op.get! ctx).next ≠ none →
    (op.get! ctx).parent ≠ none := by
  grind [IRContext.WellFormed, Operation.WellFormed]

theorem IRContext.WellFormed.OperationPtr_parent!_ne_none_of_prev!_ne_none
    {ctx : IRContext} {op : OperationPtr} (hop : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    (op.get! ctx).prev ≠ none →
    (op.get! ctx).parent ≠ none := by
  grind [IRContext.WellFormed, Operation.WellFormed]

end Veir
