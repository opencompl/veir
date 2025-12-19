import Veir.IR.Basic
import Veir.IR.Grind
import Veir.ForLean
import Std.Data.ExtHashSet

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
  grind [ValuePtr.DefUse, Array.getElem?_of_mem]

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
  induction i <;> grind (splits := 20) [ValuePtr.DefUse]

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

theorem ValuePtr.DefUse.OpOperandPtr_setValue_of_defUseMissingLink
    {use : OpOperandPtr} (useInBounds : use.InBounds ctx)
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ value) :
    value.DefUse ctx array missingUses →
    value.DefUse (use.setValue ctx value) array (missingUses.insert use) := by
  intros hWF
  constructor <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse.OpOperandPtr_setValue_of_defUse
    {use : OpOperandPtr} (useInBounds : use.InBounds ctx)
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ value) :
    value.DefUse ctx array missingUses →
    value.DefUse (use.setValue ctx value) array (missingUses.insert use) := by
  intros hWF
  constructor <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse.OpOperandPtr_setValue_of_defUse_empty
    {use : OpOperandPtr} (useInBounds : use.InBounds ctx)
    (useOfOtherValue : (use.get ctx useInBounds).value ≠ value) :
    value.DefUse ctx array →
    value.DefUse (use.setValue ctx value) array (Std.ExtHashSet.ofList [use]) := by
  intros hWF
  constructor <;> grind [ValuePtr.DefUse]

structure BlockPtr.DefUse (blockPtr : BlockPtr) (ctx : IRContext) (array : Array BlockOperandPtr)
    (hbl : blockPtr.InBounds ctx := by grind) : Prop where
  arrayInBounds (h : use ∈ array) : use.InBounds ctx
  firstElem : array[0]? = (blockPtr.get! ctx).firstUse
  nextElems (hi : i < array.size) : ((array[i]'(by grind)).get! ctx).nextUse = array[i + 1]?
  useValue use (hu : use ∈ array) : (use.get! ctx).value = blockPtr
  firstUseBack (heq : (blockPtr.get! ctx).firstUse = some firstUse) :
    (firstUse.get! ctx).back = BlockOperandPtrPtr.blockFirstUse blockPtr
  backNextUse i (iInBounds : i > 0 ∧ i < array.size) :
    (array[i].get! ctx).back = BlockOperandPtrPtr.blockOperandNextUse array[i - 1]
  allUsesInChain (use : BlockOperandPtr) (useInBounds : use.InBounds ctx) :
    (use.get! ctx).value = blockPtr → use ∈ array

structure BlockPtr.OperationChainWellFormed (block : BlockPtr) (ctx : IRContext) (array : Array OperationPtr) (hb : block.InBounds ctx) : Prop where
  arrayInBounds (h : op ∈ array) : op.InBounds ctx
  opParent (h : op ∈ array) : (op.get! ctx).parent = some block
  first : (block.get! ctx).firstOp = array[0]?
  last : (block.get! ctx).lastOp = array[array.size-1]?
  prevFirst (h : (block.get! ctx).firstOp = some firstOp) :
    (firstOp.get! ctx).prev = none
  prev i (h₁: i > 0) (h₂ : i < array.size) :
    (array[i].get! ctx).prev = some array[i - 1]
  next (hi : i < array.size) :
    (array[i].get! ctx).next = array[i + 1]?
  allOpsInChain (op : OperationPtr) (opInBounds : op.InBounds ctx) :
    (op.get ctx).parent = some block → op ∈ array

theorem BlockPtr.OperationChainWellFormed_unique :
    BlockPtr.OperationChainWellFormed block ctx array hctx →
    BlockPtr.OperationChainWellFormed block ctx array' hctx →
    array = array' := by
  intros hWf hWf'
  apply Array.ext_getElem?
  intros i
  induction i <;> grind [BlockPtr.OperationChainWellFormed]

structure RegionPtr.BlockChainWellFormed (region : RegionPtr) (ctx : IRContext) (array : Array BlockPtr) (hb : region.InBounds ctx) : Prop where
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

-- TODO: weird to have op and opPtr
structure Operation.WellFormed (op : Operation) (ctx : IRContext) (opPtr : OperationPtr) hop : Prop where
  inBounds : Operation.FieldsInBounds opPtr ctx hop
  result_index i (iInBounds : i < opPtr.getNumResults! ctx) : ((opPtr.getResult i).get! ctx).index = i
  operand_owner i (iInBounds : i < opPtr.getNumOperands! ctx) : ((opPtr.getOpOperand i).get! ctx).owner = opPtr
  blockOperand_owner i (iInBounds : i < opPtr.getNumSuccessors! ctx) : ((opPtr.getBlockOperand i).get! ctx).owner = opPtr
  regions_unique i (iInBounds : i < opPtr.getNumRegions! ctx) j (jInBounds : j < opPtr.getNumRegions! ctx) :
    i ≠ j → opPtr.getRegion ctx i ≠ opPtr.getRegion ctx j
  region_parent region (regionInBounds : region.InBounds ctx) :
    (∃ i, i < opPtr.getNumRegions! ctx ∧ opPtr.getRegion! ctx i = region) ↔
    (region.get! ctx).parent = some opPtr

structure Block.WellFormed (block : Block) (ctx : IRContext) (blockPtr : BlockPtr) hbl : Prop where
  inBounds : Block.FieldsInBounds blockPtr ctx hbl
  argument i (iInBounds : i < blockPtr.getNumArguments! ctx) : ((blockPtr.getArgument i).get! ctx).index = i
  argument_owners i (iInBounds : i < blockPtr.getNumArguments! ctx) : ((blockPtr.getArgument i).get! ctx).owner = blockPtr

structure Region.WellFormed (region : Region) (ctx : IRContext) (regionPtr : RegionPtr) where
  inBounds : region.FieldsInBounds ctx
  parent_op {op} (heq : region.parent = some op) : ∃ i, i < op.getNumRegions! ctx → op.getRegion! ctx i = regionPtr

structure IRContext.WellFormed (ctx : IRContext) : Prop where
  inBounds : ctx.FieldsInBounds
  valueDefUseChains (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∃ array, ValuePtr.DefUse valuePtr ctx array
  blockDefUseChains (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    ∃ array, BlockPtr.DefUse blockPtr ctx array
  opChain (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    ∃ array, BlockPtr.OperationChainWellFormed blockPtr ctx array (by grind)
  blockChain (regionPtr : RegionPtr) (regionPtrInBounds : regionPtr.InBounds ctx) :
    ∃ array, RegionPtr.BlockChainWellFormed regionPtr ctx array (by grind)
  operations (opPtr : OperationPtr) (opPtrInBounds : opPtr.InBounds ctx) :
    (opPtr.get! ctx).WellFormed ctx opPtr opPtrInBounds
  blocks (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    (blockPtr.get! ctx).WellFormed ctx blockPtr blockPtrInBounds
  regions (regionPtr : RegionPtr) (regionPtrInBounds : regionPtr.InBounds ctx) :
    (regionPtr.get! ctx).WellFormed ctx regionPtr

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

theorem BlockPtr.DefUse_unchanged
    (hWf : blockPtr.DefUse ctx array valuePtrInBounds)
    (valuePtrInBounds' : blockPtr.InBounds ctx')
    (hSameFirstUse : (blockPtr.get! ctx).firstUse = (blockPtr.get! ctx').firstUse)
    (hSameUseFields : ∀ {usePtr : BlockOperandPtr},
      usePtr.InBounds ctx →
      (usePtr.get! ctx).value = blockPtr →
      usePtr.InBounds ctx' ∧ (usePtr.get! ctx') = (usePtr.get! ctx))
    (hSameUseFields' : ∀ {usePtr : BlockOperandPtr},
      usePtr.InBounds ctx' →
      (usePtr.get! ctx').value = blockPtr →
      usePtr.InBounds ctx ∧ (usePtr.get! ctx) = (usePtr.get! ctx')) :
    blockPtr.DefUse ctx' array := by
  constructor <;> grind [BlockPtr.DefUse]

theorem BlockPtr.OperationChainWellFormed_unchanged
    (hWf : blockPtr.OperationChainWellFormed ctx array blockPtrInBounds)
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
    blockPtr.OperationChainWellFormed ctx' array blockPtrInBounds' := by
  constructor <;> grind [BlockPtr.OperationChainWellFormed]

theorem BlockPtr.OperationChainWellFormed_array_injective
    (hWF : BlockPtr.OperationChainWellFormed block ctx array hblock) :
    ∀ (i j : Nat) iInBounds jInBounds, i ≠ j → array[i]'iInBounds ≠ array[j]'jInBounds := by
  intros i
  induction i <;> grind (splits := 30) [BlockPtr.OperationChainWellFormed]

theorem BlockPtr.OperationChainWellFormed_array_toList_Nodup
    (hWF : BlockPtr.OperationChainWellFormed block ctx array hblock) :
    array.toList.Nodup := by
  simp only [List.nodup_iff_pairwise_ne]
  simp only [List.pairwise_iff_getElem]
  grind [BlockPtr.OperationChainWellFormed_array_injective]

theorem RegionPtr.BlockChainWellFormed_unchanged
    (hWf : regionPtr.BlockChainWellFormed ctx array regionPtrInBounds)
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
    regionPtr.BlockChainWellFormed ctx' array regionPtrInBounds' := by
  constructor <;> grind [RegionPtr.BlockChainWellFormed]

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
  constructor <;> grind [Operation.WellFormed]

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
    BlockPtr.OperationChainWellFormed block ctx (BlockPtr.operationList block ctx hctx hblock) hblock :=
  Exists.choose_spec (hctx.opChain block hblock)

@[grind =]
theorem BlockPtr.operationList_iff_BlockPtr_OperationChainWellFormed :
    BlockPtr.OperationChainWellFormed block ctx array hblock ↔
    BlockPtr.operationList block ctx hctx hblock = array := by
  grind [BlockPtr.operationListWF, BlockPtr.OperationChainWellFormed_unique]

noncomputable def ValuePtr.defUseArray (value : ValuePtr) (ctx : IRContext) (hctx : ctx.WellFormed) (hvalue : value.InBounds ctx) : Array OpOperandPtr :=
  (hctx.valueDefUseChains value hvalue).choose

@[grind .]
theorem ValuePtr.defUseArrayWF {hctx : IRContext.WellFormed ctx} :
    ValuePtr.DefUse value ctx (ValuePtr.defUseArray value ctx hctx hvalue) :=
  Exists.choose_spec (hctx.valueDefUseChains value hvalue)

theorem ValuePtr.defUseArray_contains_operand_use :
    (operand.get ctx operandInBounds).value = value ↔
    operand ∈ ValuePtr.defUseArray value ctx hctx hvalue := by
  grind [ValuePtr.DefUse, ValuePtr.defUseArrayWF]

theorem OperationPtr.getParent_prev_eq
    (opInBounds : OperationPtr.InBounds opPtr ctx)
    (hopParent : (OperationPtr.get! opPtr ctx).parent = some block)
    (hblock : BlockPtr.OperationChainWellFormed block ctx array hblock)
    (hprev : (OperationPtr.get! opPtr ctx).prev = some prevOp) :
    (prevOp.get! ctx).parent = some block := by
  grind (splits := 20) [BlockPtr.OperationChainWellFormed, Array.getElem?_of_mem]

theorem BlockPtr.OperationChainWellFormed_prev_ne
    (hop : OperationPtr.InBounds op ctx)
    (hctx : ctx.WellFormed)
    (hparent : (op.get! ctx).parent = some block) :
    block.OperationChainWellFormed ctx array (by grind [IRContext.WellFormed]) →
    (op.get! ctx).prev ≠ some op := by
  intros hNe
  have := hctx.inBounds
  have ⟨array, harray⟩ := hctx.opChain block (by grind)
  have : op ∈ array := by grind [BlockPtr.OperationChainWellFormed.allOpsInChain]
  intro heq
  have ⟨i, hi⟩ := Array.getElem_of_mem this
  have : array[i]'(by grind) = op := by grind
  have : i > 0 := by grind [BlockPtr.OperationChainWellFormed]
  have := harray.prev i (by grind) (by grind)
  have : op = array[i - 1]'(by grind) := by grind
  grind [BlockPtr.OperationChainWellFormed_array_injective]

theorem BlockPtr.OperationChainWellFormed_next_ne
    (hop : OperationPtr.InBounds op ctx) (hctx : ctx.WellFormed)
    (hparent : (op.get ctx hop).parent = some block) :
    block.OperationChainWellFormed ctx array (by grind [IRContext.WellFormed]) →
    (op.get ctx hop).next ≠ some op := by
  intros hNe
  have := hctx.inBounds
  have ⟨array, harray⟩ := hctx.opChain block (by grind)
  have : op ∈ array := by grind [BlockPtr.OperationChainWellFormed.allOpsInChain]
  intro heq
  have ⟨i, hi⟩ := Array.getElem?_of_mem this
  have : array[i + 1]? = some op := by grind [BlockPtr.OperationChainWellFormed]
  grind [BlockPtr.OperationChainWellFormed_array_injective]

end Veir
