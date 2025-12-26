import Veir.IR.Basic
import Veir.Rewriter.InsertPoint
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
    {block : BlockPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : block.DefUse ctx array missingUses) :
    block.DefUse (use.insertIntoCurrent ctx useInBounds ctxInBounds) array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem BlockPtr.opChain_OpOperandPtr_insertIntoCurrent
    {block : BlockPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : block.OpChain ctx array) :
    block.OpChain (use.insertIntoCurrent ctx useInBounds ctxInBounds) array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

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
    {block : BlockPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : block.DefUse ctx array missingUses) :
    block.DefUse (use.removeFromCurrent ctx useInBounds ctxInBounds) array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem BlockPtr.opChain_OpOperandPtr_removeFromCurrent
    {block : BlockPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : block.OpChain ctx array) :
    block.OpChain (use.removeFromCurrent ctx useInBounds ctxInBounds) array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

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

section OperationPtr.linkBetweenWithParent

variable {op : OperationPtr}

theorem ValuePtr.defUse_OperationPtr_linkBetweenWithParent
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    ValuePtr.DefUse value ctx array missingUses →
    ValuePtr.DefUse value newCtx array missingUses := by
  intros
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem BlockPtr.defUse_OperationPtr_linkBetweenWithParent
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    BlockPtr.DefUse block ctx array missingUses →
    BlockPtr.DefUse block newCtx array missingUses := by
  intros
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind

set_option maxHeartbeats 400000 in
theorem BlockPtr.opChain_OperationPtr_linkBetweenWithParent_self
    (ctxWf : ctx.WellFormed)
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp block selfIn prevIn nextIn parentIn = some newCtx)
    (ip : InsertPoint)
    (ipInBounds : ip.InBounds ctx)
    (ipBlock : ip.block! ctx = block)
    (ipNext : ip.next = nextOp)
    (ipPrev : ip.prev! ctx = prevOp)
    (hOpChain : BlockPtr.OpChain block ctx array) :
    BlockPtr.OpChain block newCtx (array.insertIdx (ip.idxIn ctx block (by grind) (by grind) ctxWf) op (by apply InsertPoint.idxIn.le_size_array; grind)) := by
  constructor
  case blockInBounds => grind
  case arrayInBounds => grind [Array.mem_insertIdx, BlockPtr.OpChain]
  case missingOpInBounds => grind
  case opParent => grind [Array.mem_insertIdx, BlockPtr.OpChain]
  case missingOpValue => grind
  case allOpsInChain => grind [Array.mem_insertIdx, BlockPtr.OpChain]
  case first =>
    grind [InsertPoint.idxIn_InsertPoint_prev_none, BlockPtr.OpChain]
  case last =>
    simp only [Array.size_insertIdx, Nat.add_one_sub_one, Nat.lt_add_one, getElem?_pos]
    grind [InsertPoint.next_eq_none_iff_idxIn_eq_size_array, BlockPtr.OpChain]
  case prevFirst =>
    grind [BlockPtr.OpChain]
  case prev =>
    intro i hi₁ hi₂
    let idx := ip.idxIn ctx block (by grind) (by grind) ctxWf
    have : nextOp = array[idx]? := by grind
    by_cases h₁ : i < idx
    · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
    · by_cases h₂ : i = idx
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
      · by_cases h₃ : i - 1 = idx
        · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
        · simp only [Array.size_insertIdx] at hi₂
          simp (disch := grind) only [Array.getElem_insertIdx_of_gt]
          grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
  case next =>
    intro i hi
    simp only [Array.size_insertIdx] at hi
    let idx := ip.idxIn ctx block (by grind) (by grind) ctxWf
    have : nextOp = array[idx]? := by grind
    by_cases h₁ : i + 1 < idx
    · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
    · by_cases h₂ : i + 1 = idx
      · have := @InsertPoint.prev!_eq_GetElem!_idxIn
        grind
      · by_cases h₃ : i = idx
        · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
        · have : i > idx := by grind
          cases hidx : idx <;> grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]


theorem BlockPtr.opChain_OperationPtr_linkBetweenWithParent_other
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp block selfIn prevIn nextIn parentIn = some newCtx)
    (prevParent : prevOp.maybe₁ (fun prev => (prev.get! ctx).parent = some block) )
    (nextParent : nextOp.maybe₁ (fun next => (next.get! ctx).parent = some block) )
    (hNeBlock : block ≠ block') :
    BlockPtr.OpChain block' ctx array →
    BlockPtr.OpChain block' newCtx array := by
  intros opChain
  apply BlockPtr.OpChain_unchanged (ctx := ctx)
    <;> grind [InsertPoint.prev.maybe₁_parent, Option.maybe₁_def]

theorem RegionPtr.blockChainWellFormed_OperationPtr_linkBetweenWithParent
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    RegionPtr.BlockChainWellFormed region ctx array regionInBounds →
    RegionPtr.BlockChainWellFormed region newCtx array (by grind) := by
  intros
  apply RegionPtr.BlockChainWellFormed_unchanged (ctx := ctx) <;> grind

theorem Operation.wellFormed_OperationPtr_linkBetweenWithParent
    (ctxInBounds: IRContext.FieldsInBounds ctx)
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    (OperationPtr.get! opPtr ctx).WellFormed ctx opPtr opInBounds →
    (OperationPtr.get! opPtr newCtx).WellFormed newCtx opPtr (by grind) := by
  intros
  apply Operation.WellFormed_unchanged (ctx := ctx) <;> grind

theorem Block.wellFormed_OperationPtr_linkBetweenWithParent
    (ctxInBounds: IRContext.FieldsInBounds ctx)
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    (BlockPtr.get! blockPtr ctx).WellFormed ctx blockPtr blockInBounds →
    (BlockPtr.get! blockPtr newCtx).WellFormed newCtx blockPtr (by grind) := by
  intros
  apply Block.WellFormed_unchanged (ctx := ctx) <;> grind

theorem Region.wellFormed_OperationPtr_linkBetweenWithParent
    (ctxInBounds: IRContext.FieldsInBounds ctx) (regionInBounds : regionPtr.InBounds ctx)
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    (RegionPtr.get! regionPtr ctx).WellFormed ctx regionPtr →
    (RegionPtr.get! regionPtr newCtx).WellFormed newCtx regionPtr := by
  intros
  apply Region.WellFormed_unchanged (ctx := ctx) <;> grind

end OperationPtr.linkBetweenWithParent

end Veir
