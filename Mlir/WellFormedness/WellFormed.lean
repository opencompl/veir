import Mlir.Core.Basic
import Mlir.Core.Grind
import Mlir.ForLean

namespace Mlir

structure ValuePtr.WellFormedUseDefChain
    (value : ValuePtr) (ctx : IRContext) (array : Array OpOperandPtr)
    (hvalue : value.InBounds ctx := by grind) : Prop where
  arrayInBounds (h : use ∈ array) : use.InBounds ctx
  firstElem : array[0]? = value.getFirstUse ctx
  firstUseBack (heq : value.getFirstUse ctx = some firstUse) :
    (firstUse.get ctx).back = .valueFirstUse value
  allUsesInChain (use : OpOperandPtr) (huse : use.InBounds ctx) : (use.get ctx).value = value → use ∈ array
  useValue (hin : use ∈ array) : (use.get ctx).value = value
  nextElems (hi : i < array.size) :
    (array[i].get ctx).nextUse = array[i + 1]?
  prevNextUse (iPos : i > 0) (iInBounds : i < array.size) :
    (array[i].get ctx).back = OpOperandPtrPtr.operandNextUse array[i - 1]

theorem ValuePtr.WellFormedUseDefChain_ValuePtr_back_FirstUse
    (ctx: IRContext) (ctxInBounds : ctx.FieldsInBounds)
    (firstUse : OpOperandPtr) hFirstUse array
    (hvalueFirstUse : (firstUse.get ctx hFirstUse).value.WellFormedUseDefChain ctx array (by grind))
    (heq : (firstUse.get ctx hFirstUse).back = .valueFirstUse value') :
    (firstUse.get ctx hFirstUse).value.getFirstUse ctx = some firstUse := by
  grind [ValuePtr.WellFormedUseDefChain, Array.getElem?_of_mem]

theorem ValuePtr.WellFormedUseDefChain_array_injective
    (value : ValuePtr) (ctx : IRContext) (array : Array OpOperandPtr)
    (hvalue : value.InBounds ctx)
    (hWF : value.WellFormedUseDefChain ctx array hvalue) :
    ∀ (i j : Nat) iInBounds jInBounds, i ≠ j → array[i]'iInBounds ≠ array[j]'jInBounds := by
  intros i
  induction i <;> grind (splits := 20) [ValuePtr.WellFormedUseDefChain]

theorem ValuePtr.WellFormedUseDefChain_array_toList_Nodup
    (value : ValuePtr) (ctx : IRContext) (array : Array OpOperandPtr)
    (hvalue : value.InBounds ctx)
    (hWF : value.WellFormedUseDefChain ctx array hvalue) :
    array.toList.Nodup := by
  simp only [List.nodup_iff_pairwise_ne]
  simp only [List.pairwise_iff_getElem]
  grind [ValuePtr.WellFormedUseDefChain_array_injective]

theorem ValuePtr.WellFormedUseDefChain_array_erase_mem_self
    (value : ValuePtr) (ctx : IRContext) (array : Array OpOperandPtr)
    (hvalue : value.InBounds ctx)
    (hWF : value.WellFormedUseDefChain ctx array hvalue) :
    ∀ (i : Nat) (iInBounds : i < array.size),
      array[i] ∉ array.erase array[i] := by
  have := ValuePtr.WellFormedUseDefChain_array_toList_Nodup value ctx array hvalue hWF
  rw [← Array.toArray_toList (xs := array)]
  grind [List.Nodup.not_mem_erase]

theorem ValuePtr.WellFormedUseDefChain_array_erase_array_index
    (value : ValuePtr) (ctx : IRContext) (array : Array OpOperandPtr)
    (hvalue : value.InBounds ctx)
    (hWF : value.WellFormedUseDefChain ctx array hvalue) :
    ∀ (i : Nat) (iInBounds : i < array.size),
      array.idxOf array[i] = i := by
  have := ValuePtr.WellFormedUseDefChain_array_toList_Nodup value ctx array hvalue hWF
  rw [← Array.toArray_toList (xs := array)]
  grind  [List.idxOf_getElem]

structure BlockPtr.WellFormedUseDefChain (blockPtr : BlockPtr) (ctx : IRContext) (array : Array BlockOperandPtr)
    (hbl : blockPtr.InBounds ctx := by grind) : Prop where
  arrayInBounds (h : use ∈ array) : use.InBounds ctx
  firstElem : array[0]? = (blockPtr.get ctx (by grind)).firstUse
  nextElems (hi : i < array.size) : ((array[i]'(by grind)).get ctx (by grind)).nextUse = array[i + 1]?
  useValue use (hu : use ∈ array) : (use.get ctx (by grind)).value = blockPtr
  firstUseBack (heq : (blockPtr.get ctx (by grind)).firstUse = some firstUse) :
    (firstUse.get ctx (by grind)).back = BlockOperandPtrPtr.blockFirstUse blockPtr
  backNextUse i (iInBounds : i > 0 ∧ i < array.size) :
    (array[i].get ctx (by grind)).back = BlockOperandPtrPtr.blockOperandNextUse array[i - 1]
  allUsesInChain (use : BlockOperandPtr) (useInBounds : use.InBounds ctx) :
    (use.get ctx (by grind)).value = blockPtr →
    use ∈ array

structure BlockPtr.OperationChainWellFormed (block : BlockPtr) (ctx : IRContext) (array : Array OperationPtr) (hb : block.InBounds ctx) : Prop where
  arrayInBounds (h : op ∈ array) : op.InBounds ctx
  opParent (h : op ∈ array) : (op.get ctx (by grind)).parent = some block
  first : (block.get ctx (by grind)).firstOp = array[0]?
  last : (block.get ctx (by grind)).lastOp = array[array.size-1]?
  prevFirst (h : (block.get ctx (by grind)).firstOp = some firstOp) :
    (firstOp.get ctx (by grind)).prev = none
  prev i (h₁: i > 0) (h₂ : i < array.size) :
    (array[i].get ctx (by grind)).prev = some array[i - 1]
  next (hi : i < array.size) :
    (array[i].get ctx).next = array[i + 1]?
  allOpsInChain (op : OperationPtr) (opInBounds : op.InBounds ctx) :
    (op.get ctx (by grind)).parent = some block → op ∈ array

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
  opParent (h : bl ∈ array) : (bl.get ctx (by grind)).parent = some block
  first : (region.get ctx (by grind)).firstBlock = array[0]?
  last : (region.get ctx (by grind)).lastBlock = array[array.size-1]?
  prevFirst (h : (region.get ctx (by grind)).firstBlock = some fbl) :
    (fbl.get ctx (by grind)).prev = none
  prev i (h₁: i > 0) (h₂ : i < array.size) :
    (array[i].get ctx).prev = some array[i - 1]
  next (hi : i < array.size) :
    (array[i].get ctx).next = array[i + 1]?
  allBlocksInChain (bl : BlockPtr) (blInBoundsl : bl.InBounds ctx) :
    (bl.get ctx (by grind)).parent = some region → bl ∈ array

-- TODO: weird to have op and opPtr
structure Operation.WellFormed (op : Operation) (ctx : IRContext) (opPtr : OperationPtr) hop : Prop where
  inBounds : Operation.FieldsInBounds opPtr ctx hop
  result_index i (iInBounds : i < opPtr.getNumResults ctx) : ((opPtr.getResult i).get ctx).index = i
  operand_owner i (iInBounds : i < op.operands.size) : op.operands[i].owner = opPtr
  blockOperand_owner i (iInBounds : i < op.blockOperands.size) : op.blockOperands[i].owner = opPtr
  regions_unique i (iInBounds : i < op.regions.size) j (jInBounds : j < op.regions.size) :
    i ≠ j → op.regions[i]'iInBounds ≠ op.regions[j]'jInBounds
  region_parent region regionInBounds :
    (∃ i, ∃ (iInBounds : i < op.regions.size), op.regions[i] = region) ↔
    (region.get ctx regionInBounds).parent = some opPtr

structure Block.WellFormed (block : Block) (ctx : IRContext) (blockPtr : BlockPtr) hbl : Prop where
  inBounds : Block.FieldsInBounds blockPtr ctx hbl
  argument i (iInBounds : i < block.arguments.size) : block.arguments[i].index = i
  argument_owners i (iInBounds : i < block.arguments.size) : block.arguments[i].owner = blockPtr

structure Region.WellFormed (region : Region) (ctx : IRContext) (regionPtr : RegionPtr) where
  inBounds : region.FieldsInBounds ctx
  parent_op (heq : region.parent = some op) : (op.get ctx (by grind)).regions.contains regionPtr

structure IRContext.WellFormed (ctx : IRContext) : Prop where
  inBounds : ctx.FieldsInBounds
  valueUseDefChains (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∃ array, ValuePtr.WellFormedUseDefChain valuePtr ctx array
  blockUseDefChains (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    ∃ array, BlockPtr.WellFormedUseDefChain blockPtr ctx array
  opChain (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    ∃ array, BlockPtr.OperationChainWellFormed blockPtr ctx array (by grind)
  blockChain (regionPtr : RegionPtr) (regionPtrInBounds : regionPtr.InBounds ctx) :
    ∃ array, RegionPtr.BlockChainWellFormed regionPtr ctx array (by grind)
  operations (opPtr : OperationPtr) (opPtrInBounds : opPtr.InBounds ctx) :
    (opPtr.get ctx opPtrInBounds).WellFormed ctx opPtr opPtrInBounds
  blocks (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    (blockPtr.get ctx blockPtrInBounds).WellFormed ctx blockPtr blockPtrInBounds
  regions (regionPtr : RegionPtr) (regionPtrInBounds : regionPtr.InBounds ctx) :
    (regionPtr.get ctx regionPtrInBounds).WellFormed ctx regionPtr

theorem IRContext.ValuePtr_UseDefChainWellFormed_unchanged
    (ctx ctx' : IRContext)
    (valuePtr : ValuePtr)
    (array : Array OpOperandPtr)
    (valuePtrInBounds : valuePtr.InBounds ctx)
    (hWf : valuePtr.WellFormedUseDefChain ctx array  (by grind))
    (valuePtrInBounds' : valuePtr.InBounds ctx')
    (hSameFirstUse : valuePtr.getFirstUse ctx (by grind) = valuePtr.getFirstUse ctx' (by grind))
    (hPreservesInBounds : ∀ (usePtr : OpOperandPtr) (usePtrInBounds : usePtr.InBounds ctx),
      (usePtr.get ctx usePtrInBounds).value = valuePtr →
      usePtr.InBounds ctx')
    (hSameUseFields : ∀ (usePtr : OpOperandPtr) (usePtrInBounds : usePtr.InBounds ctx)
      (useOfValue : (usePtr.get ctx usePtrInBounds).value = valuePtr),
      (usePtr.get ctx' (by grind)) = (usePtr.get ctx usePtrInBounds))
    (hPreservesInBounds' : ∀ (usePtr : OpOperandPtr) (usePtrInBounds : usePtr.InBounds ctx'),
      (usePtr.get ctx' usePtrInBounds).value = valuePtr →
      usePtr.InBounds ctx)
    (hSameUseFields' : ∀ (usePtr : OpOperandPtr) (usePtrInBounds' : usePtr.InBounds ctx')
      (useOfValue : (usePtr.get ctx' usePtrInBounds').value = valuePtr),
      (usePtr.get ctx (by grind)) = (usePtr.get ctx' usePtrInBounds')) :
    valuePtr.WellFormedUseDefChain ctx' array  (by grind) := by
  constructor <;> grind [ValuePtr.WellFormedUseDefChain]


theorem IRContext.BlockPtr_UseDefChainWellFormed_unchanged
    (ctx ctx' : IRContext)
    (blockPtr : BlockPtr)
    (array : Array BlockOperandPtr)
    (valuePtrInBounds : blockPtr.InBounds ctx)
    (valuePtrInBounds' : blockPtr.InBounds ctx')
    (hWf : blockPtr.WellFormedUseDefChain ctx array (by grind))
    (hSameFirstUse : (blockPtr.get ctx (by grind)).firstUse = (blockPtr.get ctx' (by grind)).firstUse)
    (hSameUseFields : ∀ (usePtr : BlockOperandPtr) (usePtrInBounds : usePtr.InBounds ctx),
      (usePtr.get ctx usePtrInBounds).value = blockPtr →
      ∃ (usePtrInBounds' : usePtr.InBounds ctx'), (usePtr.get ctx' usePtrInBounds') = (usePtr.get ctx usePtrInBounds))
    (hSameUseFields' : ∀ (usePtr : BlockOperandPtr) (usePtrInBounds' : usePtr.InBounds ctx'),
      (usePtr.get ctx' usePtrInBounds').value = blockPtr →
      ∃ (usePtrInBounds : usePtr.InBounds ctx), (usePtr.get ctx usePtrInBounds) = (usePtr.get ctx' usePtrInBounds')) :
    blockPtr.WellFormedUseDefChain ctx' array := by
  constructor <;> grind [BlockPtr.WellFormedUseDefChain]

theorem IRContext.OperationChainWellFormed_unchanged
    (ctx ctx' : IRContext)
    (blockPtr : BlockPtr)
    (array : Array OperationPtr)
    (blockPtrInBounds : blockPtr.InBounds ctx)
    (blockPtrInBounds' : blockPtr.InBounds ctx')
    (hWf : blockPtr.OperationChainWellFormed ctx array (by grind))
    (hSameFirstOp : (blockPtr.get ctx (by grind)).firstOp = (blockPtr.get ctx' (by grind)).firstOp)
    (hSameLastOp : (blockPtr.get ctx (by grind)).lastOp = (blockPtr.get ctx' (by grind)).lastOp)
    (hSameOpFields : ∀ (opPtr : OperationPtr) (opPtrInBounds : opPtr.InBounds ctx),
      (opPtr.get ctx opPtrInBounds).parent = some blockPtr →
      ∃ (opPtrInBounds' : opPtr.InBounds ctx'),
        (opPtr.get ctx' opPtrInBounds').parent = (opPtr.get ctx opPtrInBounds).parent ∧
        (opPtr.get ctx' opPtrInBounds').prev = (opPtr.get ctx opPtrInBounds).prev ∧
        (opPtr.get ctx' opPtrInBounds').next = (opPtr.get ctx opPtrInBounds).next)
    (hSameOpFields' : ∀ (opPtr : OperationPtr) (opPtrInBounds' : opPtr.InBounds ctx'),
      (opPtr.get ctx' opPtrInBounds').parent = some blockPtr →
      ∃ (opPtrInBounds : opPtr.InBounds ctx),
        (opPtr.get ctx opPtrInBounds).parent = (opPtr.get ctx' opPtrInBounds').parent) :
    blockPtr.OperationChainWellFormed ctx' array blockPtrInBounds' := by
  constructor <;> grind [BlockPtr.OperationChainWellFormed]

theorem BlockPtr.OperationChainWellFormed_array_injective
    (block : BlockPtr) (ctx : IRContext) (array : Array OperationPtr)
    (hblock : block.InBounds ctx)
    (hWF : block.OperationChainWellFormed ctx array hblock) :
    ∀ (i j : Nat) iInBounds jInBounds, i ≠ j → array[i]'iInBounds ≠ array[j]'jInBounds := by
  intros i
  induction i <;> grind (splits := 30) [BlockPtr.OperationChainWellFormed]

theorem BlockPtr.OperationChainWellFormed_array_toList_Nodup
    (block : BlockPtr) (ctx : IRContext) (array : Array OperationPtr)
    (hblock : block.InBounds ctx)
    (hWF : block.OperationChainWellFormed ctx array hblock) :
    array.toList.Nodup := by
  simp only [List.nodup_iff_pairwise_ne]
  simp only [List.pairwise_iff_getElem]
  grind [BlockPtr.OperationChainWellFormed_array_injective]

theorem IRContext.BlockChainWellFormed_unchanged
    {ctx ctx' : IRContext}
    {regionPtr : RegionPtr}
    {array : Array BlockPtr}
    (regionPtrInBounds : regionPtr.InBounds ctx)
    (regionPtrInBounds' : regionPtr.InBounds ctx')
    (hWf : regionPtr.BlockChainWellFormed ctx array (by grind))
    (hSameFirst : (regionPtr.get ctx (by grind)).firstBlock = (regionPtr.get ctx' (by grind)).firstBlock)
    (hSameLast : (regionPtr.get ctx (by grind)).lastBlock = (regionPtr.get ctx' (by grind)).lastBlock)
    (hSameBlockFields : ∀ (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx),
      (blockPtr.get ctx blockPtrInBounds).parent = some regionPtr →
      ∃ (blockPtrInBounds' : blockPtr.InBounds ctx'),
        (blockPtr.get ctx' blockPtrInBounds').parent = (blockPtr.get ctx blockPtrInBounds).parent ∧
        (blockPtr.get ctx' blockPtrInBounds').prev = (blockPtr.get ctx blockPtrInBounds).prev ∧
        (blockPtr.get ctx' blockPtrInBounds').next = (blockPtr.get ctx blockPtrInBounds).next)
    (hSameBlockFields' : ∀ (blockPtr : BlockPtr) (blockPtrInBounds' : blockPtr.InBounds ctx'),
      (blockPtr.get ctx' blockPtrInBounds').parent = some regionPtr →
      ∃ (blockPtrInBounds : blockPtr.InBounds ctx),
        (blockPtr.get ctx blockPtrInBounds).parent = (blockPtr.get ctx' blockPtrInBounds').parent) :
    regionPtr.BlockChainWellFormed ctx' array regionPtrInBounds' := by
  constructor <;> grind [RegionPtr.BlockChainWellFormed]

theorem IRContext.Operation_WellFormed_unchanged
    (ctx ctx' : IRContext)
    (opPtr : OperationPtr)
    (opPtrInBounds : opPtr.InBounds ctx)
    (opPtrInBounds' : opPtr.InBounds ctx')
    (hWf : (opPtr.get ctx opPtrInBounds).WellFormed ctx opPtr opPtrInBounds)
    (hInBounds' : Operation.FieldsInBounds opPtr ctx' opPtrInBounds')
    (hSameNumOperands :
      (opPtr.get ctx opPtrInBounds).operands.size = (opPtr.get ctx' opPtrInBounds').operands.size)
    (hSameOperandOwner :
      let op := opPtr.get ctx opPtrInBounds
      let op' := opPtr.get ctx' opPtrInBounds'
      ∀ i (iInBounds : i < op.operands.size),
      op.operands[i].owner = op'.operands[i].owner)
    (hSameNumBlockOperands :
      (opPtr.get ctx opPtrInBounds).blockOperands.size = (opPtr.get ctx' opPtrInBounds').blockOperands.size)
    (hSameBlockOperandOwner :
      let op := opPtr.get ctx opPtrInBounds
      let op' := opPtr.get ctx' opPtrInBounds'
      ∀ i (iInBounds : i < op.blockOperands.size),
      op.blockOperands[i].owner = op'.blockOperands[i].owner)
    (hSameNumResults :
      opPtr.getNumResults ctx opPtrInBounds = opPtr.getNumResults ctx' opPtrInBounds')
    (hSameResultIndex :
      ∀ i (iInBounds : i < opPtr.getNumResults ctx opPtrInBounds),
      ((opPtr.getResult i).get ctx).index = ((opPtr.getResult i).get ctx').index)
    (hSameRegionParents :
      ∀ (regionPtr : RegionPtr) regionInBounds, (regionPtr.get ctx regionInBounds).parent = some opPtr →
        ∃ (regionInBounds' : regionPtr.InBounds ctx'),
          (regionPtr.get ctx regionInBounds).parent = (regionPtr.get ctx' regionInBounds').parent)
    (hSameRegionParents' :
      ∀ (regionPtr : RegionPtr) regionInBounds', (regionPtr.get ctx' regionInBounds').parent = some opPtr →
        ∃ (regionInBounds : regionPtr.InBounds ctx),
          (regionPtr.get ctx regionInBounds).parent = (regionPtr.get ctx' regionInBounds').parent)
    (hSameRegions :
      (opPtr.get ctx opPtrInBounds).regions = (opPtr.get ctx' opPtrInBounds').regions) :
    (opPtr.get ctx' opPtrInBounds').WellFormed ctx' opPtr opPtrInBounds' := by
  constructor <;> grind [Operation.WellFormed]

theorem IRContext.Block_WellFormed_unchanged
    (ctx ctx' : IRContext)
    (blockPtr : BlockPtr)
    (blockPtrInBounds : blockPtr.InBounds ctx)
    (blockPtrInBounds' : blockPtr.InBounds ctx')
    (hWf : (blockPtr.get ctx blockPtrInBounds).WellFormed ctx blockPtr blockPtrInBounds)
    (hInBounds' : Block.FieldsInBounds blockPtr ctx' blockPtrInBounds')
    (hSameNumArguments :
      (blockPtr.get ctx blockPtrInBounds).arguments.size = (blockPtr.get ctx' blockPtrInBounds').arguments.size)
    (hSameArgumentOwner :
      let block := blockPtr.get ctx blockPtrInBounds
      let block' := blockPtr.get ctx' blockPtrInBounds'
      ∀ i (iInBounds : i < block.arguments.size),
      block.arguments[i].owner = block'.arguments[i].owner)
    (hSameArgumentIndex :
      let block := blockPtr.get ctx blockPtrInBounds
      let block' := blockPtr.get ctx' blockPtrInBounds'
      ∀ i (iInBounds : i < block.arguments.size),
      block.arguments[i].index = block'.arguments[i].index) :
    (blockPtr.get ctx' blockPtrInBounds').WellFormed ctx' blockPtr blockPtrInBounds':= by
  constructor <;> grind [Block.WellFormed]

theorem IRContext.Region_WellFormed_unchanged
    (ctx ctx' : IRContext)
    (regionPtr : RegionPtr)
    (regionPtrInBounds : regionPtr.InBounds ctx)
    (regionPtrInBounds' : regionPtr.InBounds ctx')
    (hWf : (regionPtr.get ctx regionPtrInBounds).WellFormed ctx regionPtr)
    (hInBounds : (regionPtr.get ctx regionPtrInBounds).FieldsInBounds ctx)
    (hInBounds' : (regionPtr.get ctx' regionPtrInBounds').FieldsInBounds ctx')
    (hSameParentOp :
      let region := regionPtr.get ctx regionPtrInBounds
      let region' := regionPtr.get ctx' regionPtrInBounds'
      region.parent = region'.parent)
    (hParentRegionsUnchanged :
      ∀ parent (h : (regionPtr.get ctx regionPtrInBounds).parent = some parent),
      (parent.get ctx (by grind)).regions = (parent.get ctx' (by grind)).regions)
      :
    (regionPtr.get ctx' regionPtrInBounds').WellFormed ctx' regionPtr := by
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

noncomputable def ValuePtr.useDefArray (value : ValuePtr) (ctx : IRContext) (hctx : ctx.WellFormed) (hvalue : value.InBounds ctx) : Array OpOperandPtr :=
  (hctx.valueUseDefChains value hvalue).choose

@[grind .]
theorem ValuePtr.useDefArrayWF {hctx : IRContext.WellFormed ctx} :
    ValuePtr.WellFormedUseDefChain value ctx (ValuePtr.useDefArray value ctx hctx hvalue) hvalue :=
  Exists.choose_spec (hctx.valueUseDefChains value hvalue)

theorem ValuePtr.useDefArray_contains_operand_use :
    (operand.get ctx operandInBounds).value = value ↔
    operand ∈ ValuePtr.useDefArray value ctx hctx hvalue := by
  grind [ValuePtr.WellFormedUseDefChain, ValuePtr.useDefArrayWF]

theorem OperationPtr.getParent_prev_eq {ctxInBounds : ctx.FieldsInBounds}
    (hopParent : (OperationPtr.get opPtr ctx opInBounds).parent = some block)
    (hblock : BlockPtr.OperationChainWellFormed block ctx array hblock)
    (hprev : (OperationPtr.get opPtr ctx opInBounds).prev = some prevOp) :
    (prevOp.get ctx (by grind)).parent = some block := by
  grind (splits := 20) [BlockPtr.OperationChainWellFormed, Array.getElem?_of_mem]

theorem BlockPtr.OperationChainWellFormed_prev_ne
    (hop : OperationPtr.InBounds op ctx) (hctx : ctx.WellFormed)
    (hparent : (op.get ctx hop).parent = some block) :
    block.OperationChainWellFormed ctx array (by grind [IRContext.WellFormed]) →
    (op.get ctx hop).prev ≠ some op := by
  intros hNe
  have := hctx.inBounds
  have ⟨array, harray⟩ := hctx.opChain block (by grind)
  have : op ∈ array := by grind [BlockPtr.OperationChainWellFormed.allOpsInChain]
  intro heq
  have ⟨i, hi⟩ := Array.getElem?_of_mem this
  have : array[i - 1]? = some op := by grind [BlockPtr.OperationChainWellFormed]
  have : i > 0 := by grind [BlockPtr.OperationChainWellFormed]
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

end Mlir
