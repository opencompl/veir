module

public import Veir.IR.Fields
import Veir.IR.GetSet
import Veir.IR.InBounds
import Veir.IR.Grind

public section

namespace Veir

open ForLean

variable {OpInfo} [IsOpCode OpInfo]
variable {ctx ctx' : IRContext OpInfo}

/--
  A def-use chain for an SSA value.
  The def-use chain is represented as an ordered array of operands, where
  each operand corresponds to a use of the value. The first element of the
  array is the first use of the value.
  Each operand in the array points to the next use of the value, forming a
  linked list.
-/
structure ValuePtr.DefUse
    (value : ValuePtr) (ctx : IRContext OpInfo) (array : Array OpOperandPtr)
    (missingUses : Std.ExtHashSet OpOperandPtr := ∅) : Prop where
  valueInBounds : value.InBounds ctx
  arrayInBounds (h : use ∈ array) : use.InBounds ctx
  firstElem : array[0]? = value.getFirstUse! ctx
  firstUseBack (heq : value.getFirstUse! ctx = some firstUse) :
    firstUse.getBack! ctx = .valueFirstUse value
  allUsesInChain (use : OpOperandPtr) (huse : use.InBounds ctx) :
    use.getValue! ctx = value → (use ∈ array ↔ use ∉ missingUses)
  useValue (hin : use ∈ array) : use.getValue! ctx = value
  nextElems (hi : i < array.size) :
    array[i].getNextUse! ctx = array[i + 1]?
  prevNextUse (iPos : i > 0) (iInBounds : i < array.size) :
    array[i].getBack! ctx = OpOperandPtrPtr.operandNextUse array[i - 1]
  missingUsesInBounds (hin : use ∈ missingUses) : use.InBounds ctx
  missingUsesValue (hin : use ∈ missingUses) : use.getValue! ctx = value

attribute [grind →] ValuePtr.DefUse.valueInBounds
attribute [grind →] ValuePtr.DefUse.arrayInBounds
grind_pattern ValuePtr.DefUse.firstElem =>
    ValuePtr.DefUse value ctx array missingUses, value.getFirstUse! ctx
grind_pattern ValuePtr.DefUse.firstElem =>
    ValuePtr.DefUse value ctx array missingUses, array[0]?
grind_pattern ValuePtr.DefUse.firstUseBack =>
    ValuePtr.DefUse value ctx array missingUses, value.getFirstUse! ctx, some firstUse,
    (firstUse.getBack! ctx) where
  guard value.getFirstUse! ctx = some firstUse
grind_pattern ValuePtr.DefUse.allUsesInChain =>
    ValuePtr.DefUse value ctx array missingUses, use.getValue! ctx, use ∈ missingUses where
  guard (use.getValue! ctx) = value
attribute [grind →] ValuePtr.DefUse.useValue
grind_pattern ValuePtr.DefUse.nextElems =>
    ValuePtr.DefUse value ctx array missingUses, array[i].getNextUse! ctx
/- ValuePtr.DefUse.prevNextUse does not need a grind_pattern, because it is included in
  the `ValuePtr.DefUse.back_array_eq` pattern instead. -/
attribute [grind →] ValuePtr.DefUse.missingUsesInBounds
grind_pattern ValuePtr.DefUse.missingUsesValue =>
    ValuePtr.DefUse value ctx array missingUses, use ∈ missingUses, use.getValue! ctx

structure BlockPtr.DefUse (blockPtr : BlockPtr) (ctx : IRContext OpInfo)
    (array : Array BlockOperandPtr) (missingUses : Std.ExtHashSet BlockOperandPtr := ∅) : Prop where
  blockInBounds : blockPtr.InBounds ctx
  arrayInBounds (h : use ∈ array) : use.InBounds ctx
  firstElem : array[0]? = blockPtr.getFirstUse! ctx
  nextElems (hi : i < array.size) : array[i].getNextUse! ctx = array[i + 1]?
  useValue use (hu : use ∈ array) : use.getValue! ctx = blockPtr
  firstUseBack (heq : blockPtr.getFirstUse! ctx = some firstUse) :
    firstUse.getBack! ctx = BlockOperandPtrPtr.blockFirstUse blockPtr
  backNextUse i (iPos : i > 0) (iInBounds : i < array.size) :
    array[i].getBack! ctx = BlockOperandPtrPtr.blockOperandNextUse array[i - 1]
  allUsesInChain (use : BlockOperandPtr) (useInBounds : use.InBounds ctx) :
    use.getValue! ctx = blockPtr → (use ∈ array ↔ use ∉ missingUses)
  missingUsesInBounds (hin : use ∈ missingUses) : use.InBounds ctx
  missingUsesValue (hin : use ∈ missingUses) : use.getValue! ctx = blockPtr

attribute [grind →] BlockPtr.DefUse.blockInBounds
attribute [grind →] BlockPtr.DefUse.arrayInBounds
grind_pattern BlockPtr.DefUse.firstElem =>
    BlockPtr.DefUse blockPtr ctx array missingUses, blockPtr.getFirstUse! ctx
grind_pattern BlockPtr.DefUse.nextElems =>
    BlockPtr.DefUse blockPtr ctx array missingUses, array[i].getNextUse! ctx
grind_pattern BlockPtr.DefUse.useValue =>
    BlockPtr.DefUse blockPtr ctx array missingUses, use ∈ array, use.getValue! ctx
grind_pattern BlockPtr.DefUse.firstUseBack =>
    BlockPtr.DefUse blockPtr ctx array missingUses, blockPtr.getFirstUse! ctx,
    some firstUse, (firstUse.getBack! ctx) where
  guard (blockPtr.getFirstUse! ctx) = some firstUse
grind_pattern BlockPtr.DefUse.backNextUse =>
  BlockPtr.DefUse blockPtr ctx array missingUses, array[i].getBack! ctx
grind_pattern BlockPtr.DefUse.allUsesInChain =>
  BlockPtr.DefUse blockPtr ctx array missingUses, use.getValue! ctx, use ∈ missingUses
attribute [grind →] BlockPtr.DefUse.missingUsesInBounds
attribute [grind →] BlockPtr.DefUse.missingUsesValue

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
structure BlockPtr.OpChain (block : BlockPtr) (ctx : IRContext OpInfo) (array : Array OperationPtr)
    (missingOps : Std.ExtHashSet OperationPtr := ∅) : Prop where
  blockInBounds : block.InBounds ctx
  arrayInBounds (h : op ∈ array) : op.InBounds ctx
  missingOpInBounds (hin : op ∈ missingOps) : op.InBounds ctx
  opParent (h : op ∈ array) : op.getParent! ctx = some block
  missingOpValue (hin : op ∈ missingOps) : op.getParent! ctx = block
  allOpsInChain (op : OperationPtr) (opInBounds : op.InBounds ctx) :
    op.getParent! ctx = some block → (op ∈ array ↔ op ∉ missingOps)
  first : block.getFirstOp! ctx = array[0]?
  last : block.getLastOp! ctx = array[array.size-1]?
  prevFirst (h : block.getFirstOp! ctx = some firstOp) :
    firstOp.getPrevOp! ctx = none
  prev i (h₁: i > 0) (h₂ : i < array.size) :
    array[i].getPrevOp! ctx = some array[i - 1]
  next (hi : i < array.size) :
    array[i].getNextOp! ctx = array[i + 1]?

attribute [grind →] BlockPtr.OpChain.blockInBounds
attribute [grind →] BlockPtr.OpChain.arrayInBounds
attribute [grind →] BlockPtr.OpChain.missingOpInBounds
grind_pattern BlockPtr.OpChain.opParent =>
    BlockPtr.OpChain block ctx array missingOps, op ∈ array, op.getParent! ctx
grind_pattern BlockPtr.OpChain.missingOpValue =>
    BlockPtr.OpChain block ctx array missingOps, op ∈ missingOps, op.getParent! ctx
grind_pattern BlockPtr.OpChain.allOpsInChain =>
    BlockPtr.OpChain block ctx array missingOps, op.getParent! ctx,
    some block, op ∈ missingOps where
  guard (op.getParent! ctx) = some block
grind_pattern BlockPtr.OpChain.first =>
    BlockPtr.OpChain block ctx array missingOps, block.getFirstOp! ctx
grind_pattern BlockPtr.OpChain.last =>
    BlockPtr.OpChain block ctx array missingOps, block.getLastOp! ctx
grind_pattern BlockPtr.OpChain.prevFirst =>
    BlockPtr.OpChain block ctx array missingOps, block.getFirstOp! ctx,
    some firstOp, (firstOp.getPrevOp! ctx) where
  guard (block.getFirstOp! ctx) = some firstOp
grind_pattern BlockPtr.OpChain.prev =>
    BlockPtr.OpChain block ctx array missingOps, array[i].getPrevOp! ctx
grind_pattern BlockPtr.OpChain.next =>
    BlockPtr.OpChain block ctx array missingOps, array[i].getNextOp! ctx

structure RegionPtr.BlockChain (region : RegionPtr) (ctx : IRContext OpInfo) (array : Array BlockPtr) : Prop where
  inBounds : region.InBounds ctx
  arrayInBounds (h : bl ∈ array) : bl.InBounds ctx
  opParent (h : bl ∈ array) : bl.getParent! ctx = some region
  first : region.getFirstBlock! ctx = array[0]?
  last : region.getLastBlock! ctx = array[array.size-1]?
  prevFirst (h : region.getFirstBlock! ctx = some fbl) :
    fbl.getPrevBlock! ctx = none
  prev i (h₁: i > 0) (h₂ : i < array.size) :
    array[i].getPrevBlock! ctx = some array[i - 1]
  next (hi : i < array.size) :
    array[i].getNextBlock! ctx = array[i + 1]?
  allBlocksInChain (bl : BlockPtr) (blInBoundsl : bl.InBounds ctx) :
    bl.getParent! ctx = some region → bl ∈ array

attribute [grind →] RegionPtr.BlockChain.inBounds
attribute [grind →] RegionPtr.BlockChain.arrayInBounds
grind_pattern RegionPtr.BlockChain.opParent =>
    RegionPtr.BlockChain region ctx array, bl ∈ array, bl.getParent! ctx
grind_pattern RegionPtr.BlockChain.first =>
    RegionPtr.BlockChain region ctx array, region.getFirstBlock! ctx
grind_pattern RegionPtr.BlockChain.last =>
    RegionPtr.BlockChain region ctx array, region.getLastBlock! ctx
grind_pattern RegionPtr.BlockChain.prevFirst =>
    RegionPtr.BlockChain region ctx array, region.getFirstBlock! ctx,
    some fbl, (fbl.getPrevBlock! ctx) where
  guard (region.getFirstBlock! ctx) = some fbl
grind_pattern RegionPtr.BlockChain.prev =>
    RegionPtr.BlockChain region ctx array, array[i].getPrevBlock! ctx
grind_pattern RegionPtr.BlockChain.next =>
    RegionPtr.BlockChain region ctx array, array[i].getNextBlock! ctx
grind_pattern RegionPtr.BlockChain.allBlocksInChain =>
    RegionPtr.BlockChain region ctx array, (bl.getParent! ctx) where
  guard (bl.getParent! ctx) = some region

structure OperationPtr.WellFormed (ctx : IRContext OpInfo) (opPtr : OperationPtr) hop : Prop where
  inBounds : Operation.FieldsInBounds opPtr ctx hop
  result_index i (iInBounds : i < opPtr.getNumResults! ctx) : (opPtr.getResult i).getIndex! ctx = i
  result_owner i (iInBounds : i < opPtr.getNumResults! ctx) :
    (opPtr.getResult i).getOwner! ctx = opPtr
  operand_owner i (iInBounds : i < opPtr.getNumOperands! ctx) : (opPtr.getOpOperand i).getOwner! ctx = opPtr
  blockOperand_owner i (iInBounds : i < opPtr.getNumSuccessors! ctx) : (opPtr.getBlockOperand i).getOwner! ctx = opPtr
  regions_unique i (iInBounds : i < opPtr.getNumRegions! ctx) j (jInBounds : j < opPtr.getNumRegions! ctx) :
    i ≠ j → opPtr.getRegion ctx i ≠ opPtr.getRegion ctx j
  region_parent region (regionInBounds : region.InBounds ctx) :
    (∃ i, i < opPtr.getNumRegions! ctx ∧ opPtr.getRegion! ctx i = region) ↔
    region.getParent! ctx = some opPtr
  opChain_of_parent_none : opPtr.getParent! ctx = none →
    opPtr.getPrevOp! ctx = none ∧ opPtr.getNextOp! ctx = none

structure BlockPtr.WellFormed (ctx : IRContext OpInfo) (blockPtr : BlockPtr) hbl : Prop where
  inBounds : Block.FieldsInBounds blockPtr ctx hbl
  argument i (iInBounds : i < blockPtr.getNumArguments! ctx) : (blockPtr.getArgument i).getIndex! ctx = i
  argument_owners i (iInBounds : i < blockPtr.getNumArguments! ctx) : (blockPtr.getArgument i).getOwner! ctx = blockPtr
  prev_eq_of_parent_eq_none : blockPtr.getParent! ctx = none →
    blockPtr.getPrevBlock! ctx = none
  next_eq_of_parent_eq_none : blockPtr.getParent! ctx = none →
    blockPtr.getNextBlock! ctx = none

structure RegionPtr.WellFormed (ctx : IRContext OpInfo) (regionPtr : RegionPtr) where
  inBounds : regionPtr.FieldsInBounds ctx
  parent_op {op} (heq : regionPtr.getParent! ctx = some op) : ∃ i, i < op.getNumRegions! ctx ∧ op.getRegion! ctx i = regionPtr

structure IRContext.WellFormed (ctx : IRContext OpInfo)
  (missingOperandUses : Std.ExtHashSet OpOperandPtr := ∅)
  (missingSuccessorUses : Std.ExtHashSet BlockOperandPtr := ∅) : Prop where
  inBounds : ctx.FieldsInBounds
  valueDefUseChains (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∃ array, ValuePtr.DefUse valuePtr ctx array (missingOperandUses.filter (fun use => use.getValue! ctx = valuePtr))
  blockDefUseChains (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    ∃ array, BlockPtr.DefUse blockPtr ctx array (missingSuccessorUses.filter (fun use => use.getValue! ctx = blockPtr))
  opChain (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    ∃ array, BlockPtr.OpChain blockPtr ctx array
  blockChain (regionPtr : RegionPtr) (regionPtrInBounds : regionPtr.InBounds ctx) :
    ∃ array, RegionPtr.BlockChain regionPtr ctx array
  operations (opPtr : OperationPtr) (opPtrInBounds : opPtr.InBounds ctx) :
    opPtr.WellFormed ctx opPtrInBounds
  blocks (blockPtr : BlockPtr) (blockPtrInBounds : blockPtr.InBounds ctx) :
    blockPtr.WellFormed ctx blockPtrInBounds
  regions (regionPtr : RegionPtr) (regionPtrInBounds : regionPtr.InBounds ctx) :
    regionPtr.WellFormed ctx

attribute [grind →] IRContext.WellFormed.inBounds

noncomputable def BlockPtr.operationList (block : BlockPtr) (ctx : IRContext OpInfo)
    (hctx : ctx.WellFormed := by grind) (hblock : block.InBounds ctx := by grind) :
    Array OperationPtr :=
  (hctx.opChain block hblock).choose

noncomputable def RegionPtr.blockList (region : RegionPtr)
    (ctx : IRContext OpInfo) (hctx : ctx.WellFormed := by grind)
    (hregion : region.InBounds ctx := by grind) : Array BlockPtr :=
  (hctx.blockChain region hregion).choose

noncomputable def ValuePtr.defUseArray (value : ValuePtr) (ctx : IRContext OpInfo) (hctx : ctx.WellFormed missingUses missingBlockUses) (hvalue : value.InBounds ctx) : Array OpOperandPtr :=
  (hctx.valueDefUseChains value hvalue).choose

/--
  Compute the index of an operation in its parent's operations list.
  If the operation does not have a parent, return 0.
-/
noncomputable def OperationPtr.idxInParent (op : OperationPtr) (ctx : IRContext OpInfo)
    (hop : op.InBounds ctx := by grind)
    (hctx : ctx.WellFormed := by grind) : Nat :=
  match hparent : op.getParent! ctx with
  | some block => (block.operationList ctx hctx (by grind)).idxOf op
  | none       => 0

/--
  Compute the index of an operation in its parent's operations list from the tail
  (i.e. the last operation has index 0).
  If the operation does not have a parent, return 0.

  This function is useful for proving termination of recursive functions that traverse
  the operation list, as this function decreases when we move to the next operation in the list.
-/
noncomputable def OperationPtr.idxInParentFromTail (op : OperationPtr) (ctx : IRContext OpInfo)
    (hop : op.InBounds ctx := by grind)
    (hctx : ctx.WellFormed := by grind) : Nat :=
  match hparent : op.getParent! ctx with
  | some block =>
    (block.operationList ctx hctx (by grind)).size - 1 - op.idxInParent ctx hop hctx
  | none       => 0


@[grind .]
theorem ValuePtr.DefUse_unique :
    ValuePtr.DefUse value ctx array missingUses →
    ValuePtr.DefUse value ctx array' missingUses →
    array = array' := by
  intros hWf hWf'
  apply Array.ext_getElem?
  intros i
  induction i
  · grind [→ ValuePtr.DefUse.firstElem]
  · grind [→ ValuePtr.DefUse.nextElems]

theorem ValuePtr.DefUse.unchanged
    (hWf : valuePtr.DefUse ctx array missingUses)
    (valuePtrInBounds' : valuePtr.InBounds ctx')
    (hSameFirstUse : valuePtr.getFirstUse! ctx = valuePtr.getFirstUse! ctx')
    (hPreservesInBounds : ∀ (usePtr : OpOperandPtr),
      usePtr.InBounds ctx →
      usePtr.getValue! ctx = valuePtr → usePtr.InBounds ctx')
    (hSameUseFields : ∀ (usePtr : OpOperandPtr),
      usePtr.InBounds ctx → usePtr.getValue! ctx = valuePtr →
      usePtr.getNextUse! ctx' = usePtr.getNextUse! ctx ∧
      usePtr.getBack! ctx' = usePtr.getBack! ctx ∧
      usePtr.getValue! ctx' = usePtr.getValue! ctx)
    (hPreservesInBounds' : ∀ (usePtr : OpOperandPtr),
      usePtr.InBounds ctx' →
      usePtr.getValue! ctx' = valuePtr →
      usePtr.InBounds ctx)
    (hSameUseFields' : ∀ (usePtr : OpOperandPtr),
      usePtr.InBounds ctx' →
      usePtr.getValue! ctx' = valuePtr →
      usePtr.getNextUse! ctx = usePtr.getNextUse! ctx' ∧
      usePtr.getBack! ctx = usePtr.getBack! ctx' ∧
      usePtr.getValue! ctx = usePtr.getValue! ctx') :
    valuePtr.DefUse ctx' array missingUses := by
  grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse.back_array_eq
    (hWF : ValuePtr.DefUse value ctx array missingUses) :
    (array[i]'hi).getBack! ctx =
    if i = 0 then .valueFirstUse value else OpOperandPtrPtr.operandNextUse array[i - 1] := by
  grind [ValuePtr.DefUse]

grind_pattern ValuePtr.DefUse.back_array_eq =>
    value.DefUse ctx array missingUses, array[i].getBack! ctx

theorem ValuePtr.DefUse.OpOperandPtr_value_of_getFirstUse
    {firstUse : OpOperandPtr} (hFirstUse : value.getFirstUse! ctx = some firstUse)
    (hDefUse : value.DefUse ctx array missingUses) :
    firstUse.getValue! ctx = value := by
  grind [ValuePtr.DefUse]

grind_pattern ValuePtr.DefUse.OpOperandPtr_value_of_getFirstUse =>
    value.DefUse ctx array missingUses, value.getFirstUse! ctx,
    (firstUse.getValue! ctx) where
  guard value.getFirstUse! ctx = some firstUse

theorem ValuePtr.DefUse.ValuePtr_getFirstUse_ne_of_value_ne
    {use use' : OpOperandPtr}
    (valueNe : use.getValue! ctx ≠ use'.getValue! ctx)
    (hWF : (use.getValue! ctx).DefUse ctx array missingUses) :
    (use.getValue! ctx).getFirstUse! ctx ≠ some use' := by
  grind

theorem ValuePtr.DefUse_getFirstUse!_value_eq_of_back_eq_valueFirstUse
    {firstUse : OpOperandPtr} (hFirstUse : firstUse.InBounds ctx)
    (hvalueFirstUse : (firstUse.getValue! ctx).DefUse ctx array)
    (heq : firstUse.getBack! ctx = .valueFirstUse value') :
    (firstUse.getValue! ctx).getFirstUse! ctx = some firstUse := by
  grind [ValuePtr.DefUse, Array.getElem?_of_mem]

theorem ValuePtr.DefUse.value!_eq_of_back!_eq_valueFirstUse
    {firstUse : OpOperandPtr}
    (hDefUse : (firstUse.getValue! ctx).DefUse ctx array missingUses)
    (hInArray : firstUse ∈ array) :
    firstUse.getBack! ctx = .valueFirstUse value →
    firstUse.getValue! ctx = value := by
  have inArray : firstUse ∈ array := by grind [ValuePtr.DefUse]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem inArray
  cases i <;> grind

theorem ValuePtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse
    {firstUse : OpOperandPtr}
    (hvalueFirstUse : (firstUse.getValue! ctx).DefUse ctx array missingUses)
    (hInArray : firstUse ∈ array)
    (heq : firstUse.getBack! ctx = .valueFirstUse value) :
    value.getFirstUse! ctx = some firstUse := by
  have : firstUse.getValue! ctx = value := by grind [ValuePtr.DefUse.value!_eq_of_back!_eq_valueFirstUse]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem hInArray
  cases i <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse_back_eq_of_getFirstUse
    {firstUse : OpOperandPtr}
    (hvalueFirstUse : value.DefUse ctx array missingUses)
    (h : value.getFirstUse! ctx = some firstUse) :
    firstUse.getBack! ctx = .valueFirstUse value := by
  grind

theorem ValuePtr.DefUse_getFirstUse!_eq_iff_back_eq_valueFirstUse
    {firstUse : OpOperandPtr}
    (hDefUse : (firstUse.getValue! ctx).DefUse ctx array missingUses)
    (hFirstUse : firstUse ∈ array)
    (hDefUse' : value'.DefUse ctx array' missingUses') :
    firstUse.getBack! ctx = .valueFirstUse value' ↔
    value'.getFirstUse! ctx = some firstUse := by
  grind [ValuePtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse]

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
    (useDefUse : (use.getValue! ctx).DefUse ctx array missingUses) :
    use.getNextUse! ctx = some use' →
    use.getValue! ctx = use'.getValue! ctx := by
  intros huse'
  have : use ∈ array := by grind
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  grind [ValuePtr.DefUse]

@[grind .]
theorem ValuePtr.DefUse.value!_eq_value!_of_back!_eq_operandNextUse
    {use : OpOperandPtr}
    (useInArray : use ∈ array)
    (useDefUse : (use.getValue! ctx).DefUse ctx array missingUses) :
    use.getBack! ctx = .operandNextUse use' →
    use.getValue! ctx = use'.getValue! ctx := by
  intros huse'
  have : use ∈ array := by grind
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind [ValuePtr.DefUse]

theorem ValuePtr.DefUse.nextUse!_ne_of_getFirstUse!_eq {value : ValuePtr} {use : OpOperandPtr}
    (valueDefUse : ValuePtr.DefUse value ctx array missingUses)
    (useInArray : use ∈ array')
    (useDefUse : (use.getValue! ctx).DefUse ctx array' missingUses') :
    value.getFirstUse! ctx = some firstUse →
    use.getNextUse! ctx ≠ some firstUse := by
  intros hFirstUse hNextUse
  have : use.getValue! ctx = firstUse.getValue! ctx := by grind
  have : use.getValue! ctx = value := by grind
  subst value
  have : firstUse = array[0]'(by grind) := by grind
  have ⟨j, jInBounds, hj⟩ := Array.getElem_of_mem useInArray
  grind [ValuePtr.DefUse]

@[grind .]
theorem ValuePtr.DefUse.OpOperandPtr_setValue_self_of_value!_ne_self
    {use : OpOperandPtr} {useInBounds}
    (useOfOtherValue : use.getValue! ctx ≠ value) :
    value.DefUse ctx array missingUses →
    value.DefUse (use.setValue ctx value useInBounds) array (missingUses.insert use) := by
  intros hWF
  constructor <;> grind

theorem ValuePtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
    {use : OpOperandPtr} {useInBounds} (useOfOtherValue : use.getValue! ctx ≠ value) :
    value.DefUse ctx array →
    value.DefUse (use.setValue ctx value useInBounds) array (Std.ExtHashSet.ofList [use]) := by
  intros hWF
  constructor <;> grind

@[grind .]
theorem ValuePtr.DefUse.OpOperandPtr_setValue_other_of_mem_missingUses
    {use : OpOperandPtr} {value value' : ValuePtr} {useInBounds}
    (useOfOtherValue : use.getValue! ctx ≠ value') {array} :
    use ∈ missingUses →
    value.DefUse ctx array missingUses →
    value.DefUse (use.setValue ctx value' useInBounds) array (missingUses.erase use) := by
  intros useNotMissing hWF
  constructor <;> grind

@[grind .]
theorem ValuePtr.DefUse.OpOperandPtr_setValue_other_empty
    {use : OpOperandPtr} {value value' : ValuePtr} {useInBounds}
    (useOfOtherValue : use.getValue! ctx ≠ value') {array} :
    value.DefUse ctx array (Std.ExtHashSet.ofList [use]) →
    value.DefUse (use.setValue ctx value' useInBounds) array := by
  intro hWF
  constructor
  case allUsesInChain => grind [hWF.allUsesInChain]
  case useValue => grind [ValuePtr.DefUse]
  all_goals grind

@[grind .]
theorem ValuePtr.DefUse.OpOperandPtr_setValue_other_of_value_ne
    {ctx : IRContext OpInfo} {use : OpOperandPtr} {useInBounds} (value : ValuePtr)
    (useOfOtherValue' : use.getValue! ctx ≠ value')
    (valueNe : value ≠ value') {array} :
    value'.DefUse ctx array missingUses →
    value'.DefUse (use.setValue ctx value useInBounds) array missingUses := by
  intro hWF
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind

section BlockPtr.DefUse

theorem BlockPtr.DefUse.unchanged
    (hWf : blockPtr.DefUse ctx array missingUses)
    (blockPtrInBounds' : blockPtr.InBounds ctx')
    (hSameFirstUse : blockPtr.getFirstUse! ctx = blockPtr.getFirstUse! ctx')
    (hPreservesInBounds : ∀ (usePtr : BlockOperandPtr),
      usePtr.InBounds ctx →
      usePtr.getValue! ctx = blockPtr → usePtr.InBounds ctx')
    (hSameUseFields : ∀ (usePtr : BlockOperandPtr),
      usePtr.InBounds ctx → usePtr.getValue! ctx = blockPtr →
      usePtr.getNextUse! ctx' = usePtr.getNextUse! ctx ∧
      usePtr.getBack! ctx' = usePtr.getBack! ctx ∧
      usePtr.getValue! ctx' = usePtr.getValue! ctx)
    (hPreservesInBounds' : ∀ (usePtr : BlockOperandPtr),
      usePtr.InBounds ctx' →
      usePtr.getValue! ctx' = blockPtr →
      usePtr.InBounds ctx)
    (hSameUseFields' : ∀ (usePtr : BlockOperandPtr),
      usePtr.InBounds ctx' →
      usePtr.getValue! ctx' = blockPtr →
      usePtr.getNextUse! ctx = usePtr.getNextUse! ctx' ∧
      usePtr.getBack! ctx = usePtr.getBack! ctx' ∧
      usePtr.getValue! ctx = usePtr.getValue! ctx') :
    blockPtr.DefUse ctx' array missingUses := by
  constructor <;> grind [BlockPtr.DefUse]

theorem BlockPtr.DefUse.back_array_eq
    (hWF : BlockPtr.DefUse block ctx array missingUses) :
    (array[i]'hi).getBack! ctx =
    if i = 0 then .blockFirstUse block else .blockOperandNextUse array[i - 1] := by
  grind [BlockPtr.DefUse]

grind_pattern BlockPtr.DefUse.back_array_eq =>
    block.DefUse ctx array missingUses, array[i].getBack! ctx

theorem BlockPtr.DefUse.getFirstUse_ne_of_value_ne
    {use use' : BlockOperandPtr}
    (valueNe : use.getValue! ctx ≠ use'.getValue! ctx)
    (hWF : (use.getValue! ctx).DefUse ctx array missingUses) :
    (use.getValue! ctx).getFirstUse! ctx ≠ some use' := by
  grind [BlockPtr.DefUse]

theorem BlockPtr.DefUse.getFirstUse!_value_eq_of_back_eq_valueFirstUse
    {firstUse : BlockOperandPtr} (hFirstUse : firstUse.InBounds ctx)
    (hvalueFirstUse : (firstUse.getValue! ctx).DefUse ctx array)
    (heq : firstUse.getBack! ctx = .blockFirstUse block) :
    (firstUse.getValue! ctx).getFirstUse! ctx = some firstUse := by
  have : firstUse ∈ array := by grind [BlockPtr.DefUse]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind

theorem BlockPtr.DefUse.value!_eq_of_back!_eq_valueFirstUse
    {firstUse : BlockOperandPtr}
    (hDefUse : (firstUse.getValue! ctx).DefUse ctx array missingUses)
    (hInArray : firstUse ∈ array) :
    firstUse.getBack! ctx = .blockFirstUse block →
    firstUse.getValue! ctx = block := by
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem hInArray
  cases i <;> grind [BlockPtr.DefUse]

theorem BlockPtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse
    {firstUse : BlockOperandPtr}
    (hvalueFirstUse : (firstUse.getValue! ctx).DefUse ctx array missingUses)
    (hInArray : firstUse ∈ array)
    (heq : firstUse.getBack! ctx = .blockFirstUse block) :
    block.getFirstUse! ctx = some firstUse := by
  have : firstUse.getValue! ctx = block := by grind [BlockPtr.DefUse.value!_eq_of_back!_eq_valueFirstUse]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem hInArray
  cases i <;> grind [Array.getElem?_of_mem]

theorem BlockPtr.DefUse_back_eq_of_getFirstUse
    {firstUse : BlockOperandPtr}
    (hvalueFirstUse : block.DefUse ctx array missingUses)
    (h : block.getFirstUse! ctx = some firstUse) :
    firstUse.getBack! ctx = .blockFirstUse block := by
  have : firstUse.getValue! ctx = block := by grind [BlockPtr.DefUse]
  grind [Array.getElem?_of_mem]

theorem BlockPtr.DefUse.value_eq_of_getFirstUse
    (hvalueFirstUse : BlockPtr.DefUse block ctx array missingUses)
    (h : block.getFirstUse! ctx = some firstUse) :
    firstUse.getValue! ctx = block := by
  grind [BlockPtr.DefUse]

grind_pattern BlockPtr.DefUse.value_eq_of_getFirstUse =>
  BlockPtr.DefUse block ctx array missingUses, block.getFirstUse! ctx, firstUse.getValue! ctx

theorem BlockPtr.DefUse_getFirstUse!_eq_iff_back_eq_valueFirstUse
    {firstUse : BlockOperandPtr}
    (hDefUse : (firstUse.getValue! ctx).DefUse ctx array missingUses)
    (hFirstUse : firstUse ∈ array)
    (hDefUse' : block'.DefUse ctx array' missingUses') :
    firstUse.getBack! ctx = .blockFirstUse block' ↔
    block'.getFirstUse! ctx = some firstUse := by
  constructor
  · grind [BlockPtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse]
  · grind [BlockPtr.DefUse_back_eq_of_getFirstUse]

theorem BlockPtr.DefUse_array_injective
    (hWF : BlockPtr.DefUse block ctx array missingUses) :
    ∀ (i j : Nat) iInBounds jInBounds, i ≠ j →
    array[i]'iInBounds ≠ array[j]'jInBounds := by
  intros i
  induction i
  · grind [BlockPtr.DefUse]
  · rintro ⟨_|_⟩ <;> grind [BlockPtr.DefUse]

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
    (useDefUse : (use.getValue! ctx).DefUse ctx array missingUses) :
    use.getNextUse! ctx = some use' →
    use.getValue! ctx = use'.getValue! ctx := by
  intros huse'
  have : use ∈ array := by grind
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  grind [BlockPtr.DefUse]

@[grind .]
theorem BlockPtr.DefUse.value!_eq_value!_of_back!_eq_operandNextUse
    {use : BlockOperandPtr}
    (useInArray : use ∈ array)
    (useDefUse : (use.getValue! ctx).DefUse ctx array missingUses) :
    use.getBack! ctx = .blockOperandNextUse use' →
    use.getValue! ctx = use'.getValue! ctx := by
  intros huse'
  have : use ∈ array := by grind
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind [BlockPtr.DefUse]

theorem BlockPtr.DefUse.nextUse!_ne_of_getFirstUse!_eq {value : BlockPtr} {use : BlockOperandPtr}
    (valueDefUse : BlockPtr.DefUse value ctx array missingUses)
    (useInArray : use ∈ array')
    (useDefUse : (use.getValue! ctx).DefUse ctx array' missingUses') :
    value.getFirstUse! ctx = some firstUse →
    use.getNextUse! ctx ≠ some firstUse := by
  intros hFirstUse hNextUse
  have : use.getValue! ctx = firstUse.getValue! ctx := by grind
  have : use.getValue! ctx = value := by grind
  subst value
  have : firstUse = array[0]'(by grind) := by grind
  have ⟨j, jInBounds, hj⟩ := Array.getElem_of_mem useInArray
  grind [BlockPtr.DefUse]

@[grind .]
theorem BlockPtr.DefUse.OpOperandPtr_setValue_self_of_value!_ne_self
    {use : BlockOperandPtr} {useInBounds}
    (useOfOtherValue : use.getValue! ctx ≠ value) :
    value.DefUse ctx array missingUses →
    value.DefUse (use.setValue ctx value useInBounds) array (missingUses.insert use) := by
  intros hWF
  constructor <;> grind

theorem BlockPtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
    {use : BlockOperandPtr} {useInBounds} (useOfOtherValue : use.getValue! ctx ≠ value) :
    value.DefUse ctx array →
    value.DefUse (use.setValue ctx value useInBounds) array (Std.ExtHashSet.ofList [use]) := by
  intros hWF
  constructor <;> grind

@[grind .]
theorem BlockPtr.DefUse.OpOperandPtr_setValue_other_of_mem_missingUses
    {use : BlockOperandPtr} {block block' : BlockPtr} {useInBounds}
    (useOfOtherValue : use.getValue! ctx ≠ block') {array} :
    use ∈ missingUses →
    block.DefUse ctx array missingUses →
    block.DefUse (use.setValue ctx block' useInBounds) array (missingUses.erase use) := by
  intros useNotMissing hWF
  constructor <;> grind

@[grind .]
theorem BlockPtr.DefUse.OpOperandPtr_setValue_other_empty
    {use : BlockOperandPtr} {block block' : BlockPtr} {useInBounds}
    (useOfOtherValue : use.getValue! ctx ≠ block') {array} :
    block.DefUse ctx array (Std.ExtHashSet.ofList [use]) →
    block.DefUse (use.setValue ctx block' useInBounds) array := by
  intros hWF
  constructor <;> grind [BlockPtr.DefUse]

@[grind .]
theorem BlockPtr.DefUse.OpOperandPtr_setValue_other_of_value_ne
    {ctx : IRContext OpInfo} {use : BlockOperandPtr} {useInBounds} (block : BlockPtr)
    (useOfOtherValue' : use.getValue! ctx ≠ block')
    (valueNe : block ≠ block') {array} :
    block'.DefUse ctx array missingUses →
    block'.DefUse (use.setValue ctx block useInBounds) array missingUses := by
  intro hWF
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind

end BlockPtr.DefUse

@[grind .]
theorem BlockPtr.OpChain_unique :
    BlockPtr.OpChain block ctx array →
    BlockPtr.OpChain block ctx array' →
    array = array' := by
  intros hWf hWf'
  apply Array.ext_getElem?
  intros i
  induction i <;> grind [BlockPtr.OpChain]

theorem BlockPtr.OpChain.allOpsInChain_emptySet
    (hChain : BlockPtr.OpChain block ctx array ∅)
    (op : OperationPtr) (opInBounds : op.InBounds ctx) :
    op.getParent! ctx = some block → op ∈ array := by
  grind [→ BlockPtr.OpChain.allOpsInChain]

grind_pattern BlockPtr.OpChain.allOpsInChain_emptySet =>
    BlockPtr.OpChain block ctx array ∅, op.getParent! ctx, some block where
  guard (op.getParent! ctx) = some block

theorem BlockPtr.OpChain.firstOp_eq_none_iff_lastOp_eq_none :
    BlockPtr.OpChain block ctx array missingOps →
    (block.getFirstOp! ctx = none ↔ block.getLastOp! ctx = none) := by
  grind [BlockPtr.OpChain]

theorem BlockPtr.OpChain.prev!_eq_none_iff_firstOp!_eq_self {op : OperationPtr}
    (hopInBounds : op.InBounds ctx)
    (hchain : BlockPtr.OpChain block ctx array)
    (hop : op.getParent! ctx = some block) :
    (op.getPrevOp! ctx = none ↔ block.getFirstOp! ctx = some op) := by
  constructor
  · intro hprev
    have opInArray : op ∈ array := by grind [BlockPtr.OpChain]
    have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem opInArray
    have : i = 0 := by grind [BlockPtr.OpChain]
    grind [BlockPtr.OpChain]
  · grind [BlockPtr.OpChain]

theorem BlockPtr.OpChain.next!_eq_none_iff_lastOp!_eq_self {op : OperationPtr}
    (hopInBounds : op.InBounds ctx)
    (hchain : BlockPtr.OpChain block ctx array)
    (hop : op.getParent! ctx = some block) :
    (op.getNextOp! ctx = none ↔ block.getLastOp! ctx = some op) := by
  constructor
  · intro hprev
    have opInArray : op ∈ array := by grind [BlockPtr.OpChain]
    have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem opInArray
    have : i = array.size - 1 := by grind [BlockPtr.OpChain]
    grind [BlockPtr.OpChain]
  · grind [BlockPtr.OpChain]

theorem BlockPtr.OpChain.parent!_firstOp_eq
    (hChain : BlockPtr.OpChain block ctx array missingOps)
    {firstOp : OperationPtr} :
    block.getFirstOp! ctx = some firstOp →
    firstOp.getParent! ctx = some block := by
  grind [BlockPtr.OpChain]

grind_pattern BlockPtr.OpChain.parent!_firstOp_eq =>
  BlockPtr.OpChain block ctx array missingOps,
  block.getFirstOp! ctx, (firstOp.getParent! ctx) where
    guard (block.getFirstOp! ctx) = some firstOp

theorem BlockPtr.OpChain.parent!_lastOp_eq
    (hChain : BlockPtr.OpChain block ctx array missingOps)
    {lastOp : OperationPtr} :
    block.getLastOp! ctx = some lastOp →
    lastOp.getParent! ctx = some block := by
  grind [BlockPtr.OpChain]

grind_pattern BlockPtr.OpChain.parent!_lastOp_eq =>
  BlockPtr.OpChain block ctx array missingOps,
  block.getLastOp! ctx, (lastOp.getParent! ctx) where
    guard (block.getLastOp! ctx) = some lastOp

theorem BlockPtr.OpChain.parent!_prevOp_eq
    {op prevOp : OperationPtr}
    (hChain : BlockPtr.OpChain block ctx array)
    (opInBounds : op.InBounds ctx) :
    op.getParent! ctx = some block →
    op.getPrevOp! ctx = some prevOp →
    prevOp.getParent! ctx = some block := by
  intros hParent hPrev
  have : op ∈ array := by grind [BlockPtr.OpChain]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind [BlockPtr.OpChain]

grind_pattern BlockPtr.OpChain.parent!_prevOp_eq =>
  BlockPtr.OpChain block ctx array,
  op.getParent! ctx, op.getPrevOp! ctx, some block,
  (prevOp.getParent! ctx) where
    guard (op.getParent! ctx) = some block
    guard (op.getPrevOp! ctx) = some prevOp

theorem BlockPtr.OpChain.parent!_nextOp_eq
    {op nextOp : OperationPtr}
    (hChain : BlockPtr.OpChain block ctx array)
    (opInBounds : op.InBounds ctx) :
    op.getParent! ctx = some block →
    op.getNextOp! ctx = some nextOp →
    nextOp.getParent! ctx = some block := by
  intros hParent hPext
  have : op ∈ array := by grind [BlockPtr.OpChain]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem this
  cases i <;> grind [BlockPtr.OpChain]

grind_pattern BlockPtr.OpChain.parent!_nextOp_eq =>
  BlockPtr.OpChain block ctx array,
  op.getParent! ctx, op.getNextOp! ctx, some block,
  (nextOp.getParent! ctx) where
    guard (op.getParent! ctx) = some block
    guard (op.getNextOp! ctx) = some nextOp

@[grind .]
theorem RegionPtr.BlockChain_unique :
    RegionPtr.BlockChain region ctx array →
    RegionPtr.BlockChain region ctx array' →
    array = array' := by
  intros hWf hWf'
  apply Array.ext_getElem?
  intros i
  induction i <;> grind [RegionPtr.BlockChain]

theorem RegionPtr.BlockChain_array_injective
    (hWF : RegionPtr.BlockChain region ctx array) :
    ∀ (i j : Nat) iInBounds jInBounds, i ≠ j → array[i]'iInBounds ≠ array[j]'jInBounds := by
  intros i
  induction i
  case zero => grind [RegionPtr.BlockChain]
  case succ i ih =>
    intros j
    cases j
    case zero => grind [RegionPtr.BlockChain]
    case succ j =>
      intros iInBounds jInBounds hNe
      grind [RegionPtr.BlockChain]

@[grind .]
theorem IRContext.empty_wellFormed [IsOpCode opInfo] :
    (IRContext.empty opInfo).WellFormed := by
  grind [IRContext.WellFormed]

theorem BlockPtr.OpChain_unchanged
    (hWf : blockPtr.OpChain ctx array missingOps)
    (blockPtrInBounds' : blockPtr.InBounds ctx')
    (hSameFirstOp : blockPtr.getFirstOp! ctx = blockPtr.getFirstOp! ctx')
    (hSameLastOp : blockPtr.getLastOp! ctx = blockPtr.getLastOp! ctx')
    (hSameOpFields : ∀ (opPtr : OperationPtr),
      opPtr.InBounds ctx →
      opPtr.getParent! ctx = some blockPtr →
        opPtr.InBounds ctx' ∧
        opPtr.getParent! ctx' = opPtr.getParent! ctx ∧
        opPtr.getPrevOp! ctx' = opPtr.getPrevOp! ctx ∧
        opPtr.getNextOp! ctx' = opPtr.getNextOp! ctx)
    (hSameOpFields' : ∀ (opPtr : OperationPtr),
      opPtr.InBounds ctx' →
      opPtr.getParent! ctx' = some blockPtr →
        opPtr.InBounds ctx ∧
        opPtr.getParent! ctx = opPtr.getParent! ctx') :
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
    (hSameFirst : regionPtr.getFirstBlock! ctx = regionPtr.getFirstBlock! ctx')
    (hSameLast : regionPtr.getLastBlock! ctx = regionPtr.getLastBlock! ctx')
    (hSameBlockFields : ∀ (blockPtr : BlockPtr),
      blockPtr.InBounds ctx →
      blockPtr.getParent! ctx = some regionPtr →
        blockPtr.InBounds ctx' ∧
        blockPtr.getParent! ctx' = blockPtr.getParent! ctx ∧
        blockPtr.getPrevBlock! ctx' = blockPtr.getPrevBlock! ctx ∧
        blockPtr.getNextBlock! ctx' = blockPtr.getNextBlock! ctx)
    (hSameBlockFields' : ∀ (blockPtr : BlockPtr),
      blockPtr.InBounds ctx' →
      blockPtr.getParent! ctx' = some regionPtr →
        blockPtr.InBounds ctx ∧
        blockPtr.getParent! ctx = blockPtr.getParent! ctx') :
    regionPtr.BlockChain ctx' array := by
  constructor <;> grind [RegionPtr.BlockChain]

theorem RegionPtr.BlockChain.prev_getElem_eq
    (hChain : RegionPtr.BlockChain region ctx array)
    {i : Nat} {hi : i < array.size} :
    array[i].getPrevBlock! ctx = if i = 0 then none else some array[i - 1] := by
  grind [RegionPtr.BlockChain]

grind_pattern RegionPtr.BlockChain.prev_getElem_eq =>
  RegionPtr.BlockChain region ctx array, array[i].getPrevBlock! ctx

theorem OperationPtr.WellFormed_unchanged
    (hWf : opPtr.WellFormed ctx opPtrInBounds)
    (hInBounds' : Operation.FieldsInBounds opPtr ctx' opPtrInBounds')
    (hSameNumOperands :
      opPtr.getNumOperands! ctx = opPtr.getNumOperands! ctx')
    (hSameOperandOwner :
      ∀ i, i < opPtr.getNumOperands! ctx →
      (opPtr.getOpOperand i).getOwner! ctx = (opPtr.getOpOperand i).getOwner! ctx')
    (hSameNumBlockOperands :
      opPtr.getNumSuccessors! ctx = opPtr.getNumSuccessors! ctx')
    (hSameBlockOperandOwner :
      ∀ i, i < opPtr.getNumSuccessors! ctx →
      (opPtr.getBlockOperand i).getOwner! ctx = (opPtr.getBlockOperand i).getOwner! ctx')
    (hSameNumResults :
      opPtr.getNumResults! ctx = opPtr.getNumResults! ctx')
    (hSameResultIndex :
      ∀ i, i < opPtr.getNumResults ctx opPtrInBounds →
      (opPtr.getResult i).getIndex! ctx = (opPtr.getResult i).getIndex! ctx')
    (hSameResultOwner :
      ∀ i, i < opPtr.getNumResults ctx opPtrInBounds →
      (opPtr.getResult i).getOwner! ctx = (opPtr.getResult i).getOwner! ctx')
    (hSameParent : opPtr.getParent! ctx = opPtr.getParent! ctx')
    (hSamePrev : opPtr.getPrevOp! ctx = opPtr.getPrevOp! ctx')
    (hSameNext : opPtr.getNextOp! ctx = opPtr.getNextOp! ctx')
    (hSameRegionParents :
      ∀ (regionPtr : RegionPtr), regionPtr.InBounds ctx →
        regionPtr.getParent! ctx = some opPtr →
        regionPtr.InBounds ctx' ∧ regionPtr.getParent! ctx = regionPtr.getParent! ctx')
    (hSameRegionParents' :
      ∀ (regionPtr : RegionPtr), regionPtr.InBounds ctx' →
        regionPtr.getParent! ctx' = some opPtr →
        regionPtr.InBounds ctx ∧ regionPtr.getParent! ctx = regionPtr.getParent! ctx')
    (hSameNumRegions :
      opPtr.getNumRegions! ctx = opPtr.getNumRegions! ctx')
    (hSameRegions :
      ∀ i, i < opPtr.getNumRegions! ctx → opPtr.getRegion! ctx i = opPtr.getRegion! ctx' i) :
    opPtr.WellFormed ctx' opPtrInBounds' := by
  constructor <;> grind [OperationPtr.WellFormed, Operation.FieldsInBounds]

theorem BlockPtr.WellFormed_unchanged
    (hWf : blockPtr.WellFormed ctx blockPtrInBounds)
    (hInBounds' : Block.FieldsInBounds blockPtr ctx' blockPtrInBounds')
    (hSameParent : blockPtr.getParent! ctx = blockPtr.getParent! ctx')
    (hSamePrev : blockPtr.getPrevBlock! ctx = blockPtr.getPrevBlock! ctx')
    (hSameNext : blockPtr.getNextBlock! ctx = blockPtr.getNextBlock! ctx')
    (hSameNumArguments : blockPtr.getNumArguments! ctx = blockPtr.getNumArguments! ctx')
    (hSameArgumentOwner :
      ∀ i, i < blockPtr.getNumArguments! ctx →
      (blockPtr.getArgument i).getOwner! ctx = (blockPtr.getArgument i).getOwner! ctx')
    (hSameArgumentIndex :
      ∀ i, i < blockPtr.getNumArguments ctx →
      (blockPtr.getArgument i).getIndex! ctx = (blockPtr.getArgument i).getIndex! ctx') :
    blockPtr.WellFormed ctx' blockPtrInBounds' := by
  constructor <;> grind [BlockPtr.WellFormed]

theorem RegionPtr.WellFormed_unchanged {regionPtr : RegionPtr}
    (hWf : regionPtr.WellFormed ctx)
    (hInBounds' : regionPtr.FieldsInBounds ctx')
    (hSameParentOp : regionPtr.getParent! ctx = regionPtr.getParent! ctx')
    (hSameNumRegions :
      ∀ parent, regionPtr.getParent! ctx = some parent →
      parent.getNumRegions! ctx = parent.getNumRegions! ctx')
    (hSameRegions :
      ∀ parent, regionPtr.getParent! ctx = some parent →
      ∀ i, i < parent.getNumRegions! ctx →
      parent.getRegion! ctx i = parent.getRegion! ctx' i) :
    regionPtr.WellFormed ctx' := by
  constructor <;> grind [RegionPtr.WellFormed]

theorem BlockPtr.operationListWF (ctx : IRContext OpInfo) (block : BlockPtr) (hblock : block.InBounds ctx)
  (hctx : ctx.WellFormed) :
    BlockPtr.OpChain block ctx (BlockPtr.operationList block ctx hctx hblock) :=
  Exists.choose_spec (hctx.opChain block hblock)

@[grind =]
theorem BlockPtr.operationList_iff_BlockPtr_OpChain :
    BlockPtr.OpChain block ctx array ↔
    BlockPtr.operationList block ctx hctx hblock = array := by
  grind [BlockPtr.operationListWF]

@[grind =_]
theorem BlockPtr.operationList.mem (h : op.InBounds ctx) :
    op.getParent! ctx = some block ↔
    op ∈ BlockPtr.operationList block ctx hctx hblock := by
  grind [BlockPtr.OpChain, BlockPtr.operationListWF]

@[grind .]
theorem RegionPtr.blockListWF (ctx : IRContext OpInfo) (region : RegionPtr)
    (hregion : region.InBounds ctx := by grind)
    (hctx : ctx.WellFormed := by grind) :
    RegionPtr.BlockChain region ctx (RegionPtr.blockList region ctx hctx hregion) :=
  Exists.choose_spec (hctx.blockChain region hregion)

@[grind =]
theorem RegionPtr.blockList_iff_RegionPtr_BlockChain :
    RegionPtr.BlockChain region ctx array ↔
    RegionPtr.blockList region ctx hctx hregion = array := by
  grind [RegionPtr.blockListWF]

@[grind =_]
theorem RegionPtr.blockList.mem :
    bl.getParent ctx blInBounds = some region ↔
    bl ∈ RegionPtr.blockList region ctx hctx hregion := by
  grind [RegionPtr.BlockChain, RegionPtr.blockListWF]

@[grind .]
theorem ValuePtr.defUseArrayWF {hctx : IRContext.WellFormed ctx missingUses missingBlockUses} :
    ValuePtr.DefUse value ctx (ValuePtr.defUseArray value ctx hctx hvalue) (missingUses.filter (fun use => use.getValue! ctx = value)) := by
  grind [ValuePtr.defUseArray, IRContext.WellFormed]

@[grind .]
theorem ValuePtr.defUseArray_iff_ValuePtr_DefUse {hctx : ctx.WellFormed missingUses missingBlockUses} :
    ValuePtr.DefUse value ctx array (missingUses.filter (fun use => use.getValue! ctx = value)) ↔
    ValuePtr.defUseArray value ctx hctx hvalue = array := by
  grind [ValuePtr.defUseArrayWF]

theorem ValuePtr.defUseArray_contains_operand_use
{hctx : IRContext.WellFormed ctx} (h : operand.InBounds ctx) :
    operand.getValue! ctx = value ↔
    operand ∈ ValuePtr.defUseArray value ctx hctx hvalue := by
  grind [ValuePtr.DefUse, ValuePtr.defUseArrayWF]

theorem OperationPtr.getParent_prev_eq
    (opInBounds : OperationPtr.InBounds opPtr ctx)
    (hopParent : OperationPtr.getParent! opPtr ctx = some block)
    (hblock : BlockPtr.OpChain block ctx array)
    (hprev : OperationPtr.getPrevOp! opPtr ctx = some prevOp) :
    prevOp.getParent! ctx = some block := by
  grind [BlockPtr.OpChain, Array.getElem?_of_mem]

theorem BlockPtr.OpChain_prev_ne
    (hop : OperationPtr.InBounds op ctx)
    (hctx : ctx.WellFormed)
    (hparent : op.getParent! ctx = some block) :
    block.OpChain ctx array →
    op.getPrevOp! ctx ≠ some op := by
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
    (hparent : op.getParent! ctx = some block) :
    block.OpChain ctx array →
    op.getNextOp! ctx ≠ some op := by
  intros hNe
  have := hctx.inBounds
  have ⟨array, harray⟩ := hctx.opChain block (by grind)
  have : op ∈ array := by grind
  intro heq
  have ⟨i, hi⟩ := Array.getElem?_of_mem this
  have : array[i + 1]? = some op := by grind
  grind [BlockPtr.OpChain_array_injective]

theorem ValuePtr.DefUse.hasUses!_iff
    (hWF : ValuePtr.DefUse value ctx array missingUses) :
    value.hasUses! ctx ↔ array ≠ #[] := by
  grind [DefUse, hasUses!_def]

theorem ValuePtr.DefUse.getFirstUse!_none_iff
    (hWF : ValuePtr.DefUse value ctx array missingUses) :
    value.getFirstUse! ctx = none ↔ array = #[] := by
  grind [DefUse]

theorem IRContext.WellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some
    {ctx : IRContext OpInfo} {op prevOp : OperationPtr} (hop : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    op.getPrevOp! ctx = some prevOp →
    prevOp.getNextOp! ctx = some op := by
  cases hparent : op.getParent! ctx
  case none =>
    grind [IRContext.WellFormed, OperationPtr.WellFormed.opChain_of_parent_none]
  case some parent =>
    intro hprev
    have ⟨array, harray⟩ := wf.opChain parent (by grind)
    have := BlockPtr.OpChain.allOpsInChain harray op (by grind) hparent
    have hop : op ∈ array := by grind
    have hprevOp : prevOp ∈ array := by grind [BlockPtr.OpChain]
    have ⟨i, hi⟩ := Array.getElem_of_mem hop
    cases i <;> grind [BlockPtr.OpChain]

theorem IRContext.WellFormed.OperationPtr_prev!_eq_some_of_next!_eq_some
    {ctx : IRContext OpInfo} {op nextOp : OperationPtr} (hop : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    op.getNextOp! ctx = some nextOp →
    nextOp.getPrevOp! ctx = some op := by
  cases hparent : op.getParent! ctx
  case none =>
    grind [IRContext.WellFormed, BlockPtr.OpChain, OperationPtr.WellFormed]
  case some parent =>
    intro hprev
    have ⟨array, harray⟩ := wf.opChain parent (by grind)
    grind [Array.getElem?_of_mem, BlockPtr.OpChain]

theorem IRContext.WellFormed.OperationPtr_parent!_ne_none_of_next!_ne_none
    {ctx : IRContext OpInfo} {op : OperationPtr} (hop : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    op.getNextOp! ctx ≠ none →
    op.getParent! ctx ≠ none := by
  grind [IRContext.WellFormed, OperationPtr.WellFormed]

grind_pattern IRContext.WellFormed.OperationPtr_parent!_ne_none_of_next!_ne_none =>
  ctx.WellFormed missingUses missingSuccessorUses, op.getNextOp! ctx, op.getParent! ctx

theorem IRContext.WellFormed.OperationPtr_parent!_ne_none_of_prev!_ne_none
    {ctx : IRContext OpInfo} {op : OperationPtr} (hop : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    op.getPrevOp! ctx ≠ none →
    op.getParent! ctx ≠ none := by
  grind [IRContext.WellFormed, OperationPtr.WellFormed]

grind_pattern IRContext.WellFormed.OperationPtr_parent!_ne_none_of_prev!_ne_none =>
  ctx.WellFormed missingUses missingSuccessorUses, op.getPrevOp! ctx, op.getParent! ctx

theorem IRContext.WellFormed.OpOperandPtr_value!_eq_of_back!_eq_valueFirstUse
    {ctx : IRContext OpInfo} (wf : ctx.WellFormed)
    {firstUse : OpOperandPtr} (firstUseInBounds : firstUse.InBounds ctx) :
    firstUse.getBack! ctx = .valueFirstUse value →
    firstUse.getValue! ctx = value := by
  have ⟨array, harray⟩ := wf.valueDefUseChains (firstUse.getValue! ctx) (by grind)
  have hMem : firstUse ∈ array := by grind [ValuePtr.DefUse]
  grind [ValuePtr.DefUse.value!_eq_of_back!_eq_valueFirstUse]

grind_pattern IRContext.WellFormed.OpOperandPtr_value!_eq_of_back!_eq_valueFirstUse =>
  ctx.WellFormed, firstUse.getBack! ctx, OpOperandPtrPtr.valueFirstUse value

theorem IRContext.WellFormed.OpOperandPtr_value_of_getFirstUse (wf : ctx.WellFormed)
    (valueInBounds : value.InBounds ctx) {firstUse : OpOperandPtr}
    (hFirstUse : value.getFirstUse! ctx = some firstUse) :
    firstUse.getValue! ctx = value := by
  have ⟨array, harray⟩ := wf.valueDefUseChains value (by grind)
  grind [ValuePtr.DefUse]

grind_pattern IRContext.WellFormed.OpOperandPtr_value_of_getFirstUse =>
  ctx.WellFormed, value.getFirstUse! ctx, some firstUse

theorem IRContext.WellFormed.ValuePtr_getFirstUse!_eq_of_back_eq_valueFirstUse
    {ctx : IRContext OpInfo} (wf : ctx.WellFormed) {firstUse : OpOperandPtr}
    (firstUseInBounds : firstUse.InBounds ctx)
    (heq : firstUse.getBack! ctx = .valueFirstUse value) :
    value.getFirstUse! ctx = some firstUse := by
  have ⟨array, harray⟩ := wf.valueDefUseChains value (by grind)
  have := @ValuePtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse
  grind [IRContext.WellFormed.OpOperandPtr_value!_eq_of_back!_eq_valueFirstUse, ValuePtr.DefUse]

grind_pattern IRContext.WellFormed.ValuePtr_getFirstUse!_eq_of_back_eq_valueFirstUse =>
  ctx.WellFormed, firstUse.getBack! ctx, OpOperandPtrPtr.valueFirstUse value

theorem IRContext.WellFormed.ValuePtr_hasUses_iff_operand_value_ne_value
    (ctxWf : ctx.WellFormed)
    {value : ValuePtr} (noUses : ¬ value.hasUses! ctx) (valueInBounds : value.InBounds ctx)
    {operand : OpOperandPtr} (hoperand : operand.InBounds ctx) :
    operand.getValue! ctx ≠ value := by
  grind [valueDefUseChains, ValuePtr.DefUse.hasUses!_iff, ValuePtr.DefUse]

grind_pattern IRContext.WellFormed.ValuePtr_hasUses_iff_operand_value_ne_value =>
  ctx.WellFormed, value.hasUses! ctx, operand.getValue! ctx

theorem BlockPtr.OpChain.mem_next!_of_mem
    (op nextOp : OperationPtr) (block : BlockPtr)
    (hWF : block.OpChain ctx array missingOps)
    (hnext : op.getNextOp! ctx = some nextOp)
    (hmem : op ∈ array) :
    nextOp ∈ array := by
  grind [BlockPtr.OpChain, Array.getElem_of_mem]

grind_pattern BlockPtr.OpChain.mem_next!_of_mem =>
  block.OpChain ctx array missingOps, op.getNextOp! ctx, some nextOp, op ∈ array

theorem BlockPtr.OpChain.mem_of_mem_next!
    (op nextOp : OperationPtr) (block : BlockPtr)
    (ctxWF : ctx.WellFormed)
    (hWF : block.OpChain ctx array)
    (hnext : op.getNextOp! ctx = some nextOp)
    (hop : op.InBounds ctx)
    (hmem : nextOp ∈ array) :
    op ∈ array := by
  cases hparent : (op.getParent! ctx); grind
  rename_i block'
  have ⟨array', harray'⟩ := ctxWF.opChain block' (by grind)
  grind

grind_pattern BlockPtr.OpChain.mem_of_mem_next! =>
  ctx.WellFormed, block.OpChain ctx array, op.getNextOp! ctx, some nextOp, nextOp ∈ array

theorem OperationPtr.parent!_next
    (op nextOp : OperationPtr)
    (hWF : ctx.WellFormed)
    (opInBounds : op.InBounds ctx)
    (hnext : op.getNextOp! ctx = some nextOp)
    (hparent : nextOp.getParent! ctx = some block) :
    op.getParent! ctx = some block := by
  have ⟨array, harray⟩ := hWF.opChain block (by grind)
  have : nextOp ∈ array := by grind
  grind

grind_pattern OperationPtr.parent!_next =>
  ctx.WellFormed, op.getNextOp! ctx, nextOp.getParent! ctx,
  op.getParent! ctx, some block where
  guard (op.getNextOp! ctx) = some nextOp
  guard (nextOp.getParent! ctx) = some block

theorem IRContext.WellFormed.BlockPtr_next!_eq_some_of_prev!_eq_some
    {ctx : IRContext OpInfo} {bl prevBl : BlockPtr} (hbl : bl.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    bl.getPrevBlock! ctx = some prevBl →
    prevBl.getNextBlock! ctx = some bl := by
  cases hparent : bl.getParent! ctx
  case none =>
    grind [IRContext.WellFormed, RegionPtr.BlockChain, BlockPtr.WellFormed]
  case some parent =>
    intro hprev
    have ⟨array, harray⟩ := wf.blockChain parent (by grind)
    grind [Array.getElem?_of_mem, RegionPtr.BlockChain]

grind_pattern IRContext.WellFormed.BlockPtr_next!_eq_some_of_prev!_eq_some =>
  ctx.WellFormed missingUses missingSuccessorUses, bl.getPrevBlock! ctx, some prevBl, prevBl.getNextBlock! ctx

theorem IRContext.WellFormed.BlockPtr_prev!_eq_some_of_next!_eq_some
    {ctx : IRContext OpInfo} {bl nextBl : BlockPtr} (hbl : bl.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    bl.getNextBlock! ctx = some nextBl →
    nextBl.getPrevBlock! ctx = some bl := by
  cases hparent : bl.getParent! ctx
  case none =>
    grind [IRContext.WellFormed, RegionPtr.BlockChain, BlockPtr.WellFormed]
  case some parent =>
    intro hnext
    have ⟨array, harray⟩ := wf.blockChain parent (by grind)
    grind [Array.getElem?_of_mem, RegionPtr.BlockChain]

grind_pattern IRContext.WellFormed.BlockPtr_prev!_eq_some_of_next!_eq_some =>
  ctx.WellFormed missingUses missingSuccessorUses, bl.getNextBlock! ctx, some nextBl, nextBl.getPrevBlock! ctx

theorem IRContext.WellFormed.BlockPtr_parent!_ne_none_of_next!_ne_none
    {bl : BlockPtr} (hbl : bl.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    bl.getNextBlock! ctx ≠ none →
    bl.getParent! ctx ≠ none := by
  grind [IRContext.WellFormed, BlockPtr.WellFormed]

grind_pattern IRContext.WellFormed.BlockPtr_parent!_ne_none_of_next!_ne_none =>
  ctx.WellFormed missingUses missingSuccessorUses, bl.getNextBlock! ctx, bl.getParent! ctx

theorem IRContext.WellFormed.BlockPtr_parent!_ne_none_of_prev!_ne_none
    {bl : BlockPtr} (hbl : bl.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    bl.getPrevBlock! ctx ≠ none →
    bl.getParent! ctx ≠ none := by
  grind [IRContext.WellFormed, BlockPtr.WellFormed]

grind_pattern IRContext.WellFormed.BlockPtr_parent!_ne_none_of_prev!_ne_none =>
  ctx.WellFormed missingUses missingSuccessorUses, bl.getPrevBlock! ctx, bl.getParent! ctx

@[grind <=]
theorem IRContext.WellFormed.exists_parent!_eq_some_of_next!_eq_some
    {bl : BlockPtr} (hbl : bl.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses)
    (hnext : bl.getNextBlock! ctx = some nextBl) :
    ∃ parent, bl.getParent! ctx = some parent := by
  have := IRContext.WellFormed.BlockPtr_parent!_ne_none_of_next!_ne_none hbl wf (by grind)
  have := (Option.ne_none_iff_exists.mp this)
  grind

@[grind <=]
theorem IRContext.WellFormed.exists_parent!_eq_some_of_prev!_eq_some
    {bl : BlockPtr} (hbl : bl.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses)
    (hprev : bl.getPrevBlock! ctx = some prevBl) :
    ∃ parent, bl.getParent! ctx = some parent := by
  have := IRContext.WellFormed.BlockPtr_parent!_ne_none_of_prev!_ne_none hbl wf (by grind)
  have := (Option.ne_none_iff_exists.mp this)
  grind

theorem IRContext.WellFormed.firstOp!_eq_some_iff
    {block : BlockPtr} (blockInBounds : block.InBounds ctx)
    {op : OperationPtr} (opInBounds : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    block.getFirstOp! ctx = some op ↔
    (op.getParent! ctx = some block ∧ op.getPrevOp! ctx = none) := by
  constructor
  · grind [IRContext.WellFormed, BlockPtr.OpChain.prev!_eq_none_iff_firstOp!_eq_self]
  · have ⟨array, harray⟩ := wf.opChain block (by grind)
    grind [BlockPtr.OpChain.prev!_eq_none_iff_firstOp!_eq_self]

grind_pattern IRContext.WellFormed.firstOp!_eq_some_iff =>
  ctx.WellFormed missingUses missingSuccessorUses, block.getFirstOp! ctx, some op

grind_pattern IRContext.WellFormed.firstOp!_eq_some_iff =>
  ctx.WellFormed missingUses missingSuccessorUses, op.getParent! ctx, some block,
  op.getPrevOp! ctx

theorem IRContext.WellFormed.lastOp!_eq_some_iff
    {block : BlockPtr} (blockInBounds : block.InBounds ctx)
    {op : OperationPtr} (opInBounds : op.InBounds ctx)
    (wf : ctx.WellFormed missingUses missingSuccessorUses) :
    block.getLastOp! ctx = some op ↔
    (op.getParent! ctx = some block ∧ op.getNextOp! ctx = none) := by
  constructor
  · grind [IRContext.WellFormed, BlockPtr.OpChain.next!_eq_none_iff_lastOp!_eq_self]
  · have ⟨array, harray⟩ := wf.opChain block (by grind)
    grind [BlockPtr.OpChain.next!_eq_none_iff_lastOp!_eq_self]

grind_pattern IRContext.WellFormed.lastOp!_eq_some_iff =>
  ctx.WellFormed missingUses missingSuccessorUses, block.getLastOp! ctx, some op

grind_pattern IRContext.WellFormed.lastOp!_eq_some_iff =>
  ctx.WellFormed missingUses missingSuccessorUses, op.getParent! ctx, some block,
  op.getPrevOp! ctx

theorem RegionPtr.BlockChain.mem_next!_of_mem
    (bl nextBl : BlockPtr) (region : RegionPtr)
    (hWF : region.BlockChain ctx array)
    (hnext : bl.getNextBlock! ctx = some nextBl)
    (hmem : bl ∈ array) :
    nextBl ∈ array := by
  grind [RegionPtr.BlockChain, Array.getElem_of_mem]

grind_pattern RegionPtr.BlockChain.mem_next!_of_mem =>
  region.BlockChain ctx array, bl.getNextBlock! ctx, some nextBl, bl ∈ array

theorem RegionPtr.BlockChain.mem_prev!_of_mem
    (bl prevBl : BlockPtr) (region : RegionPtr)
    (hWF : region.BlockChain ctx array)
    (hprev : bl.getPrevBlock! ctx = some prevBl)
    (hmem : bl ∈ array) :
    prevBl ∈ array := by
  have ⟨i, hi, harray⟩ := Array.getElem_of_mem hmem
  grind

grind_pattern RegionPtr.BlockChain.mem_prev!_of_mem =>
  region.BlockChain ctx array, bl.getPrevBlock! ctx, some prevBl, bl ∈ array

theorem RegionPtr.BlockChain.mem_of_mem_next!
    (bl nextBl : BlockPtr) (region : RegionPtr)
    (ctxWF : ctx.WellFormed)
    (hWF : region.BlockChain ctx array)
    (hnext : bl.getNextBlock! ctx = some nextBl)
    (hbl : bl.InBounds ctx)
    (hmem : nextBl ∈ array) :
    bl ∈ array := by
  cases hparent : (bl.getParent! ctx); grind
  rename_i region'
  have : region = region' := by grind [RegionPtr.BlockChain, Array.getElem_of_mem]
  have ⟨array', harray'⟩ := ctxWF.blockChain region' (by grind)
  grind

grind_pattern RegionPtr.BlockChain.mem_of_mem_next! =>
  ctx.WellFormed, region.BlockChain ctx array, bl.getNextBlock! ctx, some nextBl, nextBl ∈ array

theorem BlockPtr.parent!_next {bl : BlockPtr}
    (blInBounds : bl.InBounds ctx) (hctx : ctx.WellFormed missingUses missingSuccessorUses)
    (hnext : bl.getNextBlock! ctx = some nextBl) :
    bl.getParent! ctx = nextBl.getParent! ctx := by
  intros
  have ⟨parent, hparent⟩ : ∃ region, bl.getParent! ctx = some region := by grind
  have ⟨array, harray⟩ := hctx.blockChain parent (by grind)
  have : bl ∈ array := by grind [RegionPtr.BlockChain]
  grind [RegionPtr.BlockChain]

grind_pattern BlockPtr.parent!_next =>
  ctx.WellFormed missingUses missingSuccessorUses, bl.getNextBlock! ctx, some nextBl

theorem BlockPtr.parent!_prev {bl : BlockPtr}
    (blInBounds : bl.InBounds ctx) (hctx : ctx.WellFormed missingUses missingSuccessorUses)
    (hprev : bl.getPrevBlock! ctx = some prevBl) :
    bl.getParent! ctx = prevBl.getParent! ctx := by
  intros
  have ⟨parent, hparent⟩ : ∃ region, bl.getParent! ctx = some region := by grind
  have ⟨array, harray⟩ := hctx.blockChain parent (by grind)
  have : bl ∈ array := by grind [RegionPtr.BlockChain]
  grind [RegionPtr.BlockChain]

grind_pattern BlockPtr.parent!_prev =>
  ctx.WellFormed missingUses missingSuccessorUses, bl.getPrevBlock! ctx, some prevBl

theorem RegionPtr.firstBlock!_parent! {reg : RegionPtr}
    (regInBounds : reg.InBounds ctx) (hctx : ctx.WellFormed missingUses missingSuccessorUses)
    (hfirst : reg.getFirstBlock! ctx = some firstBl) :
    firstBl.getParent! ctx = some reg := by
  have ⟨array, harray⟩ := hctx.blockChain reg (by grind)
  grind [RegionPtr.BlockChain]

grind_pattern RegionPtr.firstBlock!_parent! =>
    ctx.WellFormed missingUses missingSuccessorUses, reg.getFirstBlock! ctx, some firstBl,
    (firstBl.getParent! ctx) where
  guard (reg.getFirstBlock! ctx) = some firstBl

theorem RegionPtr.lastBlock!_parent! {reg : RegionPtr}
    (regInBounds : reg.InBounds ctx) (hctx : ctx.WellFormed missingUses missingSuccessorUses)
    (hlast : reg.getLastBlock! ctx = some lastBl) :
    lastBl.getParent! ctx = some reg := by
  have ⟨array, harray⟩ := hctx.blockChain reg (by grind)
  grind [RegionPtr.BlockChain]

grind_pattern RegionPtr.lastBlock!_parent! =>
  ctx.WellFormed missingUses missingSuccessorUses, reg.getLastBlock! ctx, some lastBl,
  lastBl.getParent! ctx

@[grind .]
theorem OperationPtr.idxInParent_lt_size_operationList
    (op : OperationPtr) (ctx : IRContext OpInfo) (block : BlockPtr)
    (hasParent : op.getParent! ctx = some block)
    (hop : op.InBounds ctx)
    (hctx : ctx.WellFormed) :
    op.idxInParent ctx hop hctx <
      (block.operationList ctx hctx (by grind)).size := by
  grind [OperationPtr.idxInParent]

theorem OperationPtr.idxInParent_next_eq
    (op : OperationPtr) (ctx : IRContext OpInfo) (nextOp : OperationPtr)
    (hnext : op.getNextOp! ctx = some nextOp)
    (hnextOp : nextOp.InBounds ctx)
    (hop : op.InBounds ctx)
    (hctx : ctx.WellFormed) :
    nextOp.idxInParent ctx hnextOp hctx =
      op.idxInParent ctx hop hctx + 1 := by
  simp only [OperationPtr.idxInParent]
  split
  next block nextParent =>
    split
    next block' opParent =>
      have : block = block' := by grind
      subst block'
      have ⟨array, harray⟩ := hctx.opChain block (by grind)
      grind [BlockPtr.OpChain.idxOf_getElem_array, BlockPtr.OpChain]
    next opParent => grind
  next nextParent =>
    split
    next block opParent =>
      have ⟨array, harray⟩ := hctx.opChain block (by grind)
      grind
    next opParent => grind

grind_pattern OperationPtr.idxInParent_next_eq =>
  nextOp.idxInParent ctx hnextOp hctx, op.getNextOp! ctx, some nextOp

theorem OperationPtr.idxInParentFromTail_next_eq
    (op : OperationPtr) (ctx : IRContext OpInfo) (nextOp : OperationPtr)
    (hnext : op.getNextOp! ctx = some nextOp)
    (hnextOp : nextOp.InBounds ctx)
    (hop : op.InBounds ctx)
    (hctx : ctx.WellFormed) :
    nextOp.idxInParentFromTail ctx hnextOp hctx =
      op.idxInParentFromTail ctx hop hctx - 1 := by
  simp only [OperationPtr.idxInParentFromTail]
  simp only [OperationPtr.idxInParent_next_eq op ctx nextOp hnext hnextOp hop]
  split; grind
  split; rotate_left; grind
  rename_i nextParent block opParent
  have ⟨array, harray⟩ := hctx.opChain block (by grind)
  grind

grind_pattern OperationPtr.idxInParentFromTail_next_eq =>
  nextOp.idxInParentFromTail ctx hnextOp hctx, op.getNextOp! ctx, some nextOp, ctx.WellFormed, op.InBounds ctx

theorem OperationPtr.idxInParentFromTail_next_ne_zero
    (op : OperationPtr) (ctx : IRContext OpInfo) (nextOp : OperationPtr)
    (hnext : op.getNextOp! ctx = some nextOp)
    (hop : op.InBounds ctx)
    (hctx : ctx.WellFormed) :
    op.idxInParentFromTail ctx hop hctx ≠ 0 := by
  simp only [OperationPtr.idxInParentFromTail]
  split; rotate_left; grind
  rename_i block hblock
  have : nextOp.getParent! ctx = some block := by grind [IRContext.WellFormed]
  have := OperationPtr.idxInParent_lt_size_operationList nextOp ctx block (by grind) (by grind) hctx
  grind

grind_pattern OperationPtr.idxInParentFromTail_next_ne_zero =>
  op.idxInParentFromTail ctx hop hctx, op.getNextOp! ctx, some nextOp, ctx.WellFormed, op.InBounds ctx

theorem OperationPtr.idxInParentFromTail_next_lt_idxInParentFromTail
    (op : OperationPtr) (ctx : IRContext OpInfo) (nextOp : OperationPtr)
    (hnext : op.getNextOp! ctx = some nextOp)
    (hnextOp : nextOp.InBounds ctx)
    (hop : op.InBounds ctx)
    (hctx : ctx.WellFormed) :
    nextOp.idxInParentFromTail ctx hnextOp hctx <
      op.idxInParentFromTail ctx hop hctx := by
  simp only [OperationPtr.idxInParentFromTail_next_eq op ctx nextOp hnext hnextOp hop]
  grind

grind_pattern OperationPtr.idxInParentFromTail_next_eq =>
  nextOp.idxInParentFromTail ctx hnextOp hctx, op.getNextOp! ctx, some nextOp, ctx.WellFormed, op.InBounds ctx

/--
  Prove preservation of the `region_parent` field of `OperationPtr.WellFormed`, if
  region parents, number of regions, and region pointers are unchanged in the
  new context.
-/
theorem OperationPtr.WellFormed.region_parent.unchanged
    {opPtr : OperationPtr} {ctx ctx' : IRContext OpInfo}
    (h_getRegion : opPtr.getRegion! ctx' = opPtr.getRegion! ctx)
    (h_numRegions : opPtr.getNumRegions! ctx' = opPtr.getNumRegions! ctx)
    (h_parent : region.getParent! ctx' = region.getParent! ctx)
    (_h_inBounds : region.InBounds ctx)
    (h_wf : (∃ i, i < opPtr.getNumRegions! ctx ∧ opPtr.getRegion! ctx i = region) ↔
             region.getParent! ctx = some opPtr) :
    (∃ i, i < opPtr.getNumRegions! ctx' ∧ opPtr.getRegion! ctx' i = region) ↔
    region.getParent! ctx' = some opPtr := by
  simp only [h_getRegion, h_numRegions, h_parent, h_wf]

/--
  An IR context that also carries its well-formedness proof.
  This is the type that users are expected to work with most of the time, unless they
  need to explicitly break the well-formedness invariant during a transformation.
-/
structure WfIRContext (OpInfo : Type) [IsOpCode OpInfo] where
  raw : IRContext OpInfo
  wellFormed : raw.WellFormed

public instance {OpInfo} [IsOpCode OpInfo] :
    Coe (WfIRContext OpInfo) (IRContext OpInfo) where
  coe wfCtx := wfCtx.raw

@[grind! .]
theorem WfIRContext_raw_wellFormed (wfCtx : WfIRContext OpInfo) :
    (wfCtx.raw).WellFormed := by
  grind [WfIRContext]

instance instWfIRContextInhabited {OpInfo} [IsOpCode OpInfo] :
    Inhabited (WfIRContext OpInfo) where
  default := ⟨IRContext.empty OpInfo, IRContext.empty_wellFormed⟩

end Veir
