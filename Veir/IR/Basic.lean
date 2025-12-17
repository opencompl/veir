module

public import Std.Data.HashMap
public import Veir.Prelude
open Std (HashMap)

public section

namespace Mlir

abbrev OperationPtr := Nat
abbrev BlockPtr := Nat
abbrev RegionPtr := Nat
abbrev Location := Unit
abbrev MlirType := Unit
abbrev AttrDictionary := Unit

/-
- A pointer to an operation result.
-/
structure OpResultPtr where
  op: OperationPtr
  index: Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/-
- A pointer to an operation operand.
-/
structure OpOperandPtr where
  op: OperationPtr
  index: Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/-
- A pointer to an operation block operand.
-/
structure BlockOperandPtr where
  op: OperationPtr
  index: Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/-
- A pointer to a block argument.
-/
structure BlockArgumentPtr where
  block: BlockPtr
  index: Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/-
- The base class for operation results and block arguments.
-/
structure ValueImpl where
  -- This is used to distinguish between OpResult and BlockArgument
  type: MlirType
  firstUse: Option OpOperandPtr
deriving Inhabited, Repr, Hashable

/-
- The definition of an operation result.
-/
structure OpResult extends ValueImpl where
  index: Nat
  -- Should be computed from index and the layout
  owner: OperationPtr
deriving Inhabited, Repr, Hashable

/-
- The definition of a block argument.
-/
structure BlockArgument extends ValueImpl where
  index: Nat
  loc: Location
  owner: BlockPtr
deriving Inhabited, Repr, Hashable

/-
- An MLIR SSA value.
- A value is either an operation result, or a block argument.
-/
inductive ValuePtr where
  | opResult (ptr: OpResultPtr)
  | blockArgument (ptr: BlockArgumentPtr)
deriving Inhabited, Repr, DecidableEq, Hashable

-- As in MLIR, an OpResultPtr can be coerced to a ValuePtr
instance : Coe OpResultPtr ValuePtr where
  coe ptr := ValuePtr.opResult ptr

-- As in MLIR, a BlockArgumentPtr can be coerced to a ValuePtr
instance : Coe BlockArgumentPtr ValuePtr where
  coe ptr := ValuePtr.blockArgument ptr

/-
- A pointer to an operation operand pointer.
- This is used for the encoding of the use-def chain.
- It is either pointing to the next use field of the previous operand,
- or to the first use field of a value definition.
-/
inductive OpOperandPtrPtr where
  | operandNextUse (ptr: OpOperandPtr)
  | valueFirstUse (ptr: ValuePtr)
deriving Inhabited, Repr, DecidableEq, Hashable

/-
- An operand definition.
- It contains a pointer to the SSA value it uses, and links to the previous
- and next use of that value.
-/
structure OpOperand where
  nextUse: Option OpOperandPtr
  -- I am not sure why, but some parts of MLIR consider this to be an optional.
  -- i.e., the `IROperandBase::removeFromCurrent` method checks for null.
  back: OpOperandPtrPtr
  owner: OperationPtr
  value: ValuePtr
deriving Inhabited, Repr, Hashable

/-
- A pointer to an operation block operand pointer.
- This is used for the encoding of the use-def chain for block operands.
- It is either pointing to the next use field of the previous block operand,
- or to the first use field of a block.
-/
inductive BlockOperandPtrPtr where
  | blockOperandNextUse (ptr: BlockOperandPtr)
  | blockFirstUse (ptr: BlockPtr)
deriving Inhabited, Repr, Hashable, DecidableEq

/-
- A block operand definition.
- It contains a pointer to the block it uses, and links to the previous
- and next use of that block.
-/
structure BlockOperand where
  nextUse: Option BlockOperandPtr
  back: BlockOperandPtrPtr
  owner: OperationPtr
  value: BlockPtr
deriving Inhabited, Repr, Hashable

/-
- An MLIR operation.
-/
structure Operation where
  results: Array OpResult
  -- This is the operation pointer start
  prev: Option OperationPtr
  next: Option OperationPtr
  parent: Option BlockPtr
  -- We do not support those features yet:
  -- location: Location
  -- orderIndex: Nat
  opType: Nat
  attrs: AttrDictionary
  -- This should be replaced with an arbitrary user object
  properties: UInt64
  blockOperands: Array BlockOperand
  regions: Array RegionPtr
  operands: Array OpOperand
deriving Inhabited, Repr, Hashable

theorem Operation.default_operands_eq : (default : Operation).operands = #[] := by rfl
theorem Operation.default_regions_eq : (default : Operation).regions = #[] := by rfl
theorem Operation.default_blockOperands_eq : (default : Operation).blockOperands = #[] := by rfl
theorem Operation.default_results_eq : (default : Operation).results = #[] := by rfl

/-
- An MLIR block.
-/
structure Block where
  firstUse: Option BlockOperandPtr
  prev: Option BlockPtr
  next: Option BlockPtr
  parent: Option RegionPtr
  -- validOpOrder: Bool      -- Unsupported yet
  firstOp: Option OperationPtr
  lastOp: Option OperationPtr
  arguments: Array BlockArgument
deriving Inhabited, Repr, Hashable

theorem Block.default_arguments_eq : (default : Block).arguments = #[] := by rfl

/-
- An MLIR region.
-/
structure Region where
  firstBlock: Option BlockPtr
  lastBlock: Option BlockPtr
  parent: Option OperationPtr
deriving Inhabited, Repr, Hashable

/-
- The owning context of an MLIR module.
- It contains a top-level Module operation, and a maps from pointers to
- operations, blocks, and regions.
-/
structure IRContext where
  operations: HashMap OperationPtr Operation
  blocks: HashMap BlockPtr Block
  regions: HashMap RegionPtr Region
  topLevelOp: OperationPtr
  nextID: Nat
deriving Inhabited, Repr

/- Empty objects. -/

@[expose]
def Operation.empty (opType: Nat) : Operation :=
  { results := #[]
    prev := none
    next := none
    parent := none
    opType := opType
    attrs := ()
    properties := 0
    blockOperands := #[]
    regions := #[]
    operands := #[]
  }

@[expose]
def Region.empty : Region :=
  {
    parent := none
    firstBlock := none
    lastBlock := none
  }

@[expose]
def Block.empty : Block :=
  {
    arguments := #[]
    firstUse := none
    prev := none
    next := none
    parent := none
    firstOp := none
    lastOp := none
  }

/-
 OperationPtr accessors
-/

@[local grind]
def OperationPtr.InBounds (op: OperationPtr) (ctx: IRContext) : Prop :=
  op ∈ ctx.operations

def OperationPtr.get (ptr: OperationPtr) (ctx: IRContext) (inBounds: ptr.InBounds ctx := by grind) : Operation :=
  ctx.operations[ptr]'(by unfold InBounds at inBounds; grind)

def OperationPtr.get! (ptr: OperationPtr) (ctx: IRContext) : Operation :=
  ctx.operations[ptr]!
@[grind _=_]
theorem OperationPtr.get!_eq_get {ptr : OperationPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = (ptr.get ctx hin) := by
  grind [get, get!, InBounds]

def OperationPtr.getOpType (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx) : Nat :=
  (op.get ctx (by grind)).opType

def OperationPtr.getNumOperands (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).operands.size

def OperationPtr.getNumOperands! (op: OperationPtr) (ctx: IRContext) : Nat :=
  (op.get! ctx).operands.size

@[grind _=_]
theorem OperationPtr.getNumOperands!_eq_getNumOperands {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumOperands! ctx = op.getNumOperands ctx (by grind) := by
  grind [getNumOperands, getNumOperands!]

theorem OperationPtr.getNumOperands!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumOperands! ctx = op.getNumOperands! ctx' := by
  grind [OperationPtr.getNumOperands!]

def OperationPtr.getOpOperand (op: OperationPtr) (index: Nat) : OpOperandPtr :=
  { op := op, index := index }

@[simp, grind =]
theorem OperationPtr.getOpOperand_index {op : OperationPtr} {index : Nat} :
    (OperationPtr.getOpOperand op index).index = index := by
  grind [getOpOperand]

@[simp, grind =]
theorem OperationPtr.getOpOperand_op {op : OperationPtr} {index : Nat} :
    (OperationPtr.getOpOperand op index).op = op := by
  grind [getOpOperand]

def OperationPtr.getOperand (op: OperationPtr) (ctx: IRContext) (index: Nat)
    (inBounds: op.InBounds ctx := by grind) (h: index < getNumOperands op ctx inBounds := by grind) : ValuePtr :=
  ((op.get ctx (by grind)).operands[index]'(by grind [getNumOperands])).value

def OperationPtr.getOperand! (op: OperationPtr) (ctx: IRContext) (index: Nat) : ValuePtr :=
  ((op.get! ctx).operands[index]!).value

@[grind _=_]
theorem OperationPtr.getOperand!_eq_getOperand {op : OperationPtr} {index : Nat}
    {hin} (h: index < op.getNumOperands ctx hin) {hin'} :
    op.getOperand! ctx index = op.getOperand ctx index hin' h := by
  grind [getOperand, getOperand!]

def OperationPtr.getNumSuccessors (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).blockOperands.size

def OperationPtr.getNumSuccessors! (op: OperationPtr) (ctx: IRContext) : Nat :=
  (op.get! ctx).blockOperands.size

@[grind _=_]
theorem OperationPtr.getNumSuccessors!_eq_getNumSuccessors {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumSuccessors! ctx = op.getNumSuccessors ctx (by grind) := by
  grind [getNumSuccessors, getNumSuccessors!]

theorem OperationPtr.getNumSuccessors!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumSuccessors! ctx = op.getNumSuccessors! ctx' := by
  grind [OperationPtr.getNumSuccessors!]

def OperationPtr.getBlockOperand (op: OperationPtr) (index: Nat) : BlockOperandPtr :=
  { op := op, index := index }

@[simp, grind =]
theorem OperationPtr.getBlockOperand_index {op : OperationPtr} {index : Nat} :
    (OperationPtr.getBlockOperand op index).index = index := by
  grind [getBlockOperand]

@[simp, grind =]
theorem OperationPtr.getBlockOperand_op {op : OperationPtr} {index : Nat} :
    (OperationPtr.getBlockOperand op index).op = op := by
  grind [getBlockOperand]

def OperationPtr.getSuccessor (op: OperationPtr) (ctx: IRContext) (index: Nat)
    (inBounds: op.InBounds ctx := by grind) (h: index < getNumSuccessors op ctx inBounds := by grind) : BlockPtr :=
  ((op.get ctx (by grind)).blockOperands[index]'(by grind [getNumSuccessors])).value

def OperationPtr.getSuccessor! (op: OperationPtr) (ctx: IRContext) (index: Nat) : BlockPtr :=
  ((op.get! ctx).blockOperands[index]!).value

@[grind _=_]
theorem OperationPtr.getSuccessor!_eq_getSuccessor {op : OperationPtr} {index : Nat}
    {hin} (h: index < op.getNumSuccessors ctx hin) {hin'} :
    op.getSuccessor! ctx index = op.getSuccessor ctx index hin' h := by
  grind [getSuccessor, getSuccessor!]

def OperationPtr.getNumResults (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).results.size

def OperationPtr.getNumResults! (op: OperationPtr) (ctx: IRContext) : Nat :=
  (op.get! ctx).results.size

@[grind _=_]
theorem OperationPtr.getNumResults!_eq_getNumResults {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumResults! ctx = op.getNumResults ctx (by grind) := by
  grind [getNumResults, getNumResults!]

theorem OperationPtr.getNumResults!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumResults! ctx = op.getNumResults! ctx' := by
  grind [OperationPtr.getNumResults!]

def OperationPtr.getResult (op: OperationPtr) (index: Nat) : OpResultPtr :=
  { op := op, index := index }

@[simp, grind =]
theorem OperationPtr.getResult_index {op : OperationPtr} {index : Nat} :
    (OperationPtr.getResult op index).index = index := by
  grind [getResult]

@[simp, grind =]
theorem OperationPtr.getResult_op {op : OperationPtr} {index : Nat} :
    (OperationPtr.getResult op index).op = op := by
  grind [getResult]

def OperationPtr.getNumRegions (op: OperationPtr) (ctx: IRContext)
    (inBounds: op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).regions.size

def OperationPtr.getNumRegions! (op: OperationPtr) (ctx: IRContext) : Nat :=
  (op.get! ctx).regions.size

@[grind _=_]
theorem OperationPtr.getNumRegions!_eq_getNumRegions {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumRegions! ctx = op.getNumRegions ctx (by grind) := by
  grind [getNumRegions, getNumRegions!]

theorem OperationPtr.getNumRegions!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumRegions! ctx = op.getNumRegions! ctx' := by
  grind [OperationPtr.getNumRegions!]

def OperationPtr.getRegion (op: OperationPtr) (ctx: IRContext) (index: Nat)
  (inBounds: op.InBounds ctx := by grind) (iInBounds: index < op.getNumRegions ctx inBounds := by grind) : RegionPtr :=
  (op.get ctx (by grind)).regions[index]'(by grind [getNumRegions])

@[grind funCC]
def OperationPtr.getRegion! (op: OperationPtr) (ctx: IRContext) (index: Nat) : RegionPtr :=
  (op.get! ctx).regions[index]!

@[grind _=_]
theorem OperationPtr.getRegion!_eq_getRegion {op : OperationPtr} {index : Nat}
    {hin} (iInBounds : index < op.getNumRegions ctx hin) {hin'} :
    op.getRegion! ctx index = op.getRegion ctx index hin' iInBounds := by
  grind [getRegion, getRegion!]

theorem OperationPtr.getRegion!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getRegion! ctx = op.getRegion! ctx' := by
  grind [OperationPtr.get!, OperationPtr.getRegion!]

def OperationPtr.set (ptr: OperationPtr) (ctx: IRContext) (newOp: Operation) : IRContext :=
  {ctx with operations := ctx.operations.insert ptr newOp}

def OperationPtr.setNextOp (op: OperationPtr) (ctx: IRContext) (newNext : Option OperationPtr)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx
  op.set ctx { oldOp with next := newNext}

def OperationPtr.setPrevOp (op: OperationPtr) (ctx: IRContext) (newPrev: Option OperationPtr)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with prev := newPrev}

def OperationPtr.setParent (op: OperationPtr) (ctx: IRContext) (newParent: Option BlockPtr)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with parent := newParent}

def OperationPtr.setRegions (op: OperationPtr) (ctx: IRContext) (newRegions: Array RegionPtr)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with regions := newRegions}

def OperationPtr.setResults (op: OperationPtr) (ctx: IRContext) (newResults: Array OpResult)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with results := newResults}

def OperationPtr.pushResult (op : OperationPtr) (ctx : IRContext) (resultS : OpResult)
      (hop : op.InBounds ctx := by grind) :=
    op.setResults ctx ((op.get ctx).results.push resultS)

def OperationPtr.setOperands (op: OperationPtr) (ctx: IRContext) (newOperands: Array OpOperand)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with operands := newOperands}

def OperationPtr.pushOperand (op : OperationPtr) (ctx : IRContext) (operandS : OpOperand)
      (hop : op.InBounds ctx := by grind) :=
    op.setOperands ctx ((op.get ctx).operands.push operandS)

def OperationPtr.setProperties (op: OperationPtr) (ctx: IRContext) (newValue: UInt64)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with properties := newValue }

@[grind]
def OperationPtr.nextOperand (op : OperationPtr) (ctx : IRContext)
    (inBounds: op.InBounds ctx := by grind) : OpOperandPtr :=
  .mk op (op.getNumOperands ctx (by grind))

@[grind]
def OperationPtr.nextResult (op : OperationPtr) (ctx : IRContext)
    (inBounds: op.InBounds ctx := by grind) : OpResultPtr :=
  .mk op (op.getNumResults ctx (by grind))

def OperationPtr.allocEmpty (ctx : IRContext) (opType : Nat) : Option (IRContext × OperationPtr) :=
  let newOpPtr : OperationPtr := ctx.nextID
  let operation := Operation.empty opType
  if _ : ctx.operations.contains newOpPtr then none else
  let ctx := { ctx with nextID := ctx.nextID + 1 }
  let ctx := newOpPtr.set ctx operation
  (ctx, newOpPtr)


/-
 OpOperandPtr accessors
-/

@[local grind]
def OpOperandPtr.InBounds (operand: OpOperandPtr) (ctx: IRContext) : Prop :=
  ∃ h, operand.index < (operand.op.get ctx h).operands.size

theorem OpOperandPtr.inBounds_def : InBounds opr ctx ↔ ∃ h, opr.index < opr.op.getNumOperands ctx h := by
  rfl

def OpOperandPtr.get (operand: OpOperandPtr) (ctx: IRContext) (operandIn: operand.InBounds ctx := by grind) : OpOperand :=
  (operand.op.get ctx (by grind [OpOperandPtr.InBounds])).operands[operand.index]'(by grind [OpOperandPtr.InBounds, OperationPtr.getNumOperands])

def OpOperandPtr.get! (operand: OpOperandPtr) (ctx: IRContext) : OpOperand :=
  (operand.op.get! ctx).operands[operand.index]!

@[grind _=_]
theorem OpOperandPtr.get!_eq_get {ptr : OpOperandPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem OpOperandPtr.get!_eq_of_OperationPtr_get!_eq {opr : OpOperandPtr} :
    opr.op.get! ctx = opr.op.get! ctx' →
    opr.get! ctx = opr.get! ctx' := by
  grind [OperationPtr.get!, OpOperandPtr.get!]

@[grind =]
theorem OperationPtr.getOperand_eq_OpOperandPtr_get :
    OperationPtr.getOperand op ctx index opInBounds indexInBounds =
    (OpOperandPtr.get (OperationPtr.getOpOperand op index) ctx (by grind [OperationPtr.getOpOperand, OpOperandPtr.InBounds, OperationPtr.getNumOperands])).value := by
  grind [OpOperandPtr.get, OperationPtr.getOperand, OperationPtr.get, OperationPtr.getOpOperand]

def OpOperandPtr.set (operand: OpOperandPtr) (ctx: IRContext) (newOperand: OpOperand)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let op := operand.op.get ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        operands := op.operands.set operand.index newOperand (by grind)} }

def OpOperandPtr.setNextUse (operand: OpOperandPtr) (ctx: IRContext) (newNextUse: Option OpOperandPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with nextUse := newNextUse }

def OpOperandPtr.setBack (operand: OpOperandPtr) (ctx: IRContext) (newBack: OpOperandPtrPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with back := newBack }

def OpOperandPtr.setOwner (operand: OpOperandPtr) (ctx: IRContext) (newOwner: OperationPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with owner := newOwner }

def OpOperandPtr.setValue (operand: OpOperandPtr) (ctx: IRContext) (newValue: ValuePtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with value := newValue }

/-
 BlockOperandPtr accessors
-/

@[local grind]
def BlockOperandPtr.InBounds (operand: BlockOperandPtr) (ctx: IRContext) : Prop :=
  ∃ h, operand.index < (operand.op.get ctx h).blockOperands.size

def BlockOperandPtr.get (operand: BlockOperandPtr) (ctx: IRContext) (operandIn: operand.InBounds ctx := by grind) : BlockOperand :=
  (operand.op.get ctx (by grind [InBounds])).blockOperands[operand.index]'(by grind [InBounds])
def BlockOperandPtr.get! (operand: BlockOperandPtr) (ctx: IRContext) : BlockOperand :=
  operand.op.get! ctx |>.blockOperands[operand.index]!
@[grind _=_]
theorem BlockOperandPtr.get!_eq_get {ptr : BlockOperandPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!, OperationPtr.get!]

theorem BlockOperandPtr.get!_eq_of_OperationPtr_get!_eq {opr : BlockOperandPtr} :
    opr.op.get! ctx = opr.op.get! ctx' →
    opr.get! ctx = opr.get! ctx' := by
  grind [OperationPtr.get!, BlockOperandPtr.get!]

def BlockOperandPtr.set (operand: BlockOperandPtr) (ctx: IRContext) (newOperand: BlockOperand) (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let op := operand.op.get ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        blockOperands := op.blockOperands.set operand.index newOperand (by grind)} }

def BlockOperandPtr.setNextUse (operand: BlockOperandPtr) (ctx: IRContext) (newNextUse: Option BlockOperandPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with nextUse := newNextUse }

def BlockOperandPtr.setBack (operand: BlockOperandPtr) (ctx: IRContext) (newBack: BlockOperandPtrPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with back := newBack }

def BlockOperandPtr.setOwner (operand: BlockOperandPtr) (ctx: IRContext) (newOwner: OperationPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with owner := newOwner }

def BlockOperandPtr.setValue (operand: BlockOperandPtr) (ctx: IRContext) (newValue: BlockPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with value := newValue }

/-
 OpResultPtr accessors
-/

@[local grind]
def OpResultPtr.InBounds (result: OpResultPtr) (ctx: IRContext) : Prop :=
  ∃ h, result.index < (result.op.get ctx h).results.size

@[grind .]
theorem OpResultPtr.inBounds_OperationPtr_getNumResults! (result: OpResultPtr) (ctx: IRContext) (h: result.InBounds ctx) :
    result.index < result.op.getNumResults! ctx := by
  simp [OperationPtr.getNumResults!, OperationPtr.get!]
  grind [OperationPtr.get]

def OpResultPtr.get (result: OpResultPtr) (ctx: IRContext) (resultIn: result.InBounds ctx := by grind) : OpResult :=
  (result.op.get ctx (by grind [InBounds])).results[result.index]'(by grind [InBounds])

def OpResultPtr.get! (result: OpResultPtr) (ctx: IRContext) : OpResult :=
  (result.op.get! ctx).results[result.index]!

@[grind _=_]
theorem OpResultPtr.get!_eq_get {ptr : OpResultPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem OpResultPtr.get!_eq_of_OperationPtr_get!_eq {res : OpResultPtr} :
    res.op.get! ctx = res.op.get! ctx' →
    res.get! ctx = res.get! ctx' := by
  grind [OperationPtr.get!, OpResultPtr.get!]

def OpResultPtr.set (result: OpResultPtr) (ctx: IRContext) (newresult: OpResult) (resultIn: result.InBounds ctx := by grind) : IRContext :=
  let op := result.op.get ctx
  { ctx with
    operations := ctx.operations.insert result.op
      { op with
        results := op.results.set result.index newresult (by grind)} }

def OpResultPtr.setType (result: OpResultPtr) (ctx: IRContext) (newType: MlirType)
    (resultIn: result.InBounds ctx := by grind) : IRContext :=
  let oldResult := result.get ctx
  result.set ctx { oldResult with type := newType }

def OpResultPtr.setFirstUse (result: OpResultPtr) (ctx: IRContext) (newFirstUse: Option OpOperandPtr)
    (resultIn: result.InBounds ctx := by grind) : IRContext :=
  let oldResult := result.get ctx
  result.set ctx { oldResult with firstUse := newFirstUse }

def OpResultPtr.setOwner (result: OpResultPtr) (ctx: IRContext) (newOwner: OperationPtr)
    (resultIn: result.InBounds ctx := by grind) : IRContext :=
  let oldResult := result.get ctx
  result.set ctx { oldResult with owner := newOwner }

/-
 BlockPtr accessors
-/

def BlockPtr.InBounds (block: BlockPtr) (ctx: IRContext) : Prop :=
  block ∈ ctx.blocks

def BlockPtr.get (ptr: BlockPtr) (ctx: IRContext) (inBounds: ptr.InBounds ctx := by grind) : Block :=
  ctx.blocks[ptr]'(by unfold InBounds at inBounds; grind)

def BlockPtr.get! (ptr: BlockPtr) (ctx: IRContext) : Block := ctx.blocks[ptr]!

@[grind _=_]
theorem BlockPtr.get!_eq_get {ptr : BlockPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

def BlockPtr.set (ptr: BlockPtr) (ctx: IRContext) (newBlock: Block) : IRContext :=
  {ctx with blocks := ctx.blocks.insert ptr newBlock}

def BlockPtr.setParent (block: BlockPtr) (ctx: IRContext) (newParent: Option RegionPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with parent := newParent}

def BlockPtr.setFirstUse (block: BlockPtr) (ctx: IRContext) (newFirstUse: Option BlockOperandPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with firstUse := newFirstUse}

def BlockPtr.setFirstOp (block: BlockPtr) (ctx: IRContext) (newFirstOp: Option OperationPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with firstOp := newFirstOp}

def BlockPtr.setLastOp (block: BlockPtr) (ctx: IRContext) (newLastOp: Option OperationPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with lastOp := newLastOp}

def BlockPtr.setNextBlock (block: BlockPtr) (ctx: IRContext) (newNext: Option BlockPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with next := newNext}

def BlockPtr.setPrevBlock (block: BlockPtr) (ctx: IRContext) (newPrev: Option BlockPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with prev := newPrev}

def BlockPtr.allocEmpty (ctx: IRContext) : Option (IRContext × BlockPtr) :=
  let newBlockPtr: BlockPtr := ctx.nextID
  let ctx : IRContext := { ctx with nextID := ctx.nextID + 1}
  if _ : ctx.blocks.contains newBlockPtr then none else
  let ctx := newBlockPtr.set ctx Block.empty
  some (ctx, newBlockPtr)

theorem BlockPtr.allocEmpty_def (heq : allocEmpty ctx = some (ctx', ptr')) :
    ctx' = BlockPtr.set ctx.nextID {ctx with nextID := ctx.nextID + 1} Block.empty := by
  grind [allocEmpty]

def BlockPtr.getNumArguments (block: BlockPtr) (ctx: IRContext) (inBounds: block.InBounds ctx := by grind) : Nat :=
  (block.get ctx (by grind)).arguments.size

def BlockPtr.getNumArguments! (block: BlockPtr) (ctx: IRContext) : Nat :=
  (block.get! ctx).arguments.size

@[grind _=_]
theorem BlockPtr.getNumArguments!_eq_getNumArguments {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getNumArguments! ctx = block.getNumArguments ctx (by grind) := by
  grind [getNumArguments, getNumArguments!]

theorem BlockPtr.getNumArguments!_eq_of_BlockPtr_get!_eq {block : BlockPtr} :
    block.get! ctx = block.get! ctx' →
    block.getNumArguments! ctx = block.getNumArguments! ctx' := by
  grind [BlockPtr.getNumArguments!]

def BlockPtr.getArgument (block: BlockPtr) (index: Nat) : BlockArgumentPtr :=
  { block := block, index := index }

@[simp, grind =]
theorem BlockPtr.getArgument_index {block : BlockPtr} {index : Nat} :
    (BlockPtr.getArgument block index).index = index := by
  grind [getArgument]

@[simp, grind =]
theorem BlockPtr.getArgument_block {block : BlockPtr} {index : Nat} :
    (BlockPtr.getArgument block index).block = block := by
  grind [getArgument]

/-
 BlockArgumentPtr accessors
-/

@[local grind]
def BlockArgumentPtr.InBounds (arg: BlockArgumentPtr) (ctx: IRContext) : Prop :=
  ∃ h, arg.index < (arg.block.get ctx h).arguments.size

def BlockArgumentPtr.get (arg: BlockArgumentPtr) (ctx: IRContext) (argIn: arg.InBounds ctx := by grind) : BlockArgument :=
  (arg.block.get ctx (by grind [BlockArgumentPtr.InBounds])).arguments[arg.index]'(by grind [BlockArgumentPtr.InBounds])

def BlockArgumentPtr.get! (arg: BlockArgumentPtr) (ctx: IRContext) : BlockArgument :=
  (arg.block.get! ctx).arguments[arg.index]!

@[grind _=_]
theorem BlockArgumentPtr.get!_eq_get {ptr : BlockArgumentPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem BlockArgumentPtr.get!_eq_of_BlockPtr_get!_eq {arg : BlockArgumentPtr} :
    arg.block.get! ctx = arg.block.get! ctx' →
    arg.get! ctx = arg.get! ctx' := by
  grind [BlockPtr.get!, BlockArgumentPtr.get!]

def BlockArgumentPtr.set (arg: BlockArgumentPtr) (ctx: IRContext) (newresult: BlockArgument) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let block := arg.block.get ctx
  { ctx with
    blocks := ctx.blocks.insert arg.block
      { block with
        arguments := block.arguments.set arg.index newresult (by grind)} }

def BlockArgumentPtr.setType (arg: BlockArgumentPtr) (ctx: IRContext) (newType: MlirType) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with type := newType }

def BlockArgumentPtr.setFirstUse (arg: BlockArgumentPtr) (ctx: IRContext) (newFirstUse: Option OpOperandPtr) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with firstUse := newFirstUse }

def BlockArgumentPtr.setIndex (arg: BlockArgumentPtr) (ctx: IRContext) (newIndex: Nat) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with index := newIndex }

def BlockArgumentPtr.setLoc (arg: BlockArgumentPtr) (ctx: IRContext) (newLoc: Location) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with loc := newLoc }

def BlockArgumentPtr.setOwner (arg: BlockArgumentPtr) (ctx: IRContext) (newOwner: OperationPtr) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with owner := newOwner }

/-
 ValuePtr accessors
-/

inductive ValuePtr.InBounds : ValuePtr → IRContext → Prop
| OpResultPtrInBounds ptr ctx : ptr.InBounds ctx → (opResult ptr).InBounds ctx
| BlockArgumentPtrInBounds ptr ctx : ptr.InBounds ctx → (blockArgument ptr).InBounds ctx

@[simp, grind=]
theorem ValuePtr.inBounds_opResult (ptr: OpResultPtr) (ctx: IRContext) :
    (opResult ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [ValuePtr.InBounds]

@[simp, grind=]
theorem ValuePtr.inBounds_blockArg (ptr: BlockArgumentPtr) (ctx: IRContext) :
    (blockArgument ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [ValuePtr.InBounds]

def ValuePtr.getType (arg: ValuePtr) (ctx: IRContext) (argIn: arg.InBounds ctx := by grind) : MlirType :=
  match arg with
  | opResult ptr => (ptr.get ctx (by grind)).type
  | blockArgument ptr => (ptr.get ctx (by grind)).type

def ValuePtr.getType! (arg: ValuePtr) (ctx: IRContext) : MlirType :=
  match arg with
  | opResult ptr => (ptr.get! ctx).type
  | blockArgument ptr => (ptr.get! ctx).type

@[grind _=_]
theorem ValuePtr.getType!_eq_getType {ptr : ValuePtr} (hin : ptr.InBounds ctx) :
    ptr.getType! ctx = ptr.getType ctx hin := by
  unfold getType getType!; grind

def ValuePtr.getFirstUse (arg: ValuePtr) (ctx: IRContext) (argIn: arg.InBounds ctx := by grind) : Option OpOperandPtr :=
  match arg with
  | opResult ptr => (ptr.get ctx).firstUse
  | blockArgument ptr => (ptr.get ctx).firstUse

def ValuePtr.getFirstUse! (arg: ValuePtr) (ctx: IRContext) : Option OpOperandPtr :=
  match arg with
  | opResult ptr => (ptr.get! ctx).firstUse
  | blockArgument ptr => (ptr.get! ctx).firstUse

@[grind _=_]
theorem ValuePtr.getFirstUse!_eq_getFirstUse {ptr : ValuePtr} (hin : ptr.InBounds ctx) :
    ptr.getFirstUse! ctx = ptr.getFirstUse ctx hin := by
  unfold getFirstUse getFirstUse!; grind

@[grind =]
theorem ValuePtr.getFirstUse_opResult_eq {res : OpResultPtr} {ctx : IRContext} {h : res.InBounds ctx} :
    (opResult res).getFirstUse ctx = (res.get ctx).firstUse := by
  grind [getFirstUse]

@[grind =]
theorem ValuePtr.getFirstUse_blockArgument_eq {ba : BlockArgumentPtr} {ctx : IRContext} {h : ba.InBounds ctx} :
    (blockArgument ba).getFirstUse ctx = (ba.get ctx).firstUse := by
  grind [getFirstUse]

def ValuePtr.setType (arg: ValuePtr) (ctx: IRContext) (newType: MlirType) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  match arg with
  | opResult ptr => ptr.setType ctx newType
  | blockArgument ptr => ptr.setType ctx newType

def ValuePtr.setFirstUse (arg: ValuePtr) (ctx: IRContext) (newFirstUse: Option OpOperandPtr) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  match arg with
  | opResult ptr => ptr.setFirstUse ctx newFirstUse
  | blockArgument ptr => ptr.setFirstUse ctx newFirstUse

@[simp, grind =]
theorem ValuePtr.setFirstUse_OpResultPtr (ptr: OpResultPtr) (ctx: IRContext)
    (ptrIn: (opResult ptr).InBounds ctx) (newFirstUse: Option OpOperandPtr) :
    (opResult ptr).setFirstUse ctx newFirstUse ptrIn = ptr.setFirstUse ctx newFirstUse := by
  unfold setFirstUse; grind

@[simp, grind =]
theorem ValuePtr.setFirstUse_BlockArgumentPtr (ptr: BlockArgumentPtr) (ctx: IRContext)
    (ptrIn: (blockArgument ptr).InBounds ctx) (newFirstUse: Option OpOperandPtr) :
    (blockArgument ptr).setFirstUse ctx newFirstUse ptrIn = ptr.setFirstUse ctx newFirstUse := by
  unfold setFirstUse; rfl

@[simp, grind =]
theorem ValuePtr.setType_OpResultPtr (ptr: OpResultPtr) (ctx: IRContext)
    (ptrIn: (opResult ptr).InBounds ctx) (newType: MlirType) :
    (opResult ptr).setType ctx newType ptrIn = ptr.setType ctx newType := by
  unfold setType; rfl

@[simp, grind =]
theorem ValuePtr.setType_BlockArgumentPtr (ptr: BlockArgumentPtr) (ctx: IRContext)
    (ptrIn: (blockArgument ptr).InBounds ctx) (newType: MlirType) :
    (blockArgument ptr).setType ctx newType ptrIn = ptr.setType ctx newType := by
  unfold setType; rfl

/-
  OpOperandPtrPtr accessors
-/

inductive OpOperandPtrPtr.InBounds (ctx: IRContext) : OpOperandPtrPtr → Prop
  | operandNextUseInBounds ptr : ptr.InBounds ctx → (operandNextUse ptr).InBounds ctx
  | valueFirstUseInBounds ptr : ptr.InBounds ctx → (valueFirstUse ptr).InBounds ctx

@[simp, grind=]
theorem OpOperandPtrPtr.inBounds_operandNextUse (ptr: OpOperandPtr) (ctx: IRContext) :
    (operandNextUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [OpOperandPtrPtr.InBounds]

@[simp, grind=]
theorem OpOperandPtrPtr.inBounds_valueFirstUse (ptr: ValuePtr) (ctx: IRContext) :
    (valueFirstUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [OpOperandPtrPtr.InBounds]

def OpOperandPtrPtr.get (ptrPtr: OpOperandPtrPtr) (ctx: IRContext) (ptrPtrIn: ptrPtr.InBounds ctx := by grind) : Option OpOperandPtr :=
  match ptrPtr with
  | operandNextUse ptr => (ptr.get ctx).nextUse
  | valueFirstUse val => val.getFirstUse ctx (by grind)

def OpOperandPtrPtr.get! (ptrPtr: OpOperandPtrPtr) (ctx: IRContext) : Option OpOperandPtr :=
  match ptrPtr with
  | operandNextUse ptr => (ptr.get! ctx).nextUse
  | valueFirstUse val => val.getFirstUse! ctx

@[grind _=_]
theorem OpOperandPtrPtr.get!_eq_get {ptrPtr : OpOperandPtrPtr} (hin : ptrPtr.InBounds ctx) :
    ptrPtr.get! ctx = ptrPtr.get ctx hin := by
  unfold get get!; grind

@[simp, grind =]
theorem OpOperandPtrPtr.get_operandNextUse_eq {ptr: OpOperandPtr} {ctx: IRContext} {ptrIn: ptr.InBounds ctx} :
    (operandNextUse ptr).get ctx (by grind) = (ptr.get ctx).nextUse := by
  grind [get]

@[simp, grind =]
theorem OpOperandPtrPtr.get!_operandNextUse_eq {ptr: OpOperandPtr} {ctx: IRContext} :
    (operandNextUse ptr).get! ctx = (ptr.get! ctx).nextUse := by
  grind [get!]

@[simp, grind =]
theorem OpOperandPtrPtr.get_valueFirstUse_eq {ptr: ValuePtr} {ctx: IRContext} {ptrIn: ptr.InBounds ctx} :
    (valueFirstUse ptr).get ctx (by grind) = ptr.getFirstUse ctx := by
  grind [get]

@[simp, grind =]
theorem OpOperandPtrPtr.get!_valueFirstUse_eq {ptr: ValuePtr} {ctx: IRContext} :
    (valueFirstUse ptr).get! ctx = ptr.getFirstUse! ctx := by
  grind [get!]

def OpOperandPtrPtr.set (ptrPtr: OpOperandPtrPtr) (ctx: IRContext) (newValue: Option OpOperandPtr) (ptrPtrIn: ptrPtr.InBounds ctx := by grind) : IRContext :=
  match ptrPtr with
  | operandNextUse ptr =>
    ptr.setNextUse ctx newValue
  | valueFirstUse val =>
    val.setFirstUse ctx newValue

@[simp]
theorem OpOperandPtrPtr.set_operandNextUse (ptr: OpOperandPtr) (ctx: IRContext) (newValue: Option OpOperandPtr) (ptrIn: (operandNextUse ptr).InBounds ctx) :
    (operandNextUse ptr).set ctx newValue ptrIn = ptr.setNextUse ctx newValue := by
  unfold set; rfl

@[simp]
theorem OpOperandPtrPtr.set_valueFirstUse (ptr: ValuePtr) (ctx: IRContext) (ptrIn: (valueFirstUse ptr).InBounds ctx) (newValue: Option OpOperandPtr) :
    (valueFirstUse ptr).set ctx newValue ptrIn = ptr.setFirstUse ctx newValue := by
  unfold set; rfl

/-
  RegionPtr accessors
-/

def RegionPtr.InBounds (region: RegionPtr) (ctx: IRContext) : Prop :=
  region ∈ ctx.regions

def RegionPtr.get (ptr: RegionPtr) (ctx: IRContext) (inBounds: ptr.InBounds ctx := by grind) : Region :=
  ctx.regions[ptr]'(by unfold InBounds at inBounds; grind)

def RegionPtr.get! (ptr: RegionPtr) (ctx: IRContext) : Region := ctx.regions[ptr]!

@[grind _=_]
theorem RegionPtr.get!_eq_get {ptr : RegionPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

def RegionPtr.set (ptr: RegionPtr) (ctx: IRContext) (newRegion: Region) : IRContext :=
  {ctx with regions := ctx.regions.insert ptr newRegion}

def RegionPtr.setParent (region: RegionPtr) (ctx: IRContext) (newParent: OperationPtr)
    (inBounds: region.InBounds ctx := by grind) : IRContext :=
  let oldRegion := region.get ctx (by grind)
  region.set ctx { oldRegion with parent := newParent}

def RegionPtr.setFirstBlock (region: RegionPtr) (ctx: IRContext) (newFirstBlock: Option BlockPtr)
    (inBounds: region.InBounds ctx := by grind) : IRContext :=
  let oldRegion := region.get ctx (by grind)
  region.set ctx { oldRegion with firstBlock := newFirstBlock}

def RegionPtr.setLastBlock (region: RegionPtr) (ctx: IRContext) (newLastBlock: Option BlockPtr)
    (inBounds: region.InBounds ctx := by grind) : IRContext :=
  let oldRegion := region.get ctx (by grind)
  region.set ctx { oldRegion with lastBlock := newLastBlock}

def RegionPtr.allocEmpty (ctx: IRContext) : Option (IRContext × RegionPtr) :=
  let newRegionPtr: RegionPtr := ctx.nextID
  let region := Region.empty
  let ctx := { ctx with nextID := ctx.nextID + 1}
  if _ : ctx.regions.contains newRegionPtr then none else
  let ctx := newRegionPtr.set ctx region
  (ctx, newRegionPtr)

/-
  BlockOperandPtrPtr accessors
-/

@[local grind]
inductive BlockOperandPtrPtr.InBounds (ctx: IRContext) : BlockOperandPtrPtr → Prop
  | blockOperandNextUseInBounds ptr : ptr.InBounds ctx → (blockOperandNextUse ptr).InBounds ctx
  | blockFirstUseInBounds ptr : ptr.InBounds ctx → (blockFirstUse ptr).InBounds ctx

@[simp, grind=]
theorem BlockOperandPtrPtr.inBounds_operandNextUse (ptr: BlockOperandPtr) (ctx: IRContext) :
    (blockOperandNextUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[simp, grind=]
theorem BlockOperandPtrPtr.inBounds_valueFirstUse (ptr: BlockPtr) (ctx: IRContext) :
    (blockFirstUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind

def BlockOperandPtrPtr.get (ptrPtr: BlockOperandPtrPtr) (ctx: IRContext) (ptrPtrIn: ptrPtr.InBounds ctx := by grind) : Option BlockOperandPtr :=
  match ptrPtr with
  | blockOperandNextUse ptr => (ptr.get ctx).nextUse
  | blockFirstUse val => (val.get ctx (by grind)).firstUse

def BlockOperandPtrPtr.get! (ptrPtr: BlockOperandPtrPtr) (ctx: IRContext) : Option BlockOperandPtr :=
  match ptrPtr with
  | blockOperandNextUse ptr => (ptr.get! ctx).nextUse
  | blockFirstUse val => (val.get! ctx).firstUse

@[grind _=_]
theorem BlockOperandPtrPtr.get!_eq_get {ptrPtr : BlockOperandPtrPtr} (hin : ptrPtr.InBounds ctx) :
    ptrPtr.get! ctx = ptrPtr.get ctx hin := by
  unfold get get!; grind

@[grind =]
theorem BlockOperandPtrPtr.get_nextUse_eq {bo : BlockOperandPtr} {h : bo.InBounds ctx} :
    (blockOperandNextUse bo).get ctx = (bo.get ctx).nextUse := by
  grind [get]

@[grind =]
theorem BlockOperandPtrPtr.get_firstUse_eq {bl : BlockPtr} {h : bl.InBounds ctx} :
    (blockFirstUse bl).get ctx = (bl.get ctx).firstUse := by
  grind [get]

def BlockOperandPtrPtr.set (ptrPtr: BlockOperandPtrPtr) (ctx: IRContext) (ptrPtrIn: ptrPtr.InBounds ctx := by grind) (newValue: Option BlockOperandPtr) : IRContext :=
  match ptrPtr with
  | blockOperandNextUse ptr => ptr.setNextUse ctx newValue
  | blockFirstUse val => val.setFirstUse ctx newValue

@[simp, grind =]
theorem BlockOperandPtrPtr.set_operandNextUse_eq {ptr: BlockOperandPtr} {ptrIn: ptr.InBounds ctx} (newValue: Option BlockOperandPtr) :
    (blockOperandNextUse ptr).set ctx (by grind) newValue = ptr.setNextUse ctx newValue := by
  rfl

@[simp, grind =]
theorem BlockOperandPtrPtr.set_blockFirstUse_eq {ptr: BlockPtr} {ptrIn: ptr.InBounds ctx} (newValue: Option BlockOperandPtr) :
    (blockFirstUse ptr).set ctx (by grind) newValue = ptr.setFirstUse ctx newValue := by
  rfl

/- Generic pointers -/

inductive GenericPtr where
| block (ptr : BlockPtr)
| operation (ptr : OperationPtr)
| opResult (ptr : OpResultPtr)
| opOperand (ptr : OpOperandPtr)
| blockOperand (ptr : BlockOperandPtr)
| blockOperandPtr (ptr : BlockOperandPtrPtr)
| blockArgument (ptr : BlockArgumentPtr)
| region (ptr : RegionPtr)
| value (ptr : ValuePtr)
| opOperandPtr (ptr : OpOperandPtrPtr)

namespace GenericPtr

def InBounds (ptr : GenericPtr) (ctx : IRContext) : Prop :=
  match ptr with
  | block ptr => ptr.InBounds ctx
  | operation ptr => ptr.InBounds ctx
  | opResult ptr => ptr.InBounds ctx
  | opOperand ptr => ptr.InBounds ctx
  | blockOperand ptr => ptr.InBounds ctx
  | blockOperandPtr ptr => ptr.InBounds ctx
  | blockArgument ptr => ptr.InBounds ctx
  | region ptr => ptr.InBounds ctx
  | value ptr => ptr.InBounds ctx
  | opOperandPtr ptr => ptr.InBounds ctx

section generic_ptr

variable {ctx : IRContext}

@[simp, grind =, grind =_] theorem iff_block (ptr : BlockPtr) : (block ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [InBounds]
@[simp, grind =, grind =_] theorem iff_operation (ptr : OperationPtr) : (operation ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind =, grind =_] theorem iff_result (ptr : OpResultPtr) : (opResult ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind =, grind =_] theorem iff_opOperand (ptr : OpOperandPtr) : (opOperand ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind =, grind =_] theorem iff_blockOperand (ptr : BlockOperandPtr) : (blockOperand ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind =, grind =_] theorem iff_blockOperandPtr (ptr : BlockOperandPtrPtr) : (blockOperandPtr ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind =, grind =_] theorem iff_blockArgument (ptr : BlockArgumentPtr) : (blockArgument ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind =, grind =_] theorem iff_region (ptr : RegionPtr) : (region ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind =, grind =_] theorem iff_value (ptr : ValuePtr) : (value ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]
@[simp, grind =, grind =_] theorem iff_opOperandPtr (ptr : OpOperandPtrPtr) : (opOperandPtr ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [InBounds]

end generic_ptr
end GenericPtr

/-
 - Macro to mark all get/set defitinions as local grind lemmas
 - This should only be used inside `Core/`, as the other files in this folder
 - should define all the necessary lemmas without having to unfold these definitions.
 -/
macro "setup_grind_with_get_set_definitions" : command => `(
  attribute [local grind cases] ValuePtr OpOperandPtr GenericPtr BlockOperandPtr OpResultPtr BlockArgumentPtr BlockOperandPtrPtr OpOperandPtrPtr
  attribute [local grind] OpOperandPtr.setNextUse OpOperandPtr.setBack OpOperandPtr.setOwner OpOperandPtr.setValue OpOperandPtr.set
  attribute [local grind] OpOperandPtrPtr.set OpOperandPtrPtr.get!
  attribute [local grind] ValuePtr.getFirstUse! ValuePtr.getFirstUse ValuePtr.setFirstUse ValuePtr.setType
  attribute [local grind] OpResultPtr.get! OpResultPtr.setFirstUse OpResultPtr.set OpResultPtr.setType
  attribute [local grind] BlockArgumentPtr.get! BlockArgumentPtr.setFirstUse BlockArgumentPtr.set BlockArgumentPtr.setType BlockArgumentPtr.setLoc
  attribute [local grind] OperationPtr.setOperands OperationPtr.setResults OperationPtr.pushResult OperationPtr.setRegions OperationPtr.setProperties  OperationPtr.pushOperand OperationPtr.allocEmpty OperationPtr.setNextOp OperationPtr.setPrevOp OperationPtr.setParent OperationPtr.getNumResults! OperationPtr.getNumOperands! OperationPtr.getNumRegions! OperationPtr.getRegion! OperationPtr.getNumSuccessors! OperationPtr.set
  attribute [local grind] Operation.empty
  attribute [local grind] BlockPtr.get! BlockPtr.setParent BlockPtr.setFirstUse BlockPtr.setFirstOp BlockPtr.setLastOp BlockPtr.setNextBlock BlockPtr.setPrevBlock BlockPtr.allocEmpty Block.empty BlockPtr.getNumArguments! BlockPtr.set
  attribute [local grind =] Option.maybe_def
  attribute [local grind] OpOperandPtr.get! BlockOperandPtr.get! OpResultPtr.get! BlockArgumentPtr.get! OperationPtr.get!
  attribute [local grind] BlockOperandPtr.setBack BlockOperandPtr.setNextUse BlockOperandPtr.setOwner BlockOperandPtr.setValue BlockOperandPtr.set
  attribute [local grind] BlockOperandPtrPtr.get!
  attribute [local grind] RegionPtr.get! RegionPtr.setParent RegionPtr.setFirstBlock RegionPtr.setLastBlock RegionPtr.set RegionPtr.allocEmpty
)
