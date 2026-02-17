module

public import Std.Data.HashMap
public import Veir.Prelude
public import Veir.OpCode
public import Veir.ForLean
public import Veir.IR.Attribute
public import Veir.Properties

open Std (HashMap)

public section

namespace Veir

structure OperationPtr where
  id: Nat
deriving Inhabited, Repr, DecidableEq

instance : Hashable OperationPtr where
  hash opPtr := hash opPtr.id

structure BlockPtr where
  id: Nat
deriving Inhabited, Repr, DecidableEq

instance : Hashable BlockPtr where
  hash blockPtr := hash blockPtr.id

structure RegionPtr where
  id: Nat
deriving Inhabited, Repr, DecidableEq

instance : Hashable RegionPtr where
  hash regionPtr := hash regionPtr.id

abbrev Location := Unit
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
  type: TypeAttr
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
  -- For example, the `IROperandBase::removeFromCurrent` method checks for null.
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
  opType: OpCode
  attrs: AttrDictionary
  -- This should be replaced with an arbitrary user object
  properties: propertiesOf opType
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
  nextID: Nat
deriving Inhabited, Repr

/- Empty objects. -/

@[expose]
def Operation.empty (opType: OpCode) (prop : propertiesOf opType) : Operation :=
  { results := #[]
    prev := none
    next := none
    parent := none
    opType := opType
    attrs := ()
    properties := prop
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

namespace OperationPtr

@[local grind]
def InBounds (op: OperationPtr) (ctx: IRContext) : Prop :=
  op ∈ ctx.operations

def get (ptr: OperationPtr) (ctx: IRContext) (inBounds: ptr.InBounds ctx := by grind) : Operation :=
  ctx.operations[ptr]'(by unfold InBounds at inBounds; grind)

def get! (ptr: OperationPtr) (ctx: IRContext) : Operation :=
  ctx.operations[ptr]!
@[grind _=_]
theorem get!_eq_get {ptr : OperationPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = (ptr.get ctx hin) := by
  grind [get, get!, InBounds]

def getOpType (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx) : OpCode :=
  (op.get ctx (by grind)).opType

def getNumOperands (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).operands.size

def getNumOperands! (op: OperationPtr) (ctx: IRContext) : Nat :=
  (op.get! ctx).operands.size

@[grind _=_]
theorem getNumOperands!_eq_getNumOperands {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumOperands! ctx = op.getNumOperands ctx (by grind) := by
  grind [getNumOperands, getNumOperands!]

theorem getNumOperands!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumOperands! ctx = op.getNumOperands! ctx' := by
  grind [getNumOperands!]

def getOpOperand (op: OperationPtr) (index: Nat) : OpOperandPtr :=
  { op := op, index := index }

@[simp, grind =]
theorem getOpOperand_index {op : OperationPtr} {index : Nat} :
    (getOpOperand op index).index = index := by
  grind [getOpOperand]

@[simp, grind =]
theorem getOpOperand_op {op : OperationPtr} {index : Nat} :
    (getOpOperand op index).op = op := by
  grind [getOpOperand]

def getOperand (op: OperationPtr) (ctx: IRContext) (index: Nat)
    (inBounds: op.InBounds ctx := by grind) (h: index < getNumOperands op ctx inBounds := by grind) : ValuePtr :=
  ((op.get ctx (by grind)).operands[index]'(by grind [getNumOperands])).value

def getOperand! (op: OperationPtr) (ctx: IRContext) (index: Nat) : ValuePtr :=
  ((op.get! ctx).operands[index]!).value

@[grind _=_]
theorem getOperand!_eq_getOperand {op : OperationPtr} {index : Nat}
    {hin} (h: index < op.getNumOperands ctx hin) {hin'} :
    op.getOperand! ctx index = op.getOperand ctx index hin' h := by
  grind [getOperand, getOperand!]

def getNumSuccessors (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).blockOperands.size

def getNumSuccessors! (op: OperationPtr) (ctx: IRContext) : Nat :=
  (op.get! ctx).blockOperands.size

@[grind _=_]
theorem getNumSuccessors!_eq_getNumSuccessors {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumSuccessors! ctx = op.getNumSuccessors ctx (by grind) := by
  grind [getNumSuccessors, getNumSuccessors!]

theorem getNumSuccessors!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumSuccessors! ctx = op.getNumSuccessors! ctx' := by
  grind [getNumSuccessors!]

def getBlockOperand (op: OperationPtr) (index: Nat) : BlockOperandPtr :=
  { op := op, index := index }

@[simp, grind =]
theorem getBlockOperand_index {op : OperationPtr} {index : Nat} :
    (getBlockOperand op index).index = index := by
  grind [getBlockOperand]

@[simp, grind =]
theorem getBlockOperand_op {op : OperationPtr} {index : Nat} :
    (getBlockOperand op index).op = op := by
  grind [getBlockOperand]

def getSuccessor (op: OperationPtr) (ctx: IRContext) (index: Nat)
    (inBounds: op.InBounds ctx := by grind) (h: index < getNumSuccessors op ctx inBounds := by grind) : BlockPtr :=
  ((op.get ctx (by grind)).blockOperands[index]'(by grind [getNumSuccessors])).value

def getSuccessor! (op: OperationPtr) (ctx: IRContext) (index: Nat) : BlockPtr :=
  ((op.get! ctx).blockOperands[index]!).value

@[grind _=_]
theorem getSuccessor!_eq_getSuccessor {op : OperationPtr} {index : Nat}
    {hin} (h: index < op.getNumSuccessors ctx hin) {hin'} :
    op.getSuccessor! ctx index = op.getSuccessor ctx index hin' h := by
  grind [getSuccessor, getSuccessor!]

def getNumResults (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).results.size

def getNumResults! (op: OperationPtr) (ctx: IRContext) : Nat :=
  (op.get! ctx).results.size

@[grind _=_]
theorem getNumResults!_eq_getNumResults {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumResults! ctx = op.getNumResults ctx (by grind) := by
  grind [getNumResults, getNumResults!]

theorem getNumResults!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumResults! ctx = op.getNumResults! ctx' := by
  grind [getNumResults!]

def getResult (op: OperationPtr) (index: Nat) : OpResultPtr :=
  { op := op, index := index }

@[simp, grind =]
theorem getResult_index {op : OperationPtr} {index : Nat} :
    (getResult op index).index = index := by
  grind [getResult]

@[simp, grind =]
theorem getResult_op {op : OperationPtr} {index : Nat} :
    (getResult op index).op = op := by
  grind [getResult]

theorem eq_getResult_of_OpResultPtr_op_eq {res : OpResultPtr} :
    res.op = op → res = op.getResult res.index := by
  grind [getResult, cases OpResultPtr]

def getNumRegions (op: OperationPtr) (ctx: IRContext)
    (inBounds: op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).regions.size

def getNumRegions! (op: OperationPtr) (ctx: IRContext) : Nat :=
  (op.get! ctx).regions.size

@[grind _=_]
theorem getNumRegions!_eq_getNumRegions {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumRegions! ctx = op.getNumRegions ctx (by grind) := by
  grind [getNumRegions, getNumRegions!]

theorem getNumRegions!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumRegions! ctx = op.getNumRegions! ctx' := by
  grind [getNumRegions!]

def getRegion (op: OperationPtr) (ctx: IRContext) (index: Nat)
  (inBounds: op.InBounds ctx := by grind) (iInBounds: index < op.getNumRegions ctx inBounds := by grind) : RegionPtr :=
  (op.get ctx (by grind)).regions[index]'(by grind [getNumRegions])

@[grind funCC]
def getRegion! (op: OperationPtr) (ctx: IRContext) (index: Nat) : RegionPtr :=
  (op.get! ctx).regions[index]!

@[grind _=_]
theorem getRegion!_eq_getRegion {op : OperationPtr} {index : Nat}
    {hin} (iInBounds : index < op.getNumRegions ctx hin) {hin'} :
    op.getRegion! ctx index = op.getRegion ctx index hin' iInBounds := by
  grind [getRegion, getRegion!]

theorem getRegion!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getRegion! ctx = op.getRegion! ctx' := by
  grind [get!, getRegion!]

def set (ptr: OperationPtr) (ctx: IRContext) (newOp: Operation) : IRContext :=
  {ctx with operations := ctx.operations.insert ptr newOp}

def setNextOp (op: OperationPtr) (ctx: IRContext) (newNext : Option OperationPtr)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx
  op.set ctx { oldOp with next := newNext}

def setNextOp! (op: OperationPtr) (ctx: IRContext) (newNext : Option OperationPtr) : IRContext :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with next := newNext}

@[grind _=_]
theorem setNextOp!_eq_setNextOp {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.setNextOp! ctx newNext = op.setNextOp ctx newNext inBounds := by
  grind [setNextOp, setNextOp!]

def setPrevOp (op: OperationPtr) (ctx: IRContext) (newPrev: Option OperationPtr)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with prev := newPrev}

def setPrevOp! (op: OperationPtr) (ctx: IRContext) (newPrev: Option OperationPtr) : IRContext :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with prev := newPrev}

@[grind _=_]
theorem setPrevOp!_eq_setPrevOp {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.setPrevOp! ctx newPrev = op.setPrevOp ctx newPrev inBounds := by
  grind [setPrevOp, setPrevOp!]

def setParent (op: OperationPtr) (ctx: IRContext) (newParent: Option BlockPtr)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with parent := newParent}

def setParent! (op: OperationPtr) (ctx: IRContext) (newParent: Option BlockPtr) : IRContext :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with parent := newParent}

@[grind _=_]
theorem setParent!_eq_setParent {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.setParent! ctx newParent = op.setParent ctx newParent inBounds := by
  grind [setParent, setParent!]

def setRegions (op: OperationPtr) (ctx: IRContext) (newRegions: Array RegionPtr)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with regions := newRegions}

def setRegions! (op: OperationPtr) (ctx: IRContext) (newRegions: Array RegionPtr) : IRContext :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with regions := newRegions}

@[grind _=_]
theorem setRegions!_eq_setRegions {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.setRegions! ctx newRegions = op.setRegions ctx newRegions inBounds := by
  grind [setRegions, setRegions!]

def setResults (op: OperationPtr) (ctx: IRContext) (newResults: Array OpResult)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with results := newResults}

def setResults! (op: OperationPtr) (ctx: IRContext) (newResults: Array OpResult) : IRContext :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with results := newResults}

@[grind _=_]
theorem setResults!_eq_setResults {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.setResults! ctx newResults = op.setResults ctx newResults inBounds := by
  grind [setResults, setResults!]

def pushResult (op : OperationPtr) (ctx : IRContext) (resultS : OpResult)
      (hop : op.InBounds ctx := by grind) :=
    op.setResults ctx ((op.get ctx).results.push resultS)

def pushResult! (op : OperationPtr) (ctx : IRContext) (resultS : OpResult) : IRContext :=
  op.setResults! ctx ((op.get! ctx).results.push resultS)

@[grind _=_]
theorem pushResult!_eq_pushResult {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.pushResult! ctx resultS = op.pushResult ctx resultS inBounds := by
  grind [pushResult, pushResult!]

def setBlockOperands (op: OperationPtr) (ctx: IRContext) (newOperands: Array BlockOperand)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx {oldOp with blockOperands := newOperands}

def setBlockOperands! (op: OperationPtr) (ctx: IRContext) (newOperands: Array BlockOperand) :
    IRContext :=
  let oldOp := op.get! ctx
  op.set ctx {oldOp with blockOperands := newOperands}

@[grind _=_]
theorem setBlockOperands!_eq_setBlockOperands {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.setBlockOperands! ctx newOperands = op.setBlockOperands ctx newOperands inBounds := by
  grind [setBlockOperands, setBlockOperands!]

def pushBlockOperand (op : OperationPtr) (ctx : IRContext) (operands : BlockOperand)
      (hop : op.InBounds ctx := by grind) :=
    op.setBlockOperands ctx ((op.get ctx).blockOperands.push operands)

def pushBlockOperand! (op : OperationPtr) (ctx : IRContext) (operands : BlockOperand) :
    IRContext :=
  op.setBlockOperands! ctx ((op.get! ctx).blockOperands.push operands)

@[grind _=_]
theorem pushBlockOperand!_eq_pushBlockOperand
    {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.pushBlockOperand! ctx operands = op.pushBlockOperand ctx operands inBounds := by
  grind [pushBlockOperand, pushBlockOperand!]

def setOperands (op: OperationPtr) (ctx: IRContext) (newOperands: Array OpOperand)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with operands := newOperands}

def setOperands! (op: OperationPtr) (ctx: IRContext) (newOperands: Array OpOperand) : IRContext :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with operands := newOperands}

@[grind _=_]
theorem setOperands!_eq_setOperands {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.setOperands! ctx newOperands = op.setOperands ctx newOperands inBounds := by
  grind [setOperands, setOperands!]

def pushOperand (op : OperationPtr) (ctx : IRContext) (operandS : OpOperand)
      (hop : op.InBounds ctx := by grind) :=
    op.setOperands ctx ((op.get ctx).operands.push operandS)

def pushOperand! (op : OperationPtr) (ctx : IRContext) (operands : OpOperand) : IRContext :=
  op.setOperands! ctx ((op.get! ctx).operands.push operands)

@[grind _=_]
theorem pushOperand!_eq_pushOperand {op : OperationPtr} (inBounds: op.InBounds ctx) :
    op.pushOperand! ctx operands = op.pushOperand ctx operands inBounds := by
  grind [pushOperand, pushOperand!]

@[inline]
def getProperties (op : OperationPtr) (ctx : IRContext) (opCode : OpCode)
    (inBounds : op.InBounds ctx := by grind)
    (hprop : (op.get ctx inBounds).opType = opCode := by grind) : propertiesOf opCode :=
  hprop ▸ (op.get ctx (by grind)).properties

@[inline]
def getProperties! (op : OperationPtr) (ctx : IRContext) (opCode : OpCode) : propertiesOf opCode :=
  if h : (op.get! ctx).opType = opCode then
    h ▸ (op.get! ctx).properties
  else
    default

@[grind _=_]
theorem getProperties!_eq_getProperties {op : OperationPtr} (inBounds: op.InBounds ctx)
    (hprop : (op.get! ctx).opType = opCode) :
    op.getProperties! ctx opCode = op.getProperties ctx opCode inBounds (by grind) := by
  grind [getProperties, getProperties!]

/--
  Get the properties of an operation without requiring a proof of in-bounds access or that
  the operation properties type matches the expected type.
-/
def getPropertiesFromOpType! (op : OperationPtr) (ctx : IRContext) (opType : OpCode) : propertiesOf opType :=
  if h : (op.get! ctx).opType = opType then
    h ▸ (op.get! ctx).properties
  else
    default

def setProperties (op : OperationPtr) (ctx : IRContext)
    (newProperties : propertiesOf opCode)
    (inBounds: op.InBounds ctx := by grind)
    (propEq : (op.get ctx inBounds).opType = opCode := by grind) : IRContext :=
  let oldOp := op.get ctx (by grind)
  op.set ctx { oldOp with properties := propEq ▸ newProperties }

def setProperties! (op: OperationPtr) (ctx: IRContext)
  (newProperties : propertiesOf opCode)
  (propEq : (op.get! ctx).opType = opCode := by grind) : IRContext :=
  let oldOp := op.get! ctx
  op.set ctx { oldOp with properties := propEq ▸ newProperties }

@[grind _=_]
theorem setProperties!_eq_setProperties {op : OperationPtr}
    (newProperties : propertiesOf opCode) (inBounds: op.InBounds ctx)
    (propEq : (op.get ctx inBounds).opType = opCode) :
    op.setProperties! ctx newProperties =
    op.setProperties ctx newProperties inBounds := by
  grind [setProperties, setProperties!]

@[grind]
def nextOperand (op : OperationPtr) (ctx : IRContext)
    (inBounds: op.InBounds ctx := by grind) : OpOperandPtr :=
  .mk op (op.getNumOperands ctx (by grind))

@[grind]
def nextOperand! (op : OperationPtr) (ctx : IRContext) : OpOperandPtr :=
  .mk op (op.getNumOperands! ctx)

@[grind]
def nextBlockOperand (op : OperationPtr) (ctx : IRContext)
    (inBounds: op.InBounds ctx := by grind) : BlockOperandPtr :=
  .mk op (op.getNumSuccessors ctx (by grind))

@[grind]
def nextBlockOperand! (op : OperationPtr) (ctx : IRContext) : BlockOperandPtr :=
  .mk op (op.getNumSuccessors! ctx)

@[grind]
def nextResult (op : OperationPtr) (ctx : IRContext)
    (inBounds: op.InBounds ctx := by grind) : OpResultPtr :=
  .mk op (op.getNumResults ctx (by grind))

@[grind]
def nextResult! (op : OperationPtr) (ctx : IRContext) : OpResultPtr :=
  .mk op (op.getNumResults! ctx)

def allocEmpty (ctx : IRContext) (opType : OpCode) (properties : propertiesOf opType) :
    Option (IRContext × OperationPtr) :=
  let newOpPtr : OperationPtr := ⟨ctx.nextID⟩
  let operation := Operation.empty opType properties
  if _ : ctx.operations.contains newOpPtr then none else
  let ctx := { ctx with nextID := ctx.nextID + 1 }
  let ctx := newOpPtr.set ctx operation
  (ctx, newOpPtr)

-- `inBounds` is unused as ExtHashMap does not require proof of key presence for `erase`.
-- We still keep it as an API consistency.
set_option linter.unusedVariables false in
def dealloc (op : OperationPtr) (ctx : IRContext)
    (inBounds: op.InBounds ctx := by grind) : IRContext :=
  { ctx with operations := ctx.operations.erase op }

end OperationPtr

/-
 OpOperandPtr accessors
-/

namespace OpOperandPtr

@[local grind]
def InBounds (operand: OpOperandPtr) (ctx: IRContext) : Prop :=
  ∃ h, operand.index < (operand.op.get ctx h).operands.size

theorem inBounds_def : InBounds opr ctx ↔ ∃ h, opr.index < opr.op.getNumOperands ctx h := by
  rfl

@[grind .]
theorem InBounds_iff (operand : OpOperandPtr) (ctx : IRContext) :
    operand.op.InBounds ctx →
    operand.index < operand.op.getNumOperands! ctx →
    operand.InBounds ctx :=
  by grind [inBounds_def]

def get (operand: OpOperandPtr) (ctx: IRContext) (operandIn: operand.InBounds ctx := by grind) : OpOperand :=
  (operand.op.get ctx (by grind [InBounds])).operands[operand.index]'(by grind [InBounds, OperationPtr.getNumOperands])

def get! (operand: OpOperandPtr) (ctx: IRContext) : OpOperand :=
  (operand.op.get! ctx).operands[operand.index]!

@[grind _=_]
theorem get!_eq_get {ptr : OpOperandPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem get!_eq_of_OperationPtr_get!_eq {opr : OpOperandPtr} :
    opr.op.get! ctx = opr.op.get! ctx' →
    opr.get! ctx = opr.get! ctx' := by
  grind [OperationPtr.get!, get!]

def set (operand: OpOperandPtr) (ctx: IRContext) (newOperand: OpOperand)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let op := operand.op.get ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        operands := op.operands.set operand.index newOperand (by grind)} }

def set! (operand: OpOperandPtr) (ctx: IRContext) (newOperand: OpOperand) : IRContext :=
  let op := operand.op.get! ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        operands := op.operands.set! operand.index newOperand } }

@[grind _=_]
theorem set!_eq_set {operand : OpOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.set! ctx newOperand = operand.set ctx newOperand inBounds := by
  grind [set, set!]

def setNextUse (operand: OpOperandPtr) (ctx: IRContext) (newNextUse: Option OpOperandPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with nextUse := newNextUse }

def setNextUse! (operand: OpOperandPtr) (ctx: IRContext) (newNextUse: Option OpOperandPtr) : IRContext :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with nextUse := newNextUse }

@[grind _=_]
theorem setNextUse!_eq_setNextUse {operand : OpOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.setNextUse! ctx newNextUse = operand.setNextUse ctx newNextUse inBounds := by
  grind [setNextUse, setNextUse!]

def setBack (operand: OpOperandPtr) (ctx: IRContext) (newBack: OpOperandPtrPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with back := newBack }

def setBack! (operand: OpOperandPtr) (ctx: IRContext) (newBack: OpOperandPtrPtr) : IRContext :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with back := newBack }

@[grind _=_]
theorem setBack!_eq_setBack {operand : OpOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.setBack! ctx newBack = operand.setBack ctx newBack inBounds := by
  grind [setBack, setBack!]

def setOwner (operand: OpOperandPtr) (ctx: IRContext) (newOwner: OperationPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with owner := newOwner }

def setOwner! (operand: OpOperandPtr) (ctx: IRContext) (newOwner: OperationPtr) : IRContext :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with owner := newOwner }

@[grind _=_]
theorem setOwner!_eq_setOwner {operand : OpOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.setOwner! ctx newOwner = operand.setOwner ctx newOwner inBounds := by
  grind [setOwner, setOwner!]

def setValue (operand: OpOperandPtr) (ctx: IRContext) (newValue: ValuePtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with value := newValue }

def setValue! (operand: OpOperandPtr) (ctx: IRContext) (newValue: ValuePtr) : IRContext :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with value := newValue }

@[grind _=_]
theorem setValue!_eq_setValue {operand : OpOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.setValue! ctx newValue = operand.setValue ctx newValue inBounds := by
  grind [setValue, setValue!]

end OpOperandPtr

@[grind =]
theorem OperationPtr.getOperand_eq_OpOperandPtr_get :
    OperationPtr.getOperand op ctx index opInBounds indexInBounds =
    (OpOperandPtr.get (OperationPtr.getOpOperand op index) ctx (by grind [OperationPtr.getOpOperand, OpOperandPtr.InBounds, OperationPtr.getNumOperands])).value := by
  grind [OpOperandPtr.get, OperationPtr.getOperand, OperationPtr.get, OperationPtr.getOpOperand]

/-
 BlockOperandPtr accessors
-/

namespace BlockOperandPtr

@[local grind]
def InBounds (operand: BlockOperandPtr) (ctx: IRContext) : Prop :=
  ∃ h, operand.index < (operand.op.get ctx h).blockOperands.size

theorem inBounds_def :
    InBounds opr ctx ↔ ∃ h, opr.index < opr.op.getNumSuccessors ctx h := by
  rfl

@[grind .]
theorem inBounds_of_OperationPtr_inBounds {operand : BlockOperandPtr} {ctx : IRContext} :
    operand.op.InBounds ctx →
    operand.index < operand.op.getNumSuccessors! ctx →
    operand.InBounds ctx :=
  by grind [inBounds_def]

def get (operand: BlockOperandPtr) (ctx: IRContext) (operandIn: operand.InBounds ctx := by grind) : BlockOperand :=
  (operand.op.get ctx (by grind [InBounds])).blockOperands[operand.index]'(by grind [InBounds])
def get! (operand: BlockOperandPtr) (ctx: IRContext) : BlockOperand :=
  operand.op.get! ctx |>.blockOperands[operand.index]!
@[grind _=_]
theorem get!_eq_get {ptr : BlockOperandPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!, OperationPtr.get!]

theorem get!_eq_of_OperationPtr_get!_eq {opr : BlockOperandPtr} :
    opr.op.get! ctx = opr.op.get! ctx' →
    opr.get! ctx = opr.get! ctx' := by
  grind [OperationPtr.get!, get!]

def set (operand: BlockOperandPtr) (ctx: IRContext) (newOperand: BlockOperand) (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let op := operand.op.get ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        blockOperands := op.blockOperands.set operand.index newOperand (by grind)} }

def set! (operand: BlockOperandPtr) (ctx: IRContext) (newOperand: BlockOperand) : IRContext :=
  let op := operand.op.get! ctx
  { ctx with
    operations := ctx.operations.insert operand.op
      { op with
        blockOperands := op.blockOperands.set! operand.index newOperand } }

@[grind _=_]
theorem set!_eq_set {operand : BlockOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.set! ctx newOperand = operand.set ctx newOperand inBounds := by
  grind [set, set!]

def setNextUse (operand: BlockOperandPtr) (ctx: IRContext) (newNextUse: Option BlockOperandPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with nextUse := newNextUse }

def setNextUse! (operand: BlockOperandPtr) (ctx: IRContext) (newNextUse: Option BlockOperandPtr) :
    IRContext :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with nextUse := newNextUse }

@[grind _=_]
theorem setNextUse!_eq_setNextUse {operand : BlockOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.setNextUse! ctx newNextUse = operand.setNextUse ctx newNextUse inBounds := by
  grind [setNextUse, setNextUse!]

def setBack (operand: BlockOperandPtr) (ctx: IRContext) (newBack: BlockOperandPtrPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with back := newBack }

def setBack! (operand: BlockOperandPtr) (ctx: IRContext) (newBack: BlockOperandPtrPtr) : IRContext :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with back := newBack }

theorem setBack!_eq_setBack {operand : BlockOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.setBack! ctx newBack = operand.setBack ctx newBack inBounds := by
  grind [setBack, setBack!]

def setOwner (operand: BlockOperandPtr) (ctx: IRContext) (newOwner: OperationPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with owner := newOwner }

def setOwner! (operand: BlockOperandPtr) (ctx: IRContext) (newOwner: OperationPtr) : IRContext :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with owner := newOwner }

@[grind _=_]
theorem setOwner!_eq_setOwner {operand : BlockOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.setOwner! ctx newOwner = operand.setOwner ctx newOwner inBounds := by
  grind [setOwner, setOwner!]

def setValue (operand: BlockOperandPtr) (ctx: IRContext) (newValue: BlockPtr)
    (operandIn: operand.InBounds ctx := by grind) : IRContext :=
  let oldOperand := operand.get ctx
  operand.set ctx { oldOperand with value := newValue }

def setValue! (operand: BlockOperandPtr) (ctx: IRContext) (newValue: BlockPtr) : IRContext :=
  let oldOperand := operand.get! ctx
  operand.set! ctx { oldOperand with value := newValue }

@[grind _=_]
theorem setValue!_eq_setValue {operand : BlockOperandPtr} (inBounds: operand.InBounds ctx) :
    operand.setValue! ctx newValue = operand.setValue ctx newValue inBounds := by
  grind [setValue, setValue!]

end BlockOperandPtr

/-
 OpResultPtr accessors
-/

namespace OpResultPtr

@[local grind]
def InBounds (result: OpResultPtr) (ctx: IRContext) : Prop :=
  ∃ h, result.index < (result.op.get ctx h).results.size

theorem inBounds_def : InBounds res ctx ↔ ∃ h, res.index < res.op.getNumResults ctx h := by
  rfl

@[grind .]
theorem inBounds_OperationPtr_getNumResults! (result: OpResultPtr) (ctx: IRContext) (h: result.InBounds ctx) :
    result.index < result.op.getNumResults! ctx := by
  simp [OperationPtr.getNumResults!, OperationPtr.get!]
  grind [OperationPtr.get]

@[grind .]
theorem inBounds_of {result : OpResultPtr} :
    result.op.InBounds ctx →
    result.index < result.op.getNumResults! ctx →
    result.InBounds ctx :=
  by grind [InBounds, OperationPtr.getNumResults!]

def get (result: OpResultPtr) (ctx: IRContext) (resultIn: result.InBounds ctx := by grind) : OpResult :=
  (result.op.get ctx (by grind [InBounds])).results[result.index]'(by grind [InBounds])

def get! (result: OpResultPtr) (ctx: IRContext) : OpResult :=
  (result.op.get! ctx).results[result.index]!

@[grind _=_]
theorem get!_eq_get {ptr : OpResultPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem get!_eq_of_OperationPtr_get!_eq {res : OpResultPtr} :
    res.op.get! ctx = res.op.get! ctx' →
    res.get! ctx = res.get! ctx' := by
  grind [OperationPtr.get!, get!]

def set (result: OpResultPtr) (ctx: IRContext) (newresult: OpResult) (resultIn: result.InBounds ctx := by grind) : IRContext :=
  let op := result.op.get ctx
  { ctx with
    operations := ctx.operations.insert result.op
      { op with results := op.results.set result.index newresult (by grind)} }

def set! (result: OpResultPtr) (ctx: IRContext) (newresult: OpResult) : IRContext :=
  let op := result.op.get! ctx
  { ctx with
    operations := ctx.operations.insert result.op
      { op with results := op.results.set! result.index newresult } }

@[grind _=_]
theorem set!_eq_set {result : OpResultPtr} (inBounds: result.InBounds ctx) :
    result.set! ctx newresult = result.set ctx newresult inBounds := by
  grind [set, set!]

def setType (result: OpResultPtr) (ctx: IRContext) (newType: TypeAttr)
    (resultIn: result.InBounds ctx := by grind) : IRContext :=
  let oldResult := result.get ctx
  result.set ctx { oldResult with type := newType }

def setType! (result: OpResultPtr) (ctx: IRContext) (newType: TypeAttr) : IRContext :=
  let oldResult := result.get! ctx
  result.set! ctx { oldResult with type := newType }

@[grind _=_]
theorem setType!_eq_setType {result : OpResultPtr} (inBounds: result.InBounds ctx) :
    result.setType! ctx newType = result.setType ctx newType inBounds := by
  grind [setType, setType!]

def setFirstUse (result: OpResultPtr) (ctx: IRContext) (newFirstUse: Option OpOperandPtr)
    (resultIn: result.InBounds ctx := by grind) : IRContext :=
  let oldResult := result.get ctx
  result.set ctx { oldResult with firstUse := newFirstUse }

def setFirstUse! (result: OpResultPtr) (ctx: IRContext) (newFirstUse: Option OpOperandPtr) : IRContext :=
  let oldResult := result.get! ctx
  result.set! ctx { oldResult with firstUse := newFirstUse }

@[grind _=_]
theorem setFirstUse!_eq_setFirstUse {result : OpResultPtr} (inBounds: result.InBounds ctx) :
    result.setFirstUse! ctx newFirstUse = result.setFirstUse ctx newFirstUse inBounds := by
  grind [setFirstUse, setFirstUse!]

def setOwner (result: OpResultPtr) (ctx: IRContext) (newOwner: OperationPtr)
    (resultIn: result.InBounds ctx := by grind) : IRContext :=
  let oldResult := result.get ctx
  result.set ctx { oldResult with owner := newOwner }

def setOwner! (result: OpResultPtr) (ctx: IRContext) (newOwner: OperationPtr) : IRContext :=
  let oldResult := result.get! ctx
  result.set! ctx { oldResult with owner := newOwner }

@[grind _=_]
theorem setOwner!_eq_setOwner {result : OpResultPtr} (inBounds: result.InBounds ctx) :
    result.setOwner! ctx newOwner = result.setOwner ctx newOwner inBounds := by
  grind [setOwner, setOwner!]

end OpResultPtr

/-
 BlockPtr accessors
-/

namespace BlockPtr

def InBounds (block: BlockPtr) (ctx: IRContext) : Prop :=
  block ∈ ctx.blocks

def get (ptr: BlockPtr) (ctx: IRContext) (inBounds: ptr.InBounds ctx := by grind) : Block :=
  ctx.blocks[ptr]'(by unfold InBounds at inBounds; grind)

def get! (ptr: BlockPtr) (ctx: IRContext) : Block := ctx.blocks[ptr]!

@[grind _=_]
theorem get!_eq_get {ptr : BlockPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

def set (ptr: BlockPtr) (ctx: IRContext) (newBlock: Block) : IRContext :=
  {ctx with blocks := ctx.blocks.insert ptr newBlock}

def setParent (block: BlockPtr) (ctx: IRContext) (newParent: Option RegionPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with parent := newParent}

def setParent! (block: BlockPtr) (ctx: IRContext) (newParent: Option RegionPtr) : IRContext :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with parent := newParent}

@[grind _=_]
theorem setParent!_eq_setParent {block : BlockPtr} (inBounds: block.InBounds ctx) :
    block.setParent! ctx newParent = block.setParent ctx newParent inBounds := by
  grind [setParent, setParent!]

def setFirstUse (block: BlockPtr) (ctx: IRContext) (newFirstUse: Option BlockOperandPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with firstUse := newFirstUse}

def setFirstUse! (block: BlockPtr) (ctx: IRContext) (newFirstUse: Option BlockOperandPtr) : IRContext :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with firstUse := newFirstUse}

@[grind _=_]
theorem setFirstUse!_eq_setFirstUse {block : BlockPtr} (inBounds: block.InBounds ctx) :
    block.setFirstUse! ctx newFirstUse = block.setFirstUse ctx newFirstUse inBounds := by
  grind [setFirstUse, setFirstUse!]

def setFirstOp (block: BlockPtr) (ctx: IRContext) (newFirstOp: Option OperationPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with firstOp := newFirstOp}

def setFirstOp! (block: BlockPtr) (ctx: IRContext) (newFirstOp: Option OperationPtr) : IRContext :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with firstOp := newFirstOp}

@[grind _=_]
theorem setFirstOp!_eq_setFirstOp {block : BlockPtr} (inBounds: block.InBounds ctx) :
    block.setFirstOp! ctx newFirstOp = block.setFirstOp ctx newFirstOp inBounds := by
  grind [setFirstOp, setFirstOp!]

def setLastOp (block: BlockPtr) (ctx: IRContext) (newLastOp: Option OperationPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with lastOp := newLastOp}

def setLastOp! (block: BlockPtr) (ctx: IRContext) (newLastOp: Option OperationPtr) : IRContext :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with lastOp := newLastOp}

@[grind _=_]
theorem setLastOp!_eq_setLastOp {block : BlockPtr} (inBounds: block.InBounds ctx) :
    block.setLastOp! ctx newLastOp = block.setLastOp ctx newLastOp inBounds := by
  grind [setLastOp, setLastOp!]

def setNextBlock (block: BlockPtr) (ctx: IRContext) (newNext: Option BlockPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with next := newNext}

def setNextBlock! (block: BlockPtr) (ctx: IRContext) (newNext: Option BlockPtr) : IRContext :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with next := newNext}

@[grind _=_]
theorem setNextBlock!_eq_setNextBlock {block : BlockPtr} (inBounds: block.InBounds ctx) :
    block.setNextBlock! ctx newNext = block.setNextBlock ctx newNext inBounds := by
  grind [setNextBlock, setNextBlock!]

def setPrevBlock (block: BlockPtr) (ctx: IRContext) (newPrev: Option BlockPtr)
    (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx
  block.set ctx { oldBlock with prev := newPrev}

def setPrevBlock! (block: BlockPtr) (ctx: IRContext) (newPrev: Option BlockPtr) : IRContext :=
  let oldBlock := block.get! ctx
  block.set ctx {oldBlock with prev := newPrev}

@[grind _=_]
theorem setPrevBlock!_eq_setPrevBlock {block : BlockPtr} (inBounds: block.InBounds ctx) :
    block.setPrevBlock! ctx newPrev = block.setPrevBlock ctx newPrev inBounds := by
  grind [setPrevBlock, setPrevBlock!]

def allocEmpty (ctx: IRContext) : Option (IRContext × BlockPtr) :=
  let newBlockPtr: BlockPtr := ⟨ctx.nextID⟩
  let ctx : IRContext := { ctx with nextID := ctx.nextID + 1}
  if _ : ctx.blocks.contains newBlockPtr then none else
  let ctx := newBlockPtr.set ctx Block.empty
  some (ctx, newBlockPtr)

theorem allocEmpty_def (heq : allocEmpty ctx = some (ctx', ptr')) :
    ctx' = set ⟨ctx.nextID⟩ {ctx with nextID := ctx.nextID + 1} Block.empty := by
  grind [allocEmpty]

def getNumArguments (block: BlockPtr) (ctx: IRContext) (inBounds: block.InBounds ctx := by grind) : Nat :=
  (block.get ctx (by grind)).arguments.size

def getNumArguments! (block: BlockPtr) (ctx: IRContext) : Nat :=
  (block.get! ctx).arguments.size

@[grind _=_]
theorem getNumArguments!_eq_getNumArguments {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getNumArguments! ctx = block.getNumArguments ctx (by grind) := by
  grind [getNumArguments, getNumArguments!]

theorem getNumArguments!_eq_of_BlockPtr_get!_eq {block : BlockPtr} :
    block.get! ctx = block.get! ctx' →
    block.getNumArguments! ctx = block.getNumArguments! ctx' := by
  grind [getNumArguments!]

def getArgument (block: BlockPtr) (index: Nat) : BlockArgumentPtr :=
  { block := block, index := index }

@[simp, grind =]
theorem getArgument_index {block : BlockPtr} {index : Nat} :
    (getArgument block index).index = index := by
  grind [getArgument]

@[simp, grind =]
theorem getArgument_block {block : BlockPtr} {index : Nat} :
    (getArgument block index).block = block := by
  grind [getArgument]

def setArguments (block: BlockPtr) (ctx: IRContext)
    (newArguments: Array BlockArgument) (inBounds: block.InBounds ctx := by grind) : IRContext :=
  let oldBlock := block.get ctx (by grind)
  block.set ctx { oldBlock with arguments := newArguments }

def setArguments! (block: BlockPtr) (ctx: IRContext) (newArguments: Array BlockArgument) :
    IRContext :=
  let oldBlock := block.get! ctx
  block.set ctx { oldBlock with arguments := newArguments }

@[grind _=_]
theorem setArguments!_eq_setArguments {block : BlockPtr} (inBounds: block.InBounds ctx) :
    block.setArguments! ctx newArguments = block.setArguments ctx newArguments inBounds := by
  grind [setArguments, setArguments!]

def pushArgument (block : BlockPtr) (ctx : IRContext) (result : BlockArgument)
      (inBounds : block.InBounds ctx := by grind) :=
    block.setArguments ctx ((block.get ctx).arguments.push result)

def pushArgument! (block : BlockPtr) (ctx : IRContext) (result : BlockArgument) : IRContext :=
  block.setArguments! ctx ((block.get! ctx).arguments.push result)

@[grind _=_]
theorem pushArgument!_eq_pushArgument {block : BlockPtr} (inBounds: block.InBounds ctx) :
    block.pushArgument! ctx result = block.pushArgument ctx result inBounds := by
  grind [pushArgument, pushArgument!]

end BlockPtr

/-
 BlockArgumentPtr accessors
-/

namespace BlockArgumentPtr

@[local grind]
def InBounds (arg: BlockArgumentPtr) (ctx: IRContext) : Prop :=
  ∃ h, arg.index < (arg.block.get ctx h).arguments.size

def get (arg: BlockArgumentPtr) (ctx: IRContext) (argIn: arg.InBounds ctx := by grind) : BlockArgument :=
  (arg.block.get ctx (by grind [InBounds])).arguments[arg.index]'(by grind [InBounds])

def get! (arg: BlockArgumentPtr) (ctx: IRContext) : BlockArgument :=
  (arg.block.get! ctx).arguments[arg.index]!

@[grind _=_]
theorem get!_eq_get {ptr : BlockArgumentPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem get!_eq_of_BlockPtr_get!_eq {arg : BlockArgumentPtr} :
    arg.block.get! ctx = arg.block.get! ctx' →
    arg.get! ctx = arg.get! ctx' := by
  grind [BlockPtr.get!, get!]

def set (arg: BlockArgumentPtr) (ctx: IRContext) (newresult: BlockArgument) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let block := arg.block.get ctx
  { ctx with
    blocks := ctx.blocks.insert arg.block
      { block with arguments := block.arguments.set arg.index newresult (by grind)} }

def set! (arg: BlockArgumentPtr) (ctx: IRContext) (newresult: BlockArgument) : IRContext :=
  let block := arg.block.get! ctx
  { ctx with
    blocks := ctx.blocks.insert arg.block
      { block with arguments := block.arguments.set! arg.index newresult } }

@[grind _=_]
theorem set!_eq_set {arg : BlockArgumentPtr} (inBounds: arg.InBounds ctx) :
    arg.set! ctx newresult = arg.set ctx newresult inBounds := by
  grind [set, set!]

def setType (arg: BlockArgumentPtr) (ctx: IRContext) (newType: TypeAttr) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with type := newType }

def setType! (arg: BlockArgumentPtr) (ctx: IRContext) (newType: TypeAttr) : IRContext :=
  let oldResult := arg.get! ctx
  arg.set! ctx { oldResult with type := newType }

@[grind _=_]
theorem setType!_eq_setType {arg : BlockArgumentPtr} (inBounds: arg.InBounds ctx) :
    arg.setType! ctx newType = arg.setType ctx newType inBounds := by
  grind [setType, setType!]

def setFirstUse (arg: BlockArgumentPtr) (ctx: IRContext) (newFirstUse: Option OpOperandPtr) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with firstUse := newFirstUse }

def setFirstUse! (arg: BlockArgumentPtr) (ctx: IRContext) (newFirstUse: Option OpOperandPtr) :
    IRContext :=
  let oldResult := arg.get! ctx
  arg.set! ctx {oldResult with firstUse := newFirstUse}

@[grind _=_]
theorem setFirstUse!_eq_setFirstUse {arg : BlockArgumentPtr} (inBounds: arg.InBounds ctx) :
    arg.setFirstUse! ctx newFirstUse = arg.setFirstUse ctx newFirstUse inBounds := by
  grind [setFirstUse, setFirstUse!]

def setIndex (arg: BlockArgumentPtr) (ctx: IRContext) (newIndex: Nat) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with index := newIndex }

def setIndex! (arg: BlockArgumentPtr) (ctx: IRContext) (newIndex: Nat) : IRContext :=
  let oldResult := arg.get! ctx
  arg.set! ctx {oldResult with index := newIndex}

@[grind _=_]
theorem setIndex!_eq_setIndex {arg : BlockArgumentPtr} (inBounds: arg.InBounds ctx) :
    arg.setIndex! ctx newIndex = arg.setIndex ctx newIndex inBounds := by
  grind [setIndex, setIndex!]

def setLoc (arg: BlockArgumentPtr) (ctx: IRContext) (newLoc: Location) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with loc := newLoc }

def setLoc! (arg: BlockArgumentPtr) (ctx: IRContext) (newLoc: Location) : IRContext :=
  let oldResult := arg.get! ctx
  arg.set! ctx {oldResult with loc := newLoc}

@[grind _=_]
theorem setLoc!_eq_setLoc {arg : BlockArgumentPtr} (inBounds: arg.InBounds ctx) :
    arg.setLoc! ctx newLoc = arg.setLoc ctx newLoc inBounds := by
  grind [setLoc, setLoc!]

def setOwner (arg: BlockArgumentPtr) (ctx: IRContext) (newOwner: BlockPtr) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  let oldResult := arg.get ctx
  arg.set ctx { oldResult with owner := newOwner }

def setOwner! (arg: BlockArgumentPtr) (ctx: IRContext) (newOwner: BlockPtr) : IRContext :=
  let oldResult := arg.get! ctx
  arg.set! ctx {oldResult with owner := newOwner}

@[grind _=_]
theorem setOwner!_eq_setOwner {arg : BlockArgumentPtr} (inBounds: arg.InBounds ctx) :
    arg.setOwner! ctx newOwner = arg.setOwner ctx newOwner inBounds := by
  grind [setOwner, setOwner!]

end BlockArgumentPtr

/-
 ValuePtr accessors
-/

namespace ValuePtr

inductive InBounds : ValuePtr → IRContext → Prop
| op_result ptr ctx : ptr.InBounds ctx → (opResult ptr).InBounds ctx
| block_argument ptr ctx : ptr.InBounds ctx → (blockArgument ptr).InBounds ctx

@[simp, grind=]
theorem inBounds_opResult (ptr: OpResultPtr) (ctx: IRContext) :
    (opResult ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [InBounds]

@[simp, grind=]
theorem inBounds_blockArg (ptr: BlockArgumentPtr) (ctx: IRContext) :
    (blockArgument ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [InBounds]

def getType (arg: ValuePtr) (ctx: IRContext) (argIn: arg.InBounds ctx := by grind) : TypeAttr :=
  match arg with
  | opResult ptr => (ptr.get ctx (by grind)).type
  | blockArgument ptr => (ptr.get ctx (by grind)).type

def getType! (arg: ValuePtr) (ctx: IRContext) : TypeAttr :=
  match arg with
  | opResult ptr => (ptr.get! ctx).type
  | blockArgument ptr => (ptr.get! ctx).type

@[grind _=_]
theorem getType!_eq_getType {ptr : ValuePtr} (hin : ptr.InBounds ctx) :
    ptr.getType! ctx = ptr.getType ctx hin := by
  unfold getType getType!; grind

def getFirstUse (arg: ValuePtr) (ctx: IRContext) (argIn: arg.InBounds ctx := by grind) : Option OpOperandPtr :=
  match arg with
  | opResult ptr => (ptr.get ctx).firstUse
  | blockArgument ptr => (ptr.get ctx).firstUse

def getFirstUse! (arg: ValuePtr) (ctx: IRContext) : Option OpOperandPtr :=
  match arg with
  | opResult ptr => (ptr.get! ctx).firstUse
  | blockArgument ptr => (ptr.get! ctx).firstUse

@[grind _=_]
theorem getFirstUse!_eq_getFirstUse {ptr : ValuePtr} (hin : ptr.InBounds ctx) :
    ptr.getFirstUse! ctx = ptr.getFirstUse ctx hin := by
  unfold getFirstUse getFirstUse!; grind

@[simp, grind =]
theorem getFirstUse_opResult_eq {res : OpResultPtr} {ctx : IRContext} {h : res.InBounds ctx} :
    (opResult res).getFirstUse ctx = (res.get ctx).firstUse := by
  grind [getFirstUse]

@[simp, grind =]
theorem getFirstUse_blockArgument_eq {ba : BlockArgumentPtr} {ctx : IRContext} {h : ba.InBounds ctx} :
    (blockArgument ba).getFirstUse ctx = (ba.get ctx).firstUse := by
  grind [getFirstUse]

@[simp, grind =]
theorem getFirstUse!_opResult_eq {res : OpResultPtr} {ctx : IRContext} :
    (opResult res).getFirstUse! ctx = (res.get! ctx).firstUse := by
  grind [getFirstUse!]

@[simp, grind =]
theorem getFirstUse!_blockArgument_eq {ba : BlockArgumentPtr} {ctx : IRContext} :
    (blockArgument ba).getFirstUse! ctx = (ba.get! ctx).firstUse := by
  grind [getFirstUse!]

/--
  Returns true if the value has any uses.
-/
def hasUses (value: ValuePtr) (ctx: IRContext) (valueIn: value.InBounds ctx := by grind) : Bool :=
  (value.getFirstUse ctx (by grind)).isSome

theorem hasUses_def {value : ValuePtr} (valueIn: value.InBounds ctx) :
    value.hasUses ctx = (value.getFirstUse ctx).isSome := by
  rfl

/--
  Returns true if the value has any uses.
-/
def hasUses! (value: ValuePtr) (ctx: IRContext) : Bool :=
  (value.getFirstUse! ctx).isSome

@[grind _=_]
theorem hasUses!_eq_hasUses {ptr : ValuePtr} (hin : ptr.InBounds ctx) :
    ptr.hasUses! ctx = ptr.hasUses ctx hin := by
  unfold hasUses hasUses!; grind

theorem hasUses!_def {value : ValuePtr} :
    value.hasUses! ctx = (value.getFirstUse! ctx).isSome := by
  grind [hasUses!]

def setType (arg: ValuePtr) (ctx: IRContext) (newType: TypeAttr) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  match arg with
  | opResult ptr => ptr.setType ctx newType
  | blockArgument ptr => ptr.setType ctx newType

def setType! (arg: ValuePtr) (ctx: IRContext) (newType: TypeAttr) : IRContext :=
  match arg with
  | opResult ptr => ptr.setType! ctx newType
  | blockArgument ptr => ptr.setType! ctx newType

@[grind _=_]
theorem setType!_eq_setType {arg : ValuePtr} (inBounds: arg.InBounds ctx) :
    arg.setType! ctx newType = arg.setType ctx newType inBounds := by
  grind [setType, setType!, cases ValuePtr]

def setFirstUse (arg: ValuePtr) (ctx: IRContext) (newFirstUse: Option OpOperandPtr) (argIn: arg.InBounds ctx := by grind) : IRContext :=
  match arg with
  | opResult ptr => ptr.setFirstUse ctx newFirstUse
  | blockArgument ptr => ptr.setFirstUse ctx newFirstUse

def setFirstUse! (arg: ValuePtr) (ctx: IRContext) (newFirstUse: Option OpOperandPtr) : IRContext :=
  match arg with
  | opResult ptr => ptr.setFirstUse! ctx newFirstUse
  | blockArgument ptr => ptr.setFirstUse! ctx newFirstUse

@[grind _=_]
theorem setFirstUse!_eq_setFirstUse {arg : ValuePtr} (inBounds: arg.InBounds ctx) :
    arg.setFirstUse! ctx newFirstUse = arg.setFirstUse ctx newFirstUse inBounds := by
  grind [setFirstUse, setFirstUse!, cases ValuePtr]

@[simp, grind =]
theorem setFirstUse_OpResultPtr (ptr: OpResultPtr) (ctx: IRContext)
    (ptrIn: (opResult ptr).InBounds ctx) (newFirstUse: Option OpOperandPtr) :
    (opResult ptr).setFirstUse ctx newFirstUse ptrIn = ptr.setFirstUse ctx newFirstUse := by
  unfold setFirstUse; grind

@[simp, grind =]
theorem setFirstUse_BlockArgumentPtr (ptr: BlockArgumentPtr) (ctx: IRContext)
    (ptrIn: (blockArgument ptr).InBounds ctx) (newFirstUse: Option OpOperandPtr) :
    (blockArgument ptr).setFirstUse ctx newFirstUse ptrIn = ptr.setFirstUse ctx newFirstUse := by
  unfold setFirstUse; rfl

@[simp, grind =]
theorem setType_OpResultPtr (ptr: OpResultPtr) (ctx: IRContext)
    (ptrIn: (opResult ptr).InBounds ctx) (newType: TypeAttr) :
    (opResult ptr).setType ctx newType ptrIn = ptr.setType ctx newType := by
  unfold setType; rfl

@[simp, grind =]
theorem setType_BlockArgumentPtr (ptr: BlockArgumentPtr) (ctx: IRContext)
    (ptrIn: (blockArgument ptr).InBounds ctx) (newType: TypeAttr) :
    (blockArgument ptr).setType ctx newType ptrIn = ptr.setType ctx newType := by
  unfold setType; rfl

end ValuePtr

/-
  OpOperandPtrPtr accessors
-/

namespace OpOperandPtrPtr

inductive InBounds (ctx: IRContext) : OpOperandPtrPtr → Prop
  | operandNextUseInBounds ptr : ptr.InBounds ctx → (operandNextUse ptr).InBounds ctx
  | valueFirstUseInBounds ptr : ptr.InBounds ctx → (valueFirstUse ptr).InBounds ctx

@[simp, grind=]
theorem inBounds_operandNextUse (ptr: OpOperandPtr) (ctx: IRContext) :
    (operandNextUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [InBounds]

@[simp, grind=]
theorem inBounds_valueFirstUse (ptr: ValuePtr) (ctx: IRContext) :
    (valueFirstUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [InBounds]

def get (ptrPtr: OpOperandPtrPtr) (ctx: IRContext) (ptrPtrIn: ptrPtr.InBounds ctx := by grind) : Option OpOperandPtr :=
  match ptrPtr with
  | operandNextUse ptr => (ptr.get ctx).nextUse
  | valueFirstUse val => val.getFirstUse ctx (by grind)

def get! (ptrPtr: OpOperandPtrPtr) (ctx: IRContext) : Option OpOperandPtr :=
  match ptrPtr with
  | operandNextUse ptr => (ptr.get! ctx).nextUse
  | valueFirstUse val => val.getFirstUse! ctx

@[grind _=_]
theorem get!_eq_get {ptrPtr : OpOperandPtrPtr} (hin : ptrPtr.InBounds ctx) :
    ptrPtr.get! ctx = ptrPtr.get ctx hin := by
  unfold get get!; grind

@[simp, grind =]
theorem get_operandNextUse_eq {ptr: OpOperandPtr} {ctx: IRContext} {ptrIn: ptr.InBounds ctx} :
    (operandNextUse ptr).get ctx (by grind) = (ptr.get ctx).nextUse := by
  grind [get]

@[simp, grind =]
theorem get!_operandNextUse_eq {ptr: OpOperandPtr} {ctx: IRContext} :
    (operandNextUse ptr).get! ctx = (ptr.get! ctx).nextUse := by
  grind [get!]

@[simp, grind =]
theorem get_valueFirstUse_eq {ptr: ValuePtr} {ctx: IRContext} {ptrIn: ptr.InBounds ctx} :
    (valueFirstUse ptr).get ctx (by grind) = ptr.getFirstUse ctx := by
  grind [get]

@[simp, grind =]
theorem get!_valueFirstUse_eq {ptr: ValuePtr} {ctx: IRContext} :
    (valueFirstUse ptr).get! ctx = ptr.getFirstUse! ctx := by
  grind [get!]

def set (ptrPtr: OpOperandPtrPtr) (ctx: IRContext) (newValue: Option OpOperandPtr) (ptrPtrIn: ptrPtr.InBounds ctx := by grind) : IRContext :=
  match ptrPtr with
  | operandNextUse ptr =>
    ptr.setNextUse ctx newValue
  | valueFirstUse val =>
    val.setFirstUse ctx newValue

def set! (ptrPtr: OpOperandPtrPtr) (ctx: IRContext) (newValue: Option OpOperandPtr) : IRContext :=
  match ptrPtr with
  | operandNextUse ptr =>
    ptr.setNextUse! ctx newValue
  | valueFirstUse val =>
    val.setFirstUse! ctx newValue

theorem set!_eq_set {ptrPtr : OpOperandPtrPtr} (inBounds: ptrPtr.InBounds ctx) :
    ptrPtr.set! ctx newValue = ptrPtr.set ctx newValue inBounds := by
  grind [set, set!, cases OpOperandPtrPtr]

@[simp]
theorem set_operandNextUse (ptr: OpOperandPtr) (ctx: IRContext) (newValue: Option OpOperandPtr) (ptrIn: (operandNextUse ptr).InBounds ctx) :
    (operandNextUse ptr).set ctx newValue ptrIn = ptr.setNextUse ctx newValue := by
  unfold set; rfl

@[simp]
theorem set_valueFirstUse (ptr: ValuePtr) (ctx: IRContext) (ptrIn: (valueFirstUse ptr).InBounds ctx) (newValue: Option OpOperandPtr) :
    (valueFirstUse ptr).set ctx newValue ptrIn = ptr.setFirstUse ctx newValue := by
  unfold set; rfl

end OpOperandPtrPtr

/-
  RegionPtr accessors
-/

namespace RegionPtr

def InBounds (region: RegionPtr) (ctx: IRContext) : Prop :=
  region ∈ ctx.regions

def get (ptr: RegionPtr) (ctx: IRContext) (inBounds: ptr.InBounds ctx := by grind) : Region :=
  ctx.regions[ptr]'(by unfold InBounds at inBounds; grind)

def get! (ptr: RegionPtr) (ctx: IRContext) : Region := ctx.regions[ptr]!

@[grind _=_]
theorem get!_eq_get {ptr : RegionPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

def set (ptr: RegionPtr) (ctx: IRContext) (newRegion: Region) : IRContext :=
  {ctx with regions := ctx.regions.insert ptr newRegion}

def setParent (region: RegionPtr) (ctx: IRContext) (newParent: OperationPtr)
    (inBounds: region.InBounds ctx := by grind) : IRContext :=
  let oldRegion := region.get ctx (by grind)
  region.set ctx { oldRegion with parent := newParent}

def setParent! (region: RegionPtr) (ctx: IRContext) (newParent: OperationPtr) : IRContext :=
  let oldRegion := region.get! ctx
  region.set ctx {oldRegion with parent := newParent}

@[grind _=_]
theorem setParent!_eq_setParent {region : RegionPtr} (inBounds: region.InBounds ctx) :
    region.setParent! ctx newParent = region.setParent ctx newParent inBounds := by
  grind [setParent, setParent!]

def setFirstBlock (region: RegionPtr) (ctx: IRContext) (newFirstBlock: Option BlockPtr)
    (inBounds: region.InBounds ctx := by grind) : IRContext :=
  let oldRegion := region.get ctx (by grind)
  region.set ctx { oldRegion with firstBlock := newFirstBlock}

def setFirstBlock! (region: RegionPtr) (ctx: IRContext) (newFirstBlock: Option BlockPtr) : IRContext :=
  let oldRegion := region.get! ctx
  region.set ctx {oldRegion with firstBlock := newFirstBlock}

@[grind _=_]
theorem setFirstBlock!_eq_setFirstBlock {region : RegionPtr} (inBounds: region.InBounds ctx) :
    region.setFirstBlock! ctx newFirstBlock = region.setFirstBlock ctx newFirstBlock inBounds := by
  grind [setFirstBlock, setFirstBlock!]

def setLastBlock (region: RegionPtr) (ctx: IRContext) (newLastBlock: Option BlockPtr)
    (inBounds: region.InBounds ctx := by grind) : IRContext :=
  let oldRegion := region.get ctx (by grind)
  region.set ctx { oldRegion with lastBlock := newLastBlock}

def setLastBlock! (region: RegionPtr) (ctx: IRContext) (newLastBlock: Option BlockPtr) : IRContext :=
  let oldRegion := region.get! ctx
  region.set ctx {oldRegion with lastBlock := newLastBlock}

@[grind _=_]
theorem setLastBlock!_eq_setLastBlock {region : RegionPtr} (inBounds: region.InBounds ctx) :
    region.setLastBlock! ctx newLastBlock = region.setLastBlock ctx newLastBlock inBounds := by
  grind [setLastBlock, setLastBlock!]

def allocEmpty (ctx: IRContext) : Option (IRContext × RegionPtr) :=
  let newRegionPtr: RegionPtr := ⟨ctx.nextID⟩
  let region := Region.empty
  let ctx := { ctx with nextID := ctx.nextID + 1}
  if _ : ctx.regions.contains newRegionPtr then none else
  let ctx := newRegionPtr.set ctx region
  (ctx, newRegionPtr)

end RegionPtr

/-
  BlockOperandPtrPtr accessors
-/

namespace BlockOperandPtrPtr

@[local grind]
inductive InBounds (ctx: IRContext) : BlockOperandPtrPtr → Prop
  | blockOperandNextUseInBounds ptr : ptr.InBounds ctx → (blockOperandNextUse ptr).InBounds ctx
  | blockFirstUseInBounds ptr : ptr.InBounds ctx → (blockFirstUse ptr).InBounds ctx

@[simp, grind=]
theorem inBounds_operandNextUse (ptr: BlockOperandPtr) (ctx: IRContext) :
    (blockOperandNextUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[simp, grind=]
theorem inBounds_valueFirstUse (ptr: BlockPtr) (ctx: IRContext) :
    (blockFirstUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind

def get (ptrPtr: BlockOperandPtrPtr) (ctx: IRContext) (ptrPtrIn: ptrPtr.InBounds ctx := by grind) : Option BlockOperandPtr :=
  match ptrPtr with
  | blockOperandNextUse ptr => (ptr.get ctx).nextUse
  | blockFirstUse val => (val.get ctx (by grind)).firstUse

def get! (ptrPtr: BlockOperandPtrPtr) (ctx: IRContext) : Option BlockOperandPtr :=
  match ptrPtr with
  | blockOperandNextUse ptr => (ptr.get! ctx).nextUse
  | blockFirstUse val => (val.get! ctx).firstUse

@[grind _=_]
theorem get!_eq_get {ptrPtr : BlockOperandPtrPtr} (hin : ptrPtr.InBounds ctx) :
    ptrPtr.get! ctx = ptrPtr.get ctx hin := by
  unfold get get!; grind

@[grind =]
theorem get_nextUse_eq {bo : BlockOperandPtr} {h : bo.InBounds ctx} :
    (blockOperandNextUse bo).get ctx = (bo.get ctx).nextUse := by
  grind [get]

@[grind =]
theorem get_firstUse_eq {bl : BlockPtr} {h : bl.InBounds ctx} :
    (blockFirstUse bl).get ctx = (bl.get ctx).firstUse := by
  grind [get]

def set (ptrPtr: BlockOperandPtrPtr) (ctx: IRContext) (newValue: Option BlockOperandPtr) (ptrPtrIn: ptrPtr.InBounds ctx := by grind) : IRContext :=
  match ptrPtr with
  | blockOperandNextUse ptr => ptr.setNextUse ctx newValue
  | blockFirstUse val => val.setFirstUse ctx newValue

def set! (ptrPtr: BlockOperandPtrPtr) (ctx: IRContext) (newValue: Option BlockOperandPtr) :
    IRContext :=
  match ptrPtr with
  | blockOperandNextUse ptr => ptr.setNextUse! ctx newValue
  | blockFirstUse val => val.setFirstUse! ctx newValue

@[grind _=_]
theorem set!_eq_set {ptrPtr : BlockOperandPtrPtr} (inBounds: ptrPtr.InBounds ctx) :
    ptrPtr.set! ctx newValue = ptrPtr.set ctx newValue inBounds := by
  grind [set, set!, cases BlockOperandPtrPtr]

@[simp, grind =]
theorem set_operandNextUse_eq {ptr: BlockOperandPtr} {ptrIn: ptr.InBounds ctx} {newValue: Option BlockOperandPtr} :
    (blockOperandNextUse ptr).set ctx newValue = ptr.setNextUse ctx newValue := by
  rfl

@[simp, grind =]
theorem set_blockFirstUse_eq {ptr: BlockPtr} {ptrIn: ptr.InBounds ctx} {newValue: Option BlockOperandPtr} :
    (blockFirstUse ptr).set ctx newValue = ptr.setFirstUse ctx newValue := by
  rfl

end BlockOperandPtrPtr

namespace OperationPtr

def hasUses.loop (op: OperationPtr) (ctx : IRContext) (index : Nat)
    (opIn: op.InBounds ctx := by grind)
    (hresult : index < op.getNumResults ctx := by grind) : Bool :=
  if ((op.getResult index).get ctx).firstUse.isSome then
    true
  else
    match index with
    | 0 => false
    | index' + 1 => hasUses.loop op ctx index'

def hasUses (op: OperationPtr) (ctx: IRContext) (opIn: op.InBounds ctx := by grind) : Bool :=
  let numResults := op.getNumResults ctx
  if h: numResults = 0 then
    false
  else
    hasUses.loop op ctx (numResults - 1)

def hasUses!.loop (op: OperationPtr) (ctx : IRContext) (index : Nat) : Bool :=
  if ((op.getResult index).get! ctx).firstUse.isSome then
    true
  else
    match index with
    | 0 => false
    | index' + 1 => hasUses!.loop op ctx index'

def hasUses! (op: OperationPtr) (ctx: IRContext) : Bool :=
  let numResults := op.getNumResults! ctx
  if numResults = 0 then
    false
  else
    hasUses!.loop op ctx (numResults - 1)

theorem hasUses!.loop_eq_hasUses_loop {op : OperationPtr} (ctx : IRContext) (index : Nat)
    (opIn: op.InBounds ctx)
    (hresult : index < op.getNumResults ctx := by grind) :
    hasUses!.loop op ctx index = hasUses.loop op ctx index opIn hresult := by
  induction index
  · grind [hasUses!.loop, hasUses.loop]
  · simp only [hasUses!.loop, hasUses.loop]
    grind

@[grind _=_]
theorem hasUses!_eq_hasUses {op : OperationPtr} (hin : op.InBounds ctx) :
    op.hasUses! ctx = op.hasUses ctx hin := by
  grind [hasUses!.loop_eq_hasUses_loop, hasUses!, hasUses]

theorem hasUses!.loop_eq_true_iff {op : OperationPtr} {ctx} {index : Nat} :
    hasUses!.loop op ctx index = true ↔
    ∃ index' ≤ index, (ValuePtr.opResult (op.getResult index')).hasUses! ctx := by
  induction index <;> grind [hasUses!.loop, ValuePtr.hasUses!]

theorem hasUses!_eq_true_iff_hasUses!_getResult {op : OperationPtr} :
    op.hasUses! ctx = true ↔
    ∃ index < op.getNumResults! ctx, (ValuePtr.opResult (op.getResult index)).hasUses! ctx := by
  grind [hasUses!, hasUses!.loop_eq_true_iff]

theorem hasUses!_eq_false_iff_hasUses!_getResult_eq_false {op : OperationPtr} :
    op.hasUses! ctx = false ↔
    ∀ index < op.getNumResults! ctx, (ValuePtr.opResult (op.getResult index)).hasUses! ctx = false := by
  grind [hasUses!_eq_true_iff_hasUses!_getResult]

theorem hasUses!_eq_false_iff_hasUses!_opResult_eq_false {op : OperationPtr}
    (inBounds : op.InBounds ctx) :
    (op.hasUses! ctx = false ↔
    ∀ (opResult : OpResultPtr), opResult.InBounds ctx → opResult.op = op → (opResult : ValuePtr).hasUses! ctx = false) := by
  simp [hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
  grind [OpResultPtr.inBounds_def, getResult, cases OpResultPtr]

end OperationPtr

def IRContext.empty : IRContext := {
    nextID := 0,
    operations := Std.HashMap.emptyWithCapacity,
    blocks := Std.HashMap.emptyWithCapacity,
    regions := Std.HashMap.emptyWithCapacity,
  }

/--
  Run a function on all operations in the context.
  In particular, the function provides a proof that the operation pointer is in bounds.
-/
def IRContext.forOpsDepM (ctx : IRContext) {m : Type w → Type w'} [Monad m]
    (p : ∀ (op : OperationPtr), op.InBounds ctx → m PUnit) : m PUnit :=
  ctx.operations.forKeysDepM (fun opPtr h => p opPtr (by grind [OperationPtr.InBounds]))

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
  attribute [local grind] IRContext.empty
  attribute [local grind] OpOperandPtr.setNextUse OpOperandPtr.setBack OpOperandPtr.setOwner OpOperandPtr.setValue OpOperandPtr.set
  attribute [local grind] OpOperandPtrPtr.set OpOperandPtrPtr.get!
  attribute [local grind] ValuePtr.getFirstUse! ValuePtr.getFirstUse ValuePtr.setFirstUse ValuePtr.setType ValuePtr.getType ValuePtr.getType!
  attribute [local grind] OpResultPtr.get! OpResultPtr.setFirstUse OpResultPtr.set OpResultPtr.setType
  attribute [local grind] BlockArgumentPtr.get! BlockArgumentPtr.setFirstUse BlockArgumentPtr.set BlockArgumentPtr.setType BlockArgumentPtr.setLoc
  attribute [local grind] OperationPtr.setOperands OperationPtr.setBlockOperands OperationPtr.setResults OperationPtr.pushResult OperationPtr.setRegions OperationPtr.setProperties OperationPtr.pushOperand OperationPtr.pushBlockOperand OperationPtr.allocEmpty OperationPtr.dealloc OperationPtr.setNextOp OperationPtr.setPrevOp OperationPtr.setParent OperationPtr.getNumResults! OperationPtr.getNumOperands! OperationPtr.getNumRegions! OperationPtr.getRegion! OperationPtr.getNumSuccessors! OperationPtr.getProperties! OperationPtr.set
  attribute [local grind] Operation.empty
  attribute [local grind] BlockPtr.get! BlockPtr.setParent BlockPtr.setFirstUse BlockPtr.setFirstOp BlockPtr.setLastOp BlockPtr.setNextBlock BlockPtr.setPrevBlock BlockPtr.allocEmpty Block.empty BlockPtr.getNumArguments! BlockPtr.set BlockPtr.setArguments BlockPtr.pushArgument
  attribute [local grind =] Option.maybe_def
  attribute [local grind] OpOperandPtr.get! BlockOperandPtr.get! OpResultPtr.get! BlockArgumentPtr.get! OperationPtr.get!
  attribute [local grind] BlockOperandPtr.setBack BlockOperandPtr.setNextUse BlockOperandPtr.setOwner BlockOperandPtr.setValue BlockOperandPtr.set
  attribute [local grind] BlockOperandPtrPtr.get!
  attribute [local grind] RegionPtr.get! RegionPtr.setParent RegionPtr.setFirstBlock RegionPtr.setLastBlock RegionPtr.set RegionPtr.allocEmpty
)
