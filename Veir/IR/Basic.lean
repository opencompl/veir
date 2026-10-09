module

public import Veir.Prelude
public import Veir.IR.OpCode
public import Veir.ForLean
public import Veir.IR.Simp

open Std (HashMap)

public section

namespace Veir

structure OperationPtr where
  id : Nat
deriving Inhabited, Repr, DecidableEq

instance : Hashable OperationPtr where
  hash opPtr := hash opPtr.id

structure BlockPtr where
  id : Nat
deriving Inhabited, Repr, DecidableEq

instance : Hashable BlockPtr where
  hash blockPtr := hash blockPtr.id

structure RegionPtr where
  id : Nat
deriving Inhabited, Repr, DecidableEq

instance : Hashable RegionPtr where
  hash regionPtr := hash regionPtr.id

abbrev Location := Unit

/--
A pointer to an operation result.
-/
structure OpResultPtr where
  op : OperationPtr
  index : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/--
A pointer to an operation operand.
-/
structure OpOperandPtr where
  op : OperationPtr
  index : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/--
A pointer to an operation block operand.
-/
structure BlockOperandPtr where
  op : OperationPtr
  index : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/--
A pointer to a block argument.
-/
structure BlockArgumentPtr where
  block : BlockPtr
  index : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/--
The base class for operation results and block arguments.
-/
structure ValueImpl where
  /-- `type` is used to distinguish between OpResult and BlockArgument -/
  type : TypeAttr
  firstUse : Option OpOperandPtr
deriving Inhabited, Repr, Hashable

/--
The definition of an operation result.
-/
structure OpResult extends ValueImpl where
  index : Nat
  /-- `owner` should be computed from index and the layout -/
  owner : OperationPtr
deriving Inhabited, Repr, Hashable

/--
The definition of a block argument.
-/
structure BlockArgument extends ValueImpl where
  index : Nat
  loc : Location
  owner : BlockPtr
deriving Inhabited, Repr, Hashable

/--
An MLIR SSA value.
A value is either an operation result, or a block argument.
-/
inductive ValuePtr where
  | opResult (ptr : OpResultPtr)
  | blockArgument (ptr : BlockArgumentPtr)
deriving Inhabited, Repr, DecidableEq, Hashable

-- As in MLIR, an OpResultPtr can be coerced to a ValuePtr
instance : Coe OpResultPtr ValuePtr where
  coe ptr := ValuePtr.opResult ptr

-- As in MLIR, a BlockArgumentPtr can be coerced to a ValuePtr
instance : Coe BlockArgumentPtr ValuePtr where
  coe ptr := ValuePtr.blockArgument ptr

/--
A pointer to an operation operand pointer.
This is used for the encoding of the use-def chain.
It is either pointing to the next use field of the previous operand,
or to the first use field of a value definition.
-/
inductive OpOperandPtrPtr where
  | operandNextUse (ptr : OpOperandPtr)
  | valueFirstUse (ptr : ValuePtr)
deriving Inhabited, Repr, DecidableEq, Hashable

/--
An operand definition.
It contains a pointer to the SSA value it uses, and links to the previous
and next use of that value.
-/
structure OpOperand where
  nextUse : Option OpOperandPtr
  -- I am not sure why, but some parts of MLIR consider this to be an optional.
  -- For example, the `IROperandBase ::removeFromCurrent` method checks for null.
  back : OpOperandPtrPtr
  owner : OperationPtr
  value : ValuePtr
deriving Inhabited, Repr, Hashable

/--
A pointer to an operation block operand pointer.
This is used for the encoding of the use-def chain for block operands.
It is either pointing to the next use field of the previous block operand,
or to the first use field of a block.
-/
inductive BlockOperandPtrPtr where
  | blockOperandNextUse (ptr : BlockOperandPtr)
  | blockFirstUse (ptr : BlockPtr)
deriving Inhabited, Repr, Hashable, DecidableEq

/--
A block operand definition.
It contains a pointer to the block it uses, and links to the previous
and next use of that block.
-/
structure BlockOperand where
  nextUse : Option BlockOperandPtr
  back : BlockOperandPtrPtr
  owner : OperationPtr
  value : BlockPtr
deriving Inhabited, Repr, Hashable

/--
An MLIR operation.
-/
structure Operation (OpInfo : Type) [IsOpCode OpInfo] where
  results : Array OpResult
  -- This is the operation pointer start
  prev : Option OperationPtr
  next : Option OperationPtr
  parent : Option BlockPtr
  -- We do not support those features yet :
  -- location : Location
  -- orderIndex : Nat
  opType : OpInfo
  attrs : DictionaryAttr
  -- This should be replaced with an arbitrary user object
  properties : propertiesOf opType
  blockOperands : Array BlockOperand
  regions : Array RegionPtr
  operands : Array OpOperand
deriving Inhabited, Repr, Hashable

variable {OpInfo : Type} [IsOpCode OpInfo]
variable {Dialect : Type} [IsOpCode Dialect] [HasDialect OpInfo Dialect]

namespace Operation

theorem default_operands_eq :
    (default : Operation OpInfo).operands = #[] := by
  rfl

theorem default_regions_eq :
    (default : Operation OpInfo).regions = #[] := by
  rfl

theorem default_blockOperands_eq :
    (default : Operation OpInfo).blockOperands = #[] := by
  rfl

theorem default_results_eq :
    (default : Operation OpInfo).results = #[] := by
  rfl

theorem default_parent_eq :
    (default : Operation OpInfo).parent = none := by
  rfl

end Operation

namespace OpOperand

theorem default_value_eq :
    (default : OpOperand).value = default := by
  rfl

theorem default_nextUse_eq :
    (default : OpOperand).nextUse = none := by
  rfl

theorem default_back_eq :
    (default : OpOperand).back = default := by
  rfl

theorem default_owner_eq :
    (default : OpOperand).owner = default := by
  rfl

@[ext]
theorem ext {op1 op2 : OpOperand}
    (h_nextUse : op1.nextUse = op2.nextUse)
    (h_back : op1.back = op2.back)
    (h_owner : op1.owner = op2.owner)
    (h_value : op1.value = op2.value) :
    op1 = op2 := by
  grind [cases OpOperand]

end OpOperand

namespace BlockOperand

@[ext]
theorem ext {op1 op2 : BlockOperand}
    (h_nextUse : op1.nextUse = op2.nextUse)
    (h_back : op1.back = op2.back)
    (h_owner : op1.owner = op2.owner)
    (h_value : op1.value = op2.value) :
    op1 = op2 := by
  grind [cases BlockOperand]

theorem default_nextUse_eq : (default : BlockOperand).nextUse = none := by rfl
theorem default_back_eq : (default : BlockOperand).back = default := by rfl
theorem default_owner_eq : (default : BlockOperand).owner = default := by rfl

theorem default_value_eq :
    (default : BlockOperand).value = default := by
  rfl

end BlockOperand

namespace OpResult

theorem default_index_eq : (default : OpResult).index = default := by rfl
theorem default_owner_eq : (default : OpResult).owner = default := by rfl
theorem default_type_eq : (default : OpResult).type = default := by rfl
theorem default_firstUse_eq : (default : OpResult).firstUse = none := by rfl

end OpResult

namespace BlockArgument

theorem default_index_eq : (default : BlockArgument).index = default := by rfl
theorem default_owner_eq : (default : BlockArgument).owner = default := by rfl
theorem default_type_eq : (default : BlockArgument).type = default := by rfl
theorem default_firstUse_eq : (default : BlockArgument).firstUse = none := by rfl

end BlockArgument

/--
An MLIR block.
-/
structure Block where
  firstUse : Option BlockOperandPtr
  prev : Option BlockPtr
  next : Option BlockPtr
  parent : Option RegionPtr
  -- validOpOrder : Bool      -- Unsupported yet
  firstOp : Option OperationPtr
  lastOp : Option OperationPtr
  arguments : Array BlockArgument
deriving Inhabited, Repr, Hashable

namespace Block

theorem default_firstUse_eq : (default : Block).firstUse = none := by rfl
theorem default_prev_eq : (default : Block).prev = none := by rfl
theorem default_next_eq : (default : Block).next = none := by rfl
theorem default_parent_eq : (default : Block).parent = none := by rfl
theorem default_firstOp_eq : (default : Block).firstOp = none := by rfl
theorem default_lastOp_eq : (default : Block).lastOp = none := by rfl
theorem default_arguments_eq : (default : Block).arguments = #[] := by rfl

end Block

/--
An MLIR region.
-/
structure Region where
  firstBlock : Option BlockPtr
  lastBlock : Option BlockPtr
  parent : Option OperationPtr
deriving Inhabited, Repr, Hashable

/--
The owning context of an MLIR module.
It contains a top-level Module operation, and a maps from pointers to
operations, blocks, and regions.
-/
structure IRContext (OpInfo : Type) [IsOpCode OpInfo] where
  operations : HashMap OperationPtr (Operation OpInfo)
  blocks : HashMap BlockPtr Block
  regions : HashMap RegionPtr Region
  nextID : Nat
deriving Inhabited, Repr

theorem IRContext.default_def : (default : IRContext OpInfo) = IRContext.mk ∅ ∅ ∅ 0 := by rfl

variable {ctx ctx' : IRContext OpInfo}

/-! Empty objects. -/

@[expose]
def Operation.empty (opType : OpInfo) (prop : propertiesOf opType) : Operation OpInfo :=
  { results := #[]
    prev := none
    next := none
    parent := none
    opType := opType
    attrs := DictionaryAttr.empty
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

/-!
OperationPtr accessors
-/

namespace OperationPtr

@[local grind]
def InBounds (op : OperationPtr) (ctx : IRContext OpInfo) : Prop :=
  op ∈ ctx.operations

theorem inBounds_def : InBounds op ctx ↔ op ∈ ctx.operations := by rfl

@[no_expose]
instance : Decidable (InBounds op ctx) := by
  unfold InBounds; infer_instance

def get (ptr : OperationPtr) (ctx : IRContext OpInfo) (inBounds : ptr.InBounds ctx := by grind) : Operation OpInfo :=
  ctx.operations[ptr]'(by unfold InBounds at inBounds; grind)

def get! (ptr : OperationPtr) (ctx : IRContext OpInfo) : Operation OpInfo :=
  ctx.operations[ptr]!

@[grind =_, eq_bang ←]
theorem get!_eq_get {ptr : OperationPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = (ptr.get ctx hin) := by
  grind [get, get!, InBounds]

theorem get!_of_not_inBounds {op : OperationPtr} (notInBounds : ¬ op.InBounds ctx) :
    op.get! ctx = default := by
  grind [get!, InBounds]

def getOpType (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx) : OpInfo :=
  (op.get ctx (by grind)).opType

def getOpType! (op : OperationPtr) (ctx : IRContext OpInfo) : OpInfo :=
  (op.get! ctx).opType

@[grind =_, eq_bang ←]
theorem getOpType!_eq_getOpType {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getOpType! ctx = op.getOpType ctx hin := by
  grind [getOpType, getOpType!]

def getNumOperands (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).operands.size

def getNumOperands! (op : OperationPtr) (ctx : IRContext OpInfo) : Nat :=
  (op.get! ctx).operands.size

@[grind =_, eq_bang ←]
theorem getNumOperands!_eq_getNumOperands {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumOperands! ctx = op.getNumOperands ctx (by grind) := by
  grind [getNumOperands, getNumOperands!]

theorem getNumOperands!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumOperands! ctx = op.getNumOperands! ctx' := by
  grind [getNumOperands!]

def getOpOperand (op : OperationPtr) (index : Nat) : OpOperandPtr :=
  { op := op, index := index }

theorem getOpOperand_def {op : OperationPtr} {index : Nat} :
    getOpOperand op index = { op := op, index := index } := by rfl

@[simp, grind =]
theorem getOpOperand_index {op : OperationPtr} {index : Nat} :
    (getOpOperand op index).index = index := by
  grind [getOpOperand]

@[simp, grind =]
theorem getOpOperand_op {op : OperationPtr} {index : Nat} :
    (getOpOperand op index).op = op := by
  grind [getOpOperand]

def getOperand (op : OperationPtr) (ctx : IRContext OpInfo) (index : Nat)
    (inBounds : op.InBounds ctx := by grind) (h : index < getNumOperands! op ctx := by grind) : ValuePtr :=
  ((op.get ctx (by grind)).operands[index]'(by grind [getNumOperands!])).value

def getOperand! (op : OperationPtr) (ctx : IRContext OpInfo) (index : Nat) : ValuePtr :=
  ((op.get! ctx).operands[index]!).value

@[grind =_, eq_bang ←]
theorem getOperand!_eq_getOperand {op : OperationPtr} {index : Nat}
    (opInBounds : op.InBounds ctx) (h : index < op.getNumOperands! ctx) :
    op.getOperand! ctx index = op.getOperand ctx index opInBounds h := by
  grind [getOperand, getOperand!]

def getOperands (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx := by grind) : Array ValuePtr :=
  (op.get ctx (by grind)).operands.map (·.value)

def getOperands! (op : OperationPtr) (ctx : IRContext OpInfo) : Array ValuePtr :=
  (op.get! ctx).operands.map (·.value)

@[grind =_, eq_bang ←]
theorem getOperands!_eq_getOperands {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getOperands! ctx = op.getOperands ctx (by grind) := by
  grind [getOperands, getOperands!]

theorem getOperands!.mem_iff_exists_index {op : OperationPtr} :
    value ∈ op.getOperands! ctx ↔
    ∃ index, index < op.getNumOperands! ctx ∧ op.getOperand! ctx index = value := by
  simp only [getOperands!, Array.mem_map, getOperand!, getNumOperands!]
  constructor
  · rintro ⟨operand, ⟨hoperand, operandValue⟩⟩
    have ⟨i, hi, hoperand⟩ := Array.getElem_of_mem hoperand
    exists i
    grind
  · grind

theorem getOperands!.mem_getOperand {op : OperationPtr} :
    index < op.getNumOperands! ctx →
    (op.getOperand! ctx index) ∈ op.getOperands! ctx := by
  grind [getOperands!, getOperand!, getNumOperands!]

@[simp, grind =]
theorem getOperands!.size_eq_getNumOperands! {op : OperationPtr} :
    (op.getOperands! ctx).size = op.getNumOperands! ctx := by
  grind [getOperands!, getNumOperands!]

@[simp, grind =]
theorem getOperands!.getElem!_eq_getOperand! {op : OperationPtr} :
    (op.getOperands! ctx)[index]! = op.getOperand! ctx index := by
  simp only [getOperands!, getOperand!]
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  grind [OpOperand.default_value_eq]

@[simp, grind =]
theorem getOperands!.getElem_eq_getOperand! {op : OperationPtr} {h} :
    (op.getOperands! ctx)[index]'h = op.getOperand! ctx index := by
  grind [getOperands!, getOperand!]

def getOpOperands (op : OperationPtr) (ctx : IRContext OpInfo)
    (inBounds : op.InBounds ctx := by grind) : Array OpOperandPtr :=
  Array.map op.getOpOperand (Array.range (op.getNumOperands ctx inBounds))

def getOpOperands! (op : OperationPtr) (ctx : IRContext OpInfo) : Array OpOperandPtr :=
  Array.map op.getOpOperand (Array.range (op.getNumOperands! ctx))

@[grind =_, eq_bang ←]
theorem getOpOperands!_eq_getOpOperands {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getOpOperands! ctx = op.getOpOperands ctx (by grind) := by
  grind [getOpOperands, getOpOperands!]

theorem getOpOperands!.mem_iff_exists_index {op : OperationPtr} :
    operand ∈ op.getOpOperands! ctx ↔
    ∃ index, index < op.getNumOperands! ctx ∧ op.getOpOperand index = operand := by
  simp only [getOpOperands!, Array.mem_map, getOpOperand, getNumOperands!]
  constructor
  · rintro ⟨opr, ⟨hopr, oprValue⟩⟩
    have ⟨i, hi, hopr⟩ := Array.getElem_of_mem hopr
    exists i
    grind
  · grind

theorem getOpOperands!.mem_getOpOperand {op : OperationPtr} :
    index < op.getNumOperands! ctx →
    op.getOpOperand index ∈ op.getOpOperands! ctx := by
  grind [getOpOperands!, getOpOperand, getNumOperands!]

@[simp, grind =]
theorem getOpOperands!.size_eq_getNumOperands! {op : OperationPtr} :
    (op.getOpOperands! ctx).size = op.getNumOperands! ctx := by
  grind [getOpOperands!, getNumOperands!]

@[simp, grind =]
theorem getOpOperands!.getElem!_eq_getOpOperand {op : OperationPtr} :
    index < op.getNumOperands! ctx →
    (op.getOpOperands! ctx)[index]! = op.getOpOperand index := by
  simp only [getOpOperands!]
  grind [getOpOperand]

@[simp, grind =]
theorem getOpOperands!.getElem_eq_getOpOperand
    {op : OperationPtr} {h : index < (op.getOpOperands! ctx).size} :
    index < op.getNumOperands! ctx →
    (op.getOpOperands! ctx)[index]'h = op.getOpOperand index := by
  simp only [getOpOperands!]
  grind [getOpOperand]

def getOperandTypes (op : OperationPtr) (ctx : IRContext OpInfo)
    (inBounds : op.InBounds ctx := by grind) : Array TypeAttr :=
  (op.get ctx).operands.map fun opr =>
    match opr.value with
    | .opResult ptr => (ptr.op.get! ctx).results[ptr.index]!|>.type
    | .blockArgument ptr => (ctx.blocks[ptr.block]!).arguments[ptr.index]!|>.type

def getOperandTypes! (op : OperationPtr) (ctx : IRContext OpInfo) : Array TypeAttr :=
  (op.get! ctx).operands.map fun opr =>
    match opr.value with
    | .opResult ptr => (ptr.op.get! ctx).results[ptr.index]!|>.type
    | .blockArgument ptr => (ctx.blocks[ptr.block]!).arguments[ptr.index]!|>.type

@[grind =_, eq_bang ←]
theorem getOperandTypes!_eq_getOperandTypes {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getOperandTypes! ctx = op.getOperandTypes ctx (by grind) := by
  grind [getOperandTypes, getOperandTypes!, get!_eq_get]

@[grind =]
theorem getOperandTypes!.size_eq_getNumOperands! {op : OperationPtr} :
    (op.getOperandTypes! ctx).size = op.getNumOperands! ctx := by
  grind [getOperandTypes!, getNumOperands!]

def getNumSuccessors (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).blockOperands.size

def getNumSuccessors! (op : OperationPtr) (ctx : IRContext OpInfo) : Nat :=
  (op.get! ctx).blockOperands.size

@[grind =_, eq_bang ←]
theorem getNumSuccessors!_eq_getNumSuccessors {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumSuccessors! ctx = op.getNumSuccessors ctx (by grind) := by
  grind [getNumSuccessors, getNumSuccessors!]

theorem getNumSuccessors!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumSuccessors! ctx = op.getNumSuccessors! ctx' := by
  grind [getNumSuccessors!]

def getBlockOperand (op : OperationPtr) (index : Nat) : BlockOperandPtr :=
  { op := op, index := index }

theorem getBlockOperand_def {op : OperationPtr} {index : Nat} :
    getBlockOperand op index = { op := op, index := index } := by rfl

@[simp, grind =]
theorem getBlockOperand_index {op : OperationPtr} {index : Nat} :
    (getBlockOperand op index).index = index := by
  grind [getBlockOperand]

@[simp, grind =]
theorem getBlockOperand_op {op : OperationPtr} {index : Nat} :
    (getBlockOperand op index).op = op := by
  grind [getBlockOperand]

def getSuccessor (op : OperationPtr) (ctx : IRContext OpInfo) (index : Nat)
    (inBounds : op.InBounds ctx := by grind) (h : index < getNumSuccessors op ctx inBounds := by grind) : BlockPtr :=
  ((op.get ctx (by grind)).blockOperands[index]'(by grind [getNumSuccessors])).value

def getSuccessor! (op : OperationPtr) (ctx : IRContext OpInfo) (index : Nat) : BlockPtr :=
  ((op.get! ctx).blockOperands[index]!).value

@[grind =_, eq_bang ←]
theorem getSuccessor!_eq_getSuccessor {op : OperationPtr} {index : Nat}
    {hin} (h : index < op.getNumSuccessors ctx hin) {hin'} :
    op.getSuccessor! ctx index = op.getSuccessor ctx index hin' h := by
  grind [getSuccessor, getSuccessor!]

def getSuccessors (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx := by grind) : Array BlockPtr :=
  (op.get ctx (by grind)).blockOperands.map (·.value)

def getSuccessors! (op : OperationPtr) (ctx : IRContext OpInfo) : Array BlockPtr :=
  (op.get! ctx).blockOperands.map (·.value)

@[grind =_, eq_bang ←]
theorem getSuccessors!_eq_getSuccessors {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getSuccessors! ctx = op.getSuccessors ctx (by grind) := by
  grind [getSuccessors, getSuccessors!]

theorem getSuccessors!.mem_iff_exists_index {op : OperationPtr} :
    value ∈ op.getSuccessors! ctx ↔
    ∃ index, index < op.getNumSuccessors! ctx ∧ op.getSuccessor! ctx index = value := by
  simp only [getSuccessors!, Array.mem_map, getSuccessor!, getNumSuccessors!]
  constructor
  · rintro ⟨operand, ⟨hoperand, operandValue⟩⟩
    have ⟨i, hi, hoperand⟩ := Array.getElem_of_mem hoperand
    exists i
    grind
  · grind

theorem getSuccessors!.mem_getSuccessor {op : OperationPtr} :
    index < op.getNumSuccessors! ctx →
    (op.getSuccessor! ctx index) ∈ op.getSuccessors! ctx := by
  grind [getSuccessors!, getSuccessor!, getNumSuccessors!]

@[simp, grind =]
theorem getSuccessors!.size_eq_getNumSuccessors! {op : OperationPtr} :
    (op.getSuccessors! ctx).size = op.getNumSuccessors! ctx := by
  grind [getSuccessors!, getNumSuccessors!]

@[simp, grind =]
theorem getSuccessors!.getElem!_eq_getSuccessor! {op : OperationPtr} :
    (op.getSuccessors! ctx)[index]! = op.getSuccessor! ctx index := by
  simp only [getSuccessors!, getSuccessor!]
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  grind [BlockOperand.default_value_eq]

@[simp, grind =]
theorem getSuccessors!.getElem_eq_getSuccessor! {op : OperationPtr} {h} :
    (op.getSuccessors! ctx)[index]'h = op.getSuccessor! ctx index := by
  grind [getSuccessors!, getSuccessor!]

theorem getSuccessors!_def {op : OperationPtr} :
    op.getSuccessors! ctx =
    Array.map (fun i => op.getSuccessor! ctx i) (Array.range (op.getNumSuccessors! ctx)) := by
  grind

def getNumResults (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).results.size

def getNumResults! (op : OperationPtr) (ctx : IRContext OpInfo) : Nat :=
  (op.get! ctx).results.size

@[grind =_, eq_bang ←]
theorem getNumResults!_eq_getNumResults {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumResults! ctx = op.getNumResults ctx (by grind) := by
  grind [getNumResults, getNumResults!]

theorem getNumResults!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumResults! ctx = op.getNumResults! ctx' := by
  grind [getNumResults!]

def getResult (op : OperationPtr) (index : Nat) : OpResultPtr :=
  { op := op, index := index }

theorem getResult_def {op : OperationPtr} {index : Nat} :
    getResult op index = { op := op, index := index } := by rfl

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

def getOpResults (op : OperationPtr) (ctx : IRContext OpInfo)
  (inBounds : op.InBounds ctx := by grind) : Array OpResultPtr :=
  Array.map (fun i => op.getResult i) (Array.range (op.getNumResults ctx inBounds))

def getOpResults! (op : OperationPtr) (ctx : IRContext OpInfo) : Array OpResultPtr :=
  Array.map (fun i => op.getResult i) (Array.range (op.getNumResults! ctx))

@[grind =_, eq_bang ←]
theorem getOpResults!_eq_getOpResults {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getOpResults! ctx = op.getOpResults ctx (by grind) := by
  grind [getOpResults, getOpResults!]

theorem getOpResults!.mem_iff_exists_index {op : OperationPtr} :
    value ∈ op.getOpResults! ctx ↔
    ∃ index, index < op.getNumResults! ctx ∧ op.getResult index = value := by
  simp only [getOpResults!, Array.mem_map, getResult, getNumResults!]
  constructor
  · rintro ⟨result, ⟨hresult, resultValue⟩⟩
    have ⟨i, hi, hresult⟩ := Array.getElem_of_mem hresult
    exists i
    grind
  · grind

theorem getOpResults!.mem_getResult {op : OperationPtr} :
    index < op.getNumResults! ctx →
    op.getResult index ∈ op.getOpResults! ctx := by
  grind [getOpResults!, getResult, getNumResults!]

@[simp, grind =]
theorem getOpResults!.size_eq_getNumResults! {op : OperationPtr} :
    (op.getOpResults! ctx).size = op.getNumResults! ctx := by
  grind [getOpResults!, getNumResults!]

@[simp, grind =]
theorem getOpResults!.getElem!_eq_getResult {op : OperationPtr} :
    index < op.getNumResults! ctx →
    (op.getOpResults! ctx)[index]! = op.getResult index := by
  simp only [getOpResults!, getResult]
  grind

@[simp, grind =]
theorem getOpResults!.getElem_eq_getResult
    {op : OperationPtr} {h : index < (op.getOpResults! ctx).size} :
    index < op.getNumResults! ctx →
    (op.getOpResults! ctx)[index]'h = op.getResult index := by
  simp only [getOpResults!, getResult]
  grind

def getResults (op : OperationPtr) (ctx : IRContext OpInfo)
  (inBounds : op.InBounds ctx := by grind) : Array ValuePtr :=
  Array.map (fun i => op.getResult i) (Array.range (op.getNumResults ctx inBounds))

def getResults! (op : OperationPtr) (ctx : IRContext OpInfo) : Array ValuePtr :=
  Array.map (fun i => op.getResult i) (Array.range (op.getNumResults! ctx))

@[grind =_, eq_bang ←]
theorem getResults!_eq_getResults {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getResults! ctx = op.getResults ctx (by grind) := by
  grind [getResults, getResults!]

theorem getResults!.mem_iff_exists_index {op : OperationPtr} :
    value ∈ op.getResults! ctx ↔
    ∃ index, index < op.getNumResults! ctx ∧ op.getResult index = value := by
  simp only [getResults!, Array.mem_map, getResult, getNumResults!]
  constructor
  · rintro ⟨result, ⟨hresult, resultValue⟩⟩
    have ⟨i, hi, hresult⟩ := Array.getElem_of_mem hresult
    exists i
    grind
  · grind

theorem getResults!.mem_getResult {op : OperationPtr} :
    index < op.getNumResults! ctx →
    (op.getResult index : ValuePtr) ∈ op.getResults! ctx := by
  grind [getResults!, getResult, getNumResults!]

@[simp, grind =]
theorem getResults!.size_eq_getNumResults! {op : OperationPtr} :
    (op.getResults! ctx).size = op.getNumResults! ctx := by
  grind [getResults!, getNumResults!]

@[simp, grind =]
theorem getResults!.getElem!_eq_getResult {op : OperationPtr} :
    index < op.getNumResults! ctx →
    (op.getResults! ctx)[index]! = op.getResult index := by
  simp only [getResults!, getResult]
  grind

@[simp, grind =]
theorem getResults!.getElem_eq_getResult
    {op : OperationPtr} {h : index < (op.getResults! ctx).size} :
    index < op.getNumResults! ctx →
    (op.getResults! ctx)[index]'h = op.getResult index := by
  simp only [getResults!, getResult]
  grind

theorem getResult_eq_of_idxOf_getResults! {op : OperationPtr} :
    value ∈ op.getResults! ctx →
    (op.getResults! ctx).idxOf value = index →
    op.getResult index = value := by
  grind [Array.getElem?_idxOf]

grind_pattern getResult_eq_of_idxOf_getResults! =>
  value ∈ op.getResults! ctx, (op.getResults! ctx).idxOf value, op.getResult index

def getResultTypes (op : OperationPtr) (ctx : IRContext OpInfo)
    (inBounds : op.InBounds ctx := by grind) : Array TypeAttr :=
  (op.get ctx).results.map (·.type)

def getResultTypes! (op : OperationPtr) (ctx : IRContext OpInfo) : Array TypeAttr :=
  (op.get! ctx).results.map (·.type)

@[grind =_, eq_bang ←]
theorem getResultTypes!_eq_getResultTypes {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getResultTypes! ctx = op.getResultTypes ctx (by grind) := by
  grind [getResultTypes, getResultTypes!, get!_eq_get, getNumResults!_eq_getNumResults]

@[grind =]
theorem getResultTypes!.size_eq_getNumResults! {op : OperationPtr} :
    (op.getResultTypes! ctx).size = op.getNumResults! ctx := by
  grind [getResultTypes!, getNumResults!]

def getNumRegions (op : OperationPtr) (ctx : IRContext OpInfo)
    (inBounds : op.InBounds ctx := by grind) : Nat :=
  (op.get ctx (by grind)).regions.size

def getNumRegions! (op : OperationPtr) (ctx : IRContext OpInfo) : Nat :=
  (op.get! ctx).regions.size

@[grind =_, eq_bang ←]
theorem getNumRegions!_eq_getNumRegions {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNumRegions! ctx = op.getNumRegions ctx (by grind) := by
  grind [getNumRegions, getNumRegions!]

theorem getNumRegions!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getNumRegions! ctx = op.getNumRegions! ctx' := by
  grind [getNumRegions!]

def getRegion (op : OperationPtr) (ctx : IRContext OpInfo) (index : Nat)
  (inBounds : op.InBounds ctx := by grind) (iInBounds : index < op.getNumRegions ctx inBounds := by grind) : RegionPtr :=
  (op.get ctx (by grind)).regions[index]'(by grind [getNumRegions])

@[grind funCC]
def getRegion! (op : OperationPtr) (ctx : IRContext OpInfo) (index : Nat) : RegionPtr :=
  (op.get! ctx).regions[index]!

@[grind =_, eq_bang ←]
theorem getRegion!_eq_getRegion {op : OperationPtr} {index : Nat}
    {hin} (iInBounds : index < op.getNumRegions ctx hin) {hin'} :
    op.getRegion! ctx index = op.getRegion ctx index hin' iInBounds := by
  grind [getRegion, getRegion!]

theorem getRegion!_eq_of_OperationPtr_get!_eq {op : OperationPtr} :
    op.get! ctx = op.get! ctx' →
    op.getRegion! ctx = op.getRegion! ctx' := by
  grind [get!, getRegion!]

def getRegions (op : OperationPtr) (ctx : IRContext OpInfo)
    (inBounds : op.InBounds ctx := by grind) : Array RegionPtr :=
  (op.get ctx inBounds).regions

def getRegions! (op : OperationPtr) (ctx : IRContext OpInfo) : Array RegionPtr :=
  (op.get! ctx).regions

@[grind =_, eq_bang ←]
theorem getRegions!_eq_getRegions {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getRegions! ctx = op.getRegions ctx (by grind) := by
  grind [getRegions, getRegions!]

theorem getRegions!.mem_iff_exists_index {op : OperationPtr} :
    region ∈ op.getRegions! ctx ↔
    ∃ index, index < op.getNumRegions! ctx ∧ op.getRegion! ctx index = region := by
  simp only [getRegions!, getRegion!, getNumRegions!]
  constructor
  · rintro hregion
    have ⟨i, hi, hregion⟩ := Array.getElem_of_mem hregion
    exists i
    grind
  · grind

theorem getRegions!.mem_getRegion! {op : OperationPtr} :
    index < op.getNumRegions! ctx →
    op.getRegion! ctx index ∈ op.getRegions! ctx := by
  grind [getRegions!, getRegion!, getNumRegions!]

@[simp, grind =]
theorem getRegions!.size_eq_getNumRegions! {op : OperationPtr} :
    (op.getRegions! ctx).size = op.getNumRegions! ctx := by
  grind [getRegions!, getNumRegions!]

@[simp, grind =]
theorem getRegions!.getElem!_eq_getRegion! {op : OperationPtr} :
    (op.getRegions! ctx)[index]! = op.getRegion! ctx index := by
  simp only [getRegions!, getRegion!]

@[simp, grind =]
theorem getRegions!.getElem_eq_getRegion!
    {op : OperationPtr} {h : index < (op.getRegions! ctx).size} :
    (op.getRegions! ctx)[index]'h = op.getRegion! ctx index := by
  simp only [getRegions!, getRegion!]
  grind

/--
Get the properties of an operation of type `opCode`.
The passed `opCode` can either be of the global `OpInfo` type, or the dialect-specific `Dialect`
type, in order to get the dialect-specific properties which is often easier to use.
-/
@[inline]
def getProperties (op : OperationPtr) (ctx : IRContext OpInfo) (opCode : Dialect)
    (inBounds : op.InBounds ctx := by grind)
    (hprop : op.getOpType! ctx = opCode := by grind) : propertiesOf opCode :=
  have h : (op.get ctx inBounds).opType = opCode := by grind [getOpType!]
  let globalProperties := h ▸ (op.get ctx (by grind)).properties
  HasDialect.toDialectProperties opCode globalProperties

/--
Get the properties of an operation of type `opCode`.
The passed `opCode` can either be of the global `OpInfo` type, or the dialect-specific `Dialect`
type, in order to get the dialect-specific properties which is often easier to use.

This function returns the default properties if the operation is not in bounds, or if the
operation's type does not match the passed `opCode`.
-/
@[inline]
def getProperties! (op : OperationPtr) (ctx : IRContext OpInfo)
    (opCode : Dialect) : propertiesOf opCode :=
  if h : (op.get! ctx).opType = opCode then
    let globalProperties := h ▸ (op.get! ctx).properties
    HasDialect.toDialectProperties opCode globalProperties
  else
    default

@[grind =_, eq_bang ←]
theorem getProperties!_eq_getProperties {op : OperationPtr} (inBounds : op.InBounds ctx)
    {opCode : Dialect} (hprop : op.getOpType! ctx = opCode) :
    op.getProperties! ctx opCode = op.getProperties ctx opCode inBounds (by grind) := by
  grind [getProperties, getProperties!]

theorem getProperties!_eq_of_OperationPtr_get!_eq {op : OperationPtr} {opCode : Dialect} :
    op.get! ctx = op.get! ctx' →
    op.getProperties! ctx opCode = op.getProperties! ctx' opCode := by
  grind [OperationPtr.get!, getProperties!]

def nextOperand (op : OperationPtr) (ctx : IRContext OpInfo)
    (inBounds : op.InBounds ctx := by grind) : OpOperandPtr :=
  .mk op (op.getNumOperands ctx (by grind))

def nextOperand! (op : OperationPtr) (ctx : IRContext OpInfo) : OpOperandPtr :=
  .mk op (op.getNumOperands! ctx)

@[grind =_, eq_bang ←]
theorem nextOperand!_eq_nextOperand {op : OperationPtr} (hin : op.InBounds ctx) :
    op.nextOperand! ctx = op.nextOperand ctx hin := by
  grind [nextOperand, nextOperand!]

@[grind =]
theorem nextOperand!_eq_getOpOperand {op : OperationPtr} :
    op.nextOperand! ctx = op.getOpOperand (op.getNumOperands! ctx) := by
  rfl

def nextBlockOperand (op : OperationPtr) (ctx : IRContext OpInfo)
    (inBounds : op.InBounds ctx := by grind) : BlockOperandPtr :=
  .mk op (op.getNumSuccessors ctx (by grind))

def nextBlockOperand! (op : OperationPtr) (ctx : IRContext OpInfo) : BlockOperandPtr :=
  .mk op (op.getNumSuccessors! ctx)

@[grind =_, eq_bang ←]
theorem nextBlockOperand!_eq_nextBlockOperand {op : OperationPtr} (hin : op.InBounds ctx) :
    op.nextBlockOperand! ctx = op.nextBlockOperand ctx hin := by
  grind [nextBlockOperand, nextBlockOperand!]

@[grind =]
theorem nextBlockOperand!_eq_getBlockOperand {op : OperationPtr} :
    op.nextBlockOperand! ctx = op.getBlockOperand (op.getNumSuccessors! ctx) := by
  rfl

def nextResult (op : OperationPtr) (ctx : IRContext OpInfo)
    (inBounds : op.InBounds ctx := by grind) : OpResultPtr :=
  .mk op (op.getNumResults ctx (by grind))

def nextResult! (op : OperationPtr) (ctx : IRContext OpInfo) : OpResultPtr :=
  .mk op (op.getNumResults! ctx)

@[grind =_, eq_bang ←]
theorem nextResult!_eq_nextResult {op : OperationPtr} (hin : op.InBounds ctx) :
    op.nextResult! ctx = op.nextResult ctx hin := by
  grind [nextResult, nextResult!]

@[grind =]
theorem nextResult!_eq_getResult {op : OperationPtr} :
    op.nextResult! ctx = op.getResult (op.getNumResults! ctx) := by
  rfl

def getNextOp (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx := by grind) : Option OperationPtr :=
  (op.get ctx (by grind)).next

def getNextOp! (op : OperationPtr) (ctx : IRContext OpInfo) : Option OperationPtr :=
  (op.get! ctx).next

@[grind =_, eq_bang ←]
theorem getNextOp!_eq_getNextOp {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getNextOp! ctx = op.getNextOp ctx hin := by
  grind [getNextOp, getNextOp!]

def getPrevOp (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx := by grind) : Option OperationPtr :=
  (op.get ctx (by grind)).prev

def getPrevOp! (op : OperationPtr) (ctx : IRContext OpInfo) : Option OperationPtr :=
  (op.get! ctx).prev

@[grind =_, eq_bang ←]
theorem getPrevOp!_eq_getPrevOp {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getPrevOp! ctx = op.getPrevOp ctx hin := by
  grind [getPrevOp, getPrevOp!]

def getParent (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx := by grind) : Option BlockPtr :=
  (op.get ctx (by grind)).parent

def getParent! (op : OperationPtr) (ctx : IRContext OpInfo) : Option BlockPtr :=
  (op.get! ctx).parent

@[grind =_, eq_bang ←]
theorem getParent!_eq_getParent {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getParent! ctx = op.getParent ctx hin := by
  grind [getParent, getParent!]

def getAttributes (op : OperationPtr) (ctx : IRContext OpInfo) (inBounds : op.InBounds ctx := by grind) : DictionaryAttr :=
  (op.get ctx (by grind)).attrs

def getAttributes! (op : OperationPtr) (ctx : IRContext OpInfo) : DictionaryAttr :=
  (op.get! ctx).attrs

@[grind =_, eq_bang ←]
theorem getAttributes!_eq_getAttributes {op : OperationPtr} (hin : op.InBounds ctx) :
    op.getAttributes! ctx = op.getAttributes ctx hin := by
  grind [getAttributes, getAttributes!]

end OperationPtr

/-!
 OpOperandPtr accessors
-/

namespace OpOperandPtr

@[local grind]
def InBounds (operand : OpOperandPtr) (ctx : IRContext OpInfo) : Prop :=
  ∃ h, operand.index < (operand.op.get ctx h).operands.size

theorem inBounds_def : InBounds opr ctx ↔ ∃ h, opr.index < opr.op.getNumOperands ctx h := by
  rfl

@[no_expose]
instance : Decidable (InBounds operand ctx) := by
  unfold InBounds; infer_instance

@[grind .]
theorem InBounds_iff (operand : OpOperandPtr) (ctx : IRContext OpInfo) :
    operand.op.InBounds ctx →
    operand.index < operand.op.getNumOperands! ctx →
    operand.InBounds ctx :=
  by grind [inBounds_def]

def get (operand : OpOperandPtr) (ctx : IRContext OpInfo) (operandIn : operand.InBounds ctx := by grind) : OpOperand :=
  (operand.op.get ctx (by grind [InBounds])).operands[operand.index]'(by grind [InBounds, OperationPtr.getNumOperands])

def get! (operand : OpOperandPtr) (ctx : IRContext OpInfo) : OpOperand :=
  (operand.op.get! ctx).operands[operand.index]!

@[grind =_, eq_bang ←]
theorem get!_eq_get {ptr : OpOperandPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem get!_of_not_inBounds {operand : OpOperandPtr} (notInBounds : ¬ operand.InBounds ctx) :
    operand.get! ctx = default := by
  cases opInBounds : decide (operand.op.InBounds ctx) <;>
    grind [get!, OperationPtr.get!_of_not_inBounds, Operation.default_operands_eq, InBounds]

theorem get!_eq_of_OperationPtr_get!_eq {opr : OpOperandPtr} :
    opr.op.get! ctx = opr.op.get! ctx' →
    opr.get! ctx = opr.get! ctx' := by
  grind [OperationPtr.get!, get!]

theorem get!_eq_getOperand!_of_fields_eq {opr : OpOperandPtr} :
    opr.index = oprIndex →
    opr.op = oprOp →
    (opr.get! ctx).value = oprOp.getOperand! ctx oprIndex := by
  grind [OperationPtr.getOperand!, get!]

grind_pattern get!_eq_getOperand!_of_fields_eq =>
  opr.index, opr.op, (opr.get! ctx).value, oprOp.getOperand! ctx oprIndex

def getNextUse (operand : OpOperandPtr) (ctx : IRContext OpInfo) (inBounds : operand.InBounds ctx := by grind) : Option OpOperandPtr :=
  (operand.get ctx (by grind)).nextUse

def getNextUse! (operand : OpOperandPtr) (ctx : IRContext OpInfo) : Option OpOperandPtr :=
  (operand.get! ctx).nextUse

@[grind =_, eq_bang ←]
theorem getNextUse!_eq_getNextUse {operand : OpOperandPtr} (hin : operand.InBounds ctx) :
    operand.getNextUse! ctx = operand.getNextUse ctx hin := by
  grind [getNextUse, getNextUse!]

def getBack (operand : OpOperandPtr) (ctx : IRContext OpInfo) (inBounds : operand.InBounds ctx := by grind) : OpOperandPtrPtr :=
  (operand.get ctx (by grind)).back

def getBack! (operand : OpOperandPtr) (ctx : IRContext OpInfo) : OpOperandPtrPtr :=
  (operand.get! ctx).back

@[grind =_, eq_bang ←]
theorem getBack!_eq_getBack {operand : OpOperandPtr} (hin : operand.InBounds ctx) :
    operand.getBack! ctx = operand.getBack ctx hin := by
  grind [getBack, getBack!]

def getOwner (operand : OpOperandPtr) (ctx : IRContext OpInfo) (inBounds : operand.InBounds ctx := by grind) : OperationPtr :=
  (operand.get ctx (by grind)).owner

def getOwner! (operand : OpOperandPtr) (ctx : IRContext OpInfo) : OperationPtr :=
  (operand.get! ctx).owner

@[grind =_, eq_bang ←]
theorem getOwner!_eq_getOwner {operand : OpOperandPtr} (hin : operand.InBounds ctx) :
    operand.getOwner! ctx = operand.getOwner ctx hin := by
  grind [getOwner, getOwner!]

def getValue (operand : OpOperandPtr) (ctx : IRContext OpInfo) (inBounds : operand.InBounds ctx := by grind) : ValuePtr :=
  (operand.get ctx (by grind)).value

def getValue! (operand : OpOperandPtr) (ctx : IRContext OpInfo) : ValuePtr :=
  (operand.get! ctx).value

@[grind =_, eq_bang ←]
theorem getValue!_eq_getValue {operand : OpOperandPtr} (hin : operand.InBounds ctx) :
    operand.getValue! ctx = operand.getValue ctx hin := by
  grind [getValue, getValue!]

end OpOperandPtr

@[grind =]
theorem OperationPtr.getOperand!_eq_OpOperandPtr_get! :
    OperationPtr.getOperand! op ctx index =
    (OpOperandPtr.get! (OperationPtr.getOpOperand op index) ctx).value := by
  grind [OperationPtr.getOperand!, OpOperandPtr.get!]

@[grind =]
theorem OperationPtr.getOperand_eq_OpOperandPtr_get :
    OperationPtr.getOperand op ctx index opInBounds indexInBounds =
    (OpOperandPtr.get (OperationPtr.getOpOperand op index) ctx (by grind [OperationPtr.getOpOperand, OpOperandPtr.InBounds, OperationPtr.getNumOperands])).value := by
  grind [OpOperandPtr.get, OperationPtr.getOperand, OperationPtr.get, OperationPtr.getOpOperand]

/-!
 BlockOperandPtr accessors
-/

namespace BlockOperandPtr

@[local grind]
def InBounds (operand : BlockOperandPtr) (ctx : IRContext OpInfo) : Prop :=
  ∃ h, operand.index < (operand.op.get ctx h).blockOperands.size

theorem inBounds_def :
    InBounds opr ctx ↔ ∃ h, opr.index < opr.op.getNumSuccessors ctx h := by
  rfl

@[no_expose]
instance : Decidable (InBounds operand ctx) := by
  unfold InBounds; infer_instance

@[grind .]
theorem inBounds_of_OperationPtr_inBounds {operand : BlockOperandPtr} {ctx : IRContext OpInfo} :
    operand.op.InBounds ctx →
    operand.index < operand.op.getNumSuccessors! ctx →
    operand.InBounds ctx :=
  by grind [inBounds_def]

def get (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (operandIn : operand.InBounds ctx := by grind) : BlockOperand :=
  (operand.op.get ctx (by grind [InBounds])).blockOperands[operand.index]'(by grind [InBounds])
def get! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperand :=
  operand.op.get! ctx |>.blockOperands[operand.index]!
@[grind =_, eq_bang ←]
theorem get!_eq_get {ptr : BlockOperandPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!, OperationPtr.get!]

theorem get!_of_not_inBounds {operand : BlockOperandPtr} (notInBounds : ¬ operand.InBounds ctx) :
    operand.get! ctx = default := by
  cases opInBounds : decide (operand.op.InBounds ctx)
    <;> grind [get!, OperationPtr.get!_of_not_inBounds, Operation.default_blockOperands_eq, InBounds]

theorem get!_eq_of_OperationPtr_get!_eq {opr : BlockOperandPtr} :
    opr.op.get! ctx = opr.op.get! ctx' →
    opr.get! ctx = opr.get! ctx' := by
  grind [OperationPtr.get!, get!]

def getNextUse (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (inBounds : operand.InBounds ctx := by grind) : Option BlockOperandPtr :=
  (operand.get ctx (by grind)).nextUse

def getNextUse! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) : Option BlockOperandPtr :=
  (operand.get! ctx).nextUse

@[grind =_, eq_bang ←]
theorem getNextUse!_eq_getNextUse {operand : BlockOperandPtr} (hin : operand.InBounds ctx) :
    operand.getNextUse! ctx = operand.getNextUse ctx hin := by
  grind [getNextUse, getNextUse!]

def getBack (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (inBounds : operand.InBounds ctx := by grind) : BlockOperandPtrPtr :=
  (operand.get ctx (by grind)).back

def getBack! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) : BlockOperandPtrPtr :=
  (operand.get! ctx).back

@[grind =_, eq_bang ←]
theorem getBack!_eq_getBack {operand : BlockOperandPtr} (hin : operand.InBounds ctx) :
    operand.getBack! ctx = operand.getBack ctx hin := by
  grind [getBack, getBack!]

def getOwner (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (inBounds : operand.InBounds ctx := by grind) : OperationPtr :=
  (operand.get ctx (by grind)).owner

def getOwner! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) : OperationPtr :=
  (operand.get! ctx).owner

@[grind =_, eq_bang ←]
theorem getOwner!_eq_getOwner {operand : BlockOperandPtr} (hin : operand.InBounds ctx) :
    operand.getOwner! ctx = operand.getOwner ctx hin := by
  grind [getOwner, getOwner!]

def getValue (operand : BlockOperandPtr) (ctx : IRContext OpInfo) (inBounds : operand.InBounds ctx := by grind) : BlockPtr :=
  (operand.get ctx (by grind)).value

def getValue! (operand : BlockOperandPtr) (ctx : IRContext OpInfo) : BlockPtr :=
  (operand.get! ctx).value

@[grind =_, eq_bang ←]
theorem getValue!_eq_getValue {operand : BlockOperandPtr} (hin : operand.InBounds ctx) :
    operand.getValue! ctx = operand.getValue ctx hin := by
  grind [getValue, getValue!]

end BlockOperandPtr

theorem OperationPtr.getSuccessor!_def {op : OperationPtr} {index : Nat} :
    getSuccessor! op ctx index = ((BlockOperandPtr.mk op index).get! ctx).value := by rfl

/-!
 OpResultPtr accessors
-/

namespace OpResultPtr

@[local grind]
def InBounds (result : OpResultPtr) (ctx : IRContext OpInfo) : Prop :=
  ∃ h, result.index < (result.op.get ctx h).results.size

theorem inBounds_def : InBounds res ctx ↔ ∃ h, res.index < res.op.getNumResults ctx h := by
  rfl

@[no_expose]
instance : Decidable (InBounds result ctx) := by
  unfold InBounds; infer_instance

@[grind .]
theorem inBounds_OperationPtr_getNumResults! (result : OpResultPtr) (ctx : IRContext OpInfo) (h : result.InBounds ctx) :
    result.index < result.op.getNumResults! ctx := by
  simp [OperationPtr.getNumResults!, OperationPtr.get!]
  grind [OperationPtr.get]

@[grind .]
theorem inBounds_of {result : OpResultPtr} :
    result.op.InBounds ctx →
    result.index < result.op.getNumResults! ctx →
    result.InBounds ctx :=
  by grind [InBounds, OperationPtr.getNumResults!]

def get (result : OpResultPtr) (ctx : IRContext OpInfo) (resultIn : result.InBounds ctx := by grind) : OpResult :=
  (result.op.get ctx (by grind [InBounds])).results[result.index]'(by grind [InBounds])

def get! (result : OpResultPtr) (ctx : IRContext OpInfo) : OpResult :=
  (result.op.get! ctx).results[result.index]!

@[grind =_, eq_bang ←]
theorem get!_eq_get {ptr : OpResultPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem get!_of_not_inBounds {result : OpResultPtr} (notInBounds : ¬ result.InBounds ctx) :
    result.get! ctx = default := by
  cases opInBounds : decide (result.op.InBounds ctx)
    <;> grind [get!, OperationPtr.get!_of_not_inBounds, Operation.default_results_eq, InBounds]

theorem get!_eq_of_OperationPtr_get!_eq {res : OpResultPtr} :
    res.op.get! ctx = res.op.get! ctx' →
    res.get! ctx = res.get! ctx' := by
  grind [OperationPtr.get!, get!]

def getType (result : OpResultPtr) (ctx : IRContext OpInfo) (inBounds : result.InBounds ctx := by grind) : TypeAttr :=
  (result.get ctx (by grind)).type

def getType! (result : OpResultPtr) (ctx : IRContext OpInfo) : TypeAttr :=
  (result.get! ctx).type

@[grind =_, eq_bang ←]
theorem getType!_eq_getType {result : OpResultPtr} (hin : result.InBounds ctx) :
    result.getType! ctx = result.getType ctx hin := by
  grind [getType, getType!]

def getFirstUse (result : OpResultPtr) (ctx : IRContext OpInfo) (inBounds : result.InBounds ctx := by grind) : Option OpOperandPtr :=
  (result.get ctx (by grind)).firstUse

def getFirstUse! (result : OpResultPtr) (ctx : IRContext OpInfo) : Option OpOperandPtr :=
  (result.get! ctx).firstUse

@[grind =_, eq_bang ←]
theorem getFirstUse!_eq_getFirstUse {result : OpResultPtr} (hin : result.InBounds ctx) :
    result.getFirstUse! ctx = result.getFirstUse ctx hin := by
  grind [getFirstUse, getFirstUse!]

def getOwner (result : OpResultPtr) (ctx : IRContext OpInfo) (inBounds : result.InBounds ctx := by grind) : OperationPtr :=
  (result.get ctx (by grind)).owner

def getOwner! (result : OpResultPtr) (ctx : IRContext OpInfo) : OperationPtr :=
  (result.get! ctx).owner

@[grind =_, eq_bang ←]
theorem getOwner!_eq_getOwner {result : OpResultPtr} (hin : result.InBounds ctx) :
    result.getOwner! ctx = result.getOwner ctx hin := by
  grind [getOwner, getOwner!]

def getIndex (result : OpResultPtr) (ctx : IRContext OpInfo) (inBounds : result.InBounds ctx := by grind) : Nat :=
  (result.get ctx (by grind)).index

def getIndex! (result : OpResultPtr) (ctx : IRContext OpInfo) : Nat :=
  (result.get! ctx).index

@[grind =_, eq_bang ←]
theorem getIndex!_eq_getIndex {result : OpResultPtr} (hin : result.InBounds ctx) :
    result.getIndex! ctx = result.getIndex ctx hin := by
  grind [getIndex, getIndex!]

end OpResultPtr

/-!
 BlockPtr accessors
-/

namespace BlockPtr

def InBounds (block : BlockPtr) (ctx : IRContext OpInfo) : Prop :=
  block ∈ ctx.blocks

theorem inBounds_def : InBounds block ctx ↔ block ∈ ctx.blocks := by rfl

@[no_expose]
instance : Decidable (InBounds block ctx) := by
  unfold InBounds; infer_instance

def get (ptr : BlockPtr) (ctx : IRContext OpInfo) (inBounds : ptr.InBounds ctx := by grind) : Block :=
  ctx.blocks[ptr]'(by unfold InBounds at inBounds; grind)

def get! (ptr : BlockPtr) (ctx : IRContext OpInfo) : Block := ctx.blocks[ptr]!

@[grind =_, eq_bang ←]
theorem get!_eq_get {ptr : BlockPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem get!_of_not_inBounds {ptr : BlockPtr} (notInBounds : ¬ ptr.InBounds ctx) :
    ptr.get! ctx = default := by
  grind [get!, InBounds]

def getNumArguments (block : BlockPtr) (ctx : IRContext OpInfo) (inBounds : block.InBounds ctx := by grind) : Nat :=
  (block.get ctx (by grind)).arguments.size

def getNumArguments! (block : BlockPtr) (ctx : IRContext OpInfo) : Nat :=
  (block.get! ctx).arguments.size

@[grind =_, eq_bang ←]
theorem getNumArguments!_eq_getNumArguments {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getNumArguments! ctx = block.getNumArguments ctx (by grind) := by
  grind [getNumArguments, getNumArguments!]

theorem getNumArguments!_eq_of_BlockPtr_get!_eq {block : BlockPtr} :
    block.get! ctx = block.get! ctx' →
    block.getNumArguments! ctx = block.getNumArguments! ctx' := by
  grind [getNumArguments!]

def getArgument (block : BlockPtr) (index : Nat) : BlockArgumentPtr :=
  { block := block, index := index }

theorem getArgument_def {block : BlockPtr} {index : Nat} :
    getArgument block index = ⟨block, index⟩ := by rfl

@[simp, grind =]
theorem getArgument_index {block : BlockPtr} {index : Nat} :
    (getArgument block index).index = index := by
  grind [getArgument]

@[simp, grind =]
theorem getArgument_block {block : BlockPtr} {index : Nat} :
    (getArgument block index).block = block := by
  grind [getArgument]

@[simp, grind =]
theorem getArgument_block_index {blockArg : BlockArgumentPtr} :
    (blockArg.block.getArgument blockArg.index) = blockArg := by
  cases blockArg; grind [getArgument]

def getArguments (block : BlockPtr) (ctx : IRContext OpInfo)
  (inBounds : block.InBounds ctx := by grind) : Array ValuePtr :=
  Array.map (fun i => block.getArgument i) (Array.range (block.getNumArguments ctx inBounds))

def getArguments! (block : BlockPtr) (ctx : IRContext OpInfo) : Array ValuePtr :=
  Array.map (fun i => block.getArgument i) (Array.range (block.getNumArguments! ctx))

@[grind =_, eq_bang ←]
theorem getArguments!_eq_getArguments {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getArguments! ctx = block.getArguments ctx (by grind) := by
  grind [getArguments, getArguments!]

theorem getArguments!.mem_iff_exists_index {block : BlockPtr} :
    value ∈ block.getArguments! ctx ↔
    ∃ index, index < block.getNumArguments! ctx ∧ block.getArgument index = value := by
  simp only [getArguments!, Array.mem_map, getArgument, getNumArguments!]
  constructor
  · rintro ⟨result, ⟨hresult, resultValue⟩⟩
    have ⟨i, hi, hresult⟩ := Array.getElem_of_mem hresult
    exists i
    grind
  · grind

theorem getArguments!.mem_getArgument_iff {op : BlockPtr} :
    (op.getArgument index : ValuePtr) ∈ op.getArguments! ctx ↔
    index < op.getNumArguments! ctx := by
  grind [getArguments!, getArgument, getNumArguments!]

@[simp, grind =]
theorem getArguments!.size_eq_getNumArguments! {op : BlockPtr} :
    (op.getArguments! ctx).size = op.getNumArguments! ctx := by
  grind [getArguments!, getNumArguments!]

@[simp, grind =]
theorem getArguments!.getElem!_eq_getArgument {op : BlockPtr} :
    index < op.getNumArguments! ctx →
    (op.getArguments! ctx)[index]! = op.getArgument index := by
  simp only [getArguments!, getArgument]
  grind

@[simp, grind =]
theorem getArguments!.getElem_eq_getArgument
    {op : BlockPtr} {h : index < (op.getArguments! ctx).size} :
    index < op.getNumArguments! ctx →
    (op.getArguments! ctx)[index]'h = op.getArgument index := by
  simp only [getArguments!, getArgument]
  grind

def getArgumentTypes (block : BlockPtr) (ctx : IRContext OpInfo)
    (inBounds : block.InBounds ctx := by grind) : Array TypeAttr :=
  (block.get ctx).arguments.map (·.type)

def getArgumentTypes! (block : BlockPtr) (ctx : IRContext OpInfo) : Array TypeAttr :=
  (block.get! ctx).arguments.map (·.type)

@[grind =_, eq_bang ←]
theorem getArgumentTypes!_eq_getArgumentTypes {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getArgumentTypes! ctx = block.getArgumentTypes ctx (by grind) := by
  grind [getArgumentTypes, getArgumentTypes!, get!_eq_get]

@[grind =]
theorem getArgumentTypes!.size_eq_getNumArguments! {block : BlockPtr} :
    (block.getArgumentTypes! ctx).size = block.getNumArguments! ctx := by
  grind [getArgumentTypes!, getNumArguments!]

def nextArgument (block : BlockPtr) (ctx : IRContext OpInfo)
    (inBounds: block.InBounds ctx := by grind) : BlockArgumentPtr :=
  getArgument block (block.getNumArguments ctx (by grind))

def nextArgument! (block : BlockPtr) (ctx : IRContext OpInfo) : BlockArgumentPtr :=
  getArgument block (block.getNumArguments! ctx)

@[grind =_, eq_bang ←]
theorem nextArgument!_eq_nextArgument {block : BlockPtr} (inBounds : block.InBounds ctx) :
    block.nextArgument! ctx = block.nextArgument ctx inBounds := by
  grind [nextArgument, nextArgument!, getArgument, getNumArguments, getNumArguments!]

@[grind =]
theorem nextArgument!_eq_getArgument {block : BlockPtr} :
    block.nextArgument! ctx = getArgument block (block.getNumArguments! ctx) := by
  grind [nextArgument!, getArgument, getNumArguments!]

def getParent (block : BlockPtr) (ctx : IRContext OpInfo) (inBounds : block.InBounds ctx := by grind) : Option RegionPtr :=
  (block.get ctx (by grind)).parent

def getParent! (block : BlockPtr) (ctx : IRContext OpInfo) : Option RegionPtr :=
  (block.get! ctx).parent

@[grind =_, eq_bang ←]
theorem getParent!_eq_getParent {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getParent! ctx = block.getParent ctx hin := by
  grind [getParent, getParent!]

def getFirstUse (block : BlockPtr) (ctx : IRContext OpInfo) (inBounds : block.InBounds ctx := by grind) : Option BlockOperandPtr :=
  (block.get ctx (by grind)).firstUse

def getFirstUse! (block : BlockPtr) (ctx : IRContext OpInfo) : Option BlockOperandPtr :=
  (block.get! ctx).firstUse

@[grind =_, eq_bang ←]
theorem getFirstUse!_eq_getFirstUse {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getFirstUse! ctx = block.getFirstUse ctx hin := by
  grind [getFirstUse, getFirstUse!]

def getFirstOp (block : BlockPtr) (ctx : IRContext OpInfo) (inBounds : block.InBounds ctx := by grind) : Option OperationPtr :=
  (block.get ctx (by grind)).firstOp

def getFirstOp! (block : BlockPtr) (ctx : IRContext OpInfo) : Option OperationPtr :=
  (block.get! ctx).firstOp

@[grind =_, eq_bang ←]
theorem getFirstOp!_eq_getFirstOp {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getFirstOp! ctx = block.getFirstOp ctx hin := by
  grind [getFirstOp, getFirstOp!]

def getLastOp (block : BlockPtr) (ctx : IRContext OpInfo) (inBounds : block.InBounds ctx := by grind) : Option OperationPtr :=
  (block.get ctx (by grind)).lastOp

def getLastOp! (block : BlockPtr) (ctx : IRContext OpInfo) : Option OperationPtr :=
  (block.get! ctx).lastOp

@[grind =_, eq_bang ←]
theorem getLastOp!_eq_getLastOp {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getLastOp! ctx = block.getLastOp ctx hin := by
  grind [getLastOp, getLastOp!]

def getNextBlock (block : BlockPtr) (ctx : IRContext OpInfo) (inBounds : block.InBounds ctx := by grind) : Option BlockPtr :=
  (block.get ctx (by grind)).next

def getNextBlock! (block : BlockPtr) (ctx : IRContext OpInfo) : Option BlockPtr :=
  (block.get! ctx).next

@[grind =_, eq_bang ←]
theorem getNextBlock!_eq_getNextBlock {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getNextBlock! ctx = block.getNextBlock ctx hin := by
  grind [getNextBlock, getNextBlock!]

def getPrevBlock (block : BlockPtr) (ctx : IRContext OpInfo) (inBounds : block.InBounds ctx := by grind) : Option BlockPtr :=
  (block.get ctx (by grind)).prev

def getPrevBlock! (block : BlockPtr) (ctx : IRContext OpInfo) : Option BlockPtr :=
  (block.get! ctx).prev

@[grind =_, eq_bang ←]
theorem getPrevBlock!_eq_getPrevBlock {block : BlockPtr} (hin : block.InBounds ctx) :
    block.getPrevBlock! ctx = block.getPrevBlock ctx hin := by
  grind [getPrevBlock, getPrevBlock!]

end BlockPtr

/-!
 BlockArgumentPtr accessors
-/

namespace BlockArgumentPtr

@[local grind]
def InBounds (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) : Prop :=
  ∃ h, arg.index < (arg.block.get ctx h).arguments.size

theorem inBounds_def : InBounds arg ctx ↔ ∃ h, arg.index < arg.block.getNumArguments ctx h := by
  rfl

@[no_expose]
instance : Decidable (InBounds arg ctx) := by
  unfold InBounds; infer_instance

@[grind .]
theorem InBounds_iff (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) :
    arg.block.InBounds ctx →
    arg.index < arg.block.getNumArguments! ctx →
    arg.InBounds ctx :=
  by grind [inBounds_def]

def get (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (argIn : arg.InBounds ctx := by grind) : BlockArgument :=
  (arg.block.get ctx (by grind [InBounds])).arguments[arg.index]'(by grind [InBounds])

def get! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) : BlockArgument :=
  (arg.block.get! ctx).arguments[arg.index]!

@[grind =_, eq_bang ←]
theorem get!_eq_get {ptr : BlockArgumentPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem get!_of_not_inBounds {arg : BlockArgumentPtr} (notInBounds : ¬ arg.InBounds ctx) :
    arg.get! ctx = default := by
  cases blockInBounds : decide (arg.block.InBounds ctx)
    <;> grind [get!, BlockPtr.get!_of_not_inBounds, Block.default_arguments_eq, InBounds]

theorem get!_eq_of_BlockPtr_get!_eq {arg : BlockArgumentPtr} :
    arg.block.get! ctx = arg.block.get! ctx' →
    arg.get! ctx = arg.get! ctx' := by
  grind [BlockPtr.get!, get!]

theorem exists_blockArgument_of_mem_getArguments! {bl : BlockPtr} :
    value ∈ bl.getArguments! ctx →
    ∃ blockArg, value = .blockArgument blockArg := by
  grind [BlockPtr.getArguments!]

theorem block_of_mem_getArguments! {blockArg : BlockArgumentPtr} (blockArgIn : blockArg.InBounds ctx) :
    blockArg.block = bl ↔
    (ValuePtr.blockArgument blockArg) ∈ bl.getArguments! ctx := by
  simp only [BlockPtr.getArguments!]
  simp only [Array.mem_map, Array.mem_range, ValuePtr.blockArgument.injEq]
  constructor
  · intro
    exists blockArg.index
    grind [BlockPtr.getNumArguments!, BlockArgumentPtr.InBounds]
  · grind [BlockPtr.getArgument]

def getType (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (inBounds : arg.InBounds ctx := by grind) : TypeAttr :=
  (arg.get ctx (by grind)).type

def getType! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) : TypeAttr :=
  (arg.get! ctx).type

@[grind =_, eq_bang ←]
theorem getType!_eq_getType {arg : BlockArgumentPtr} (hin : arg.InBounds ctx) :
    arg.getType! ctx = arg.getType ctx hin := by
  grind [getType, getType!]

def getFirstUse (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (inBounds : arg.InBounds ctx := by grind) : Option OpOperandPtr :=
  (arg.get ctx (by grind)).firstUse

def getFirstUse! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) : Option OpOperandPtr :=
  (arg.get! ctx).firstUse

@[grind =_, eq_bang ←]
theorem getFirstUse!_eq_getFirstUse {arg : BlockArgumentPtr} (hin : arg.InBounds ctx) :
    arg.getFirstUse! ctx = arg.getFirstUse ctx hin := by
  grind [getFirstUse, getFirstUse!]

def getIndex (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (inBounds : arg.InBounds ctx := by grind) : Nat :=
  (arg.get ctx (by grind)).index

def getIndex! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) : Nat :=
  (arg.get! ctx).index

@[grind =_, eq_bang ←]
theorem getIndex!_eq_getIndex {arg : BlockArgumentPtr} (hin : arg.InBounds ctx) :
    arg.getIndex! ctx = arg.getIndex ctx hin := by
  grind [getIndex, getIndex!]

def getLoc (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (inBounds : arg.InBounds ctx := by grind) : Location :=
  (arg.get ctx (by grind)).loc

def getLoc! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) : Location :=
  (arg.get! ctx).loc

@[grind =_, eq_bang ←]
theorem getLoc!_eq_getLoc {arg : BlockArgumentPtr} (hin : arg.InBounds ctx) :
    arg.getLoc! ctx = arg.getLoc ctx hin := by
  grind [getLoc, getLoc!]

def getOwner (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) (inBounds : arg.InBounds ctx := by grind) : BlockPtr :=
  (arg.get ctx (by grind)).owner

def getOwner! (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) : BlockPtr :=
  (arg.get! ctx).owner

@[grind =_, eq_bang ←]
theorem getOwner!_eq_getOwner {arg : BlockArgumentPtr} (hin : arg.InBounds ctx) :
    arg.getOwner! ctx = arg.getOwner ctx hin := by
  grind [getOwner, getOwner!]

end BlockArgumentPtr

@[simp, grind =]
theorem BlockPtr.getArgumentTypes!.getElem!_eq_getArgument {op : BlockPtr} :
    index < op.getNumArguments! ctx →
    (op.getArgumentTypes! ctx)[index]! = ((op.getArgument index).get! ctx).type := by
  grind [BlockPtr.getNumArguments!, getArgumentTypes!, getArgument, BlockArgumentPtr.get!]

@[simp, grind =]
theorem BlockPtr.getArgumentTypes!.getElem_eq_getArgument
    {block : BlockPtr} {h : index < (block.getArgumentTypes! ctx).size} :
    index < block.getNumArguments! ctx →
    (block.getArgumentTypes! ctx)[index]'h = ((block.getArgument index).get! ctx).type := by
  grind [BlockPtr.getNumArguments!, getArgumentTypes!, getArgument, BlockArgumentPtr.get!]

/-!
 ValuePtr accessors
-/

namespace ValuePtr

inductive InBounds : ValuePtr → IRContext OpInfo → Prop
| op_result ptr ctx : ptr.InBounds ctx → (opResult ptr).InBounds ctx
| block_argument ptr ctx : ptr.InBounds ctx → (blockArgument ptr).InBounds ctx

@[simp, grind=]
theorem inBounds_opResult (ptr : OpResultPtr) (ctx : IRContext OpInfo) :
    (opResult ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [InBounds]

@[simp, grind=]
theorem inBounds_blockArg (ptr : BlockArgumentPtr) (ctx : IRContext OpInfo) :
    (blockArgument ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [InBounds]

@[no_expose]
instance : Decidable (InBounds value ctx) := by
  cases value
  · rw [inBounds_opResult]
    infer_instance
  · rw [inBounds_blockArg]
    infer_instance

def getType (arg : ValuePtr) (ctx : IRContext OpInfo) (argIn : arg.InBounds ctx := by grind) : TypeAttr :=
  match arg with
  | opResult ptr => (ptr.get ctx (by grind)).type
  | blockArgument ptr => (ptr.get ctx (by grind)).type

@[simp, grind =]
theorem getType_opResult {ptr : OpResultPtr} {ctx : IRContext OpInfo} {h : (opResult ptr).InBounds ctx} :
    (opResult ptr).getType ctx = (ptr.get ctx (by grind)).type := by
  grind [getType]

@[simp, grind =]
theorem getType_blockArgument {ptr : BlockArgumentPtr} {ctx : IRContext OpInfo} {h : (blockArgument ptr).InBounds ctx} :
    (blockArgument ptr).getType ctx = (ptr.get ctx (by grind)).type := by
  grind [getType]

def getType! (arg : ValuePtr) (ctx : IRContext OpInfo) : TypeAttr :=
  match arg with
  | opResult ptr => (ptr.get! ctx).type
  | blockArgument ptr => (ptr.get! ctx).type

@[simp, grind =]
theorem getType!_opResult {ptr : OpResultPtr} {ctx : IRContext OpInfo} :
    (opResult ptr).getType! ctx = (ptr.get! ctx).type := by
  grind [getType!]

@[simp, grind =]
theorem getType!_blockArgument {ptr : BlockArgumentPtr} {ctx : IRContext OpInfo} :
    (blockArgument ptr).getType! ctx = (ptr.get! ctx).type := by
  grind [getType!]

@[grind =_, eq_bang ←]
theorem getType!_eq_getType {ptr : ValuePtr} (hin : ptr.InBounds ctx) :
    ptr.getType! ctx = ptr.getType ctx hin := by
  unfold getType getType!; grind

def getFirstUse (arg : ValuePtr) (ctx : IRContext OpInfo) (argIn : arg.InBounds ctx := by grind) : Option OpOperandPtr :=
  match arg with
  | opResult ptr => (ptr.get ctx).firstUse
  | blockArgument ptr => (ptr.get ctx).firstUse

def getFirstUse! (arg : ValuePtr) (ctx : IRContext OpInfo) : Option OpOperandPtr :=
  match arg with
  | opResult ptr => (ptr.get! ctx).firstUse
  | blockArgument ptr => (ptr.get! ctx).firstUse

@[grind =_, eq_bang ←]
theorem getFirstUse!_eq_getFirstUse {ptr : ValuePtr} (hin : ptr.InBounds ctx) :
    ptr.getFirstUse! ctx = ptr.getFirstUse ctx hin := by
  unfold getFirstUse getFirstUse!; grind

theorem getFirstUse!_of_not_inBounds {value : ValuePtr} (notInBounds : ¬ value.InBounds ctx) :
    value.getFirstUse! ctx = none := by
  cases value
  · grind [getFirstUse!, OpResultPtr.get!_of_not_inBounds, OpResult.default_firstUse_eq]
  · simp [inBounds_blockArg] at notInBounds
    simp [getFirstUse!]
    simp [BlockArgumentPtr.get!_of_not_inBounds notInBounds, BlockArgument.default_firstUse_eq]

@[simp, grind =]
theorem getFirstUse_opResult_eq {res : OpResultPtr} {ctx : IRContext OpInfo} {h : res.InBounds ctx} :
    (opResult res).getFirstUse ctx = (res.get ctx).firstUse := by
  grind [getFirstUse]

@[simp, grind =]
theorem getFirstUse_blockArgument_eq {ba : BlockArgumentPtr} {ctx : IRContext OpInfo} {h : ba.InBounds ctx} :
    (blockArgument ba).getFirstUse ctx = (ba.get ctx).firstUse := by
  grind [getFirstUse]

@[simp, grind =]
theorem getFirstUse!_opResult_eq {res : OpResultPtr} {ctx : IRContext OpInfo} :
    (opResult res).getFirstUse! ctx = (res.get! ctx).firstUse := by
  grind [getFirstUse!]

@[simp, grind =]
theorem getFirstUse!_blockArgument_eq {ba : BlockArgumentPtr} {ctx : IRContext OpInfo} :
    (blockArgument ba).getFirstUse! ctx = (ba.get! ctx).firstUse := by
  grind [getFirstUse!]

def definingOp? (value : ValuePtr) : Option OperationPtr :=
  match value with
  | opResult ptr => some ptr.op
  | blockArgument _ => none

@[simp, grind =]
theorem definingOp?_opResult :
    (opResult res).definingOp? = some res.op := by
  grind [definingOp?]

@[simp, grind =]
theorem definingOp?_blockArgument :
    (blockArgument ba).definingOp? = none := by
  grind [definingOp?]

@[grind =]
theorem definingOp?_eq_some_iff {value : ValuePtr} :
    value.definingOp? = some op ↔
    ∃ opRes, value = opResult opRes ∧ opRes.op = op := by
  grind [definingOp?, cases ValuePtr]

@[grind =]
theorem definingOp?_eq_none_iff {value : ValuePtr} :
    value.definingOp? = none ↔
    ∃ blockArg, value = blockArgument blockArg := by
  grind [definingOp?, cases ValuePtr]

/--
Returns true if the value has any uses.
-/
def hasUses (value : ValuePtr) (ctx : IRContext OpInfo) (valueIn : value.InBounds ctx := by grind) : Bool :=
  (value.getFirstUse ctx (by grind)).isSome

theorem hasUses_def {value : ValuePtr} (valueIn : value.InBounds ctx) :
    value.hasUses ctx = (value.getFirstUse ctx).isSome := by
  rfl

/--
Returns true if the value has any uses.
-/
def hasUses! (value : ValuePtr) (ctx : IRContext OpInfo) : Bool :=
  (value.getFirstUse! ctx).isSome

@[grind =_, eq_bang ←]
theorem hasUses!_eq_hasUses {ptr : ValuePtr} (hin : ptr.InBounds ctx) :
    ptr.hasUses! ctx = ptr.hasUses ctx hin := by
  unfold hasUses hasUses!; grind

theorem hasUses!_def {value : ValuePtr} :
    value.hasUses! ctx = (value.getFirstUse! ctx).isSome := by
  grind [hasUses!]

end ValuePtr

namespace OperationPtr

/--
Every operation result is in bounds.
It is not necessary to provide the proof that the operation is in bounds, as out-of-bounds
operations have no results.
-/
@[grind .]
theorem getResults!_mem_inBounds {op : OperationPtr} :
    ∀ v, v ∈ op.getResults! ctx →
    v.InBounds ctx := by
  grind [OperationPtr.getNumResults!, Operation.default_results_eq,
    OperationPtr.get!_of_not_inBounds, OperationPtr.getResults!.mem_iff_exists_index]

/--
A value is either not the result of an operation, or is equal to one of the operation's results.
-/
theorem getResults!_not_mem_or_eq_getResult
    (ctx : IRContext OpInfo) (value : ValuePtr) (op : OperationPtr) :
    value ∉ op.getResults! ctx ∨ (∃ i, i < op.getNumResults! ctx ∧ value = op.getResult i) := by
  grind [OperationPtr.getResults!.mem_iff_exists_index]

theorem getResultTypes!_def {op : OperationPtr} :
    op.getResultTypes! ctx =
    Array.map (fun v => v.getType! ctx) (op.getResults! ctx) := by
  grind [getResultTypes!, getResult, ValuePtr.getType!, OpResultPtr.get!]

@[simp, grind =]
theorem getResultTypes!.getElem!_eq {op : OperationPtr} :
    index < op.getNumResults! ctx →
    (op.getResultTypes! ctx)[index]! = ((op.getResult index).get! ctx).type := by
  grind [getResultTypes!, getNumResults!, getResult, OpResultPtr.get!]

@[simp, grind =]
theorem getResultTypes!.getElem_eq {op : OperationPtr}
    {h : index < (op.getResultTypes! ctx).size} :
    (op.getResultTypes! ctx)[index]'h = ((op.getResult index).get! ctx).type := by
  simp only [getResultTypes!, getResult, OpResultPtr.get!]
  grind

theorem getOperandTypes!_def {op : OperationPtr} :
    op.getOperandTypes! ctx =
    Array.map (fun v => v.getType! ctx) (op.getOperands! ctx) := by
  simp only [getOperandTypes!, getOperands!, Array.map_map]
  congr

@[simp, grind =]
theorem getOperandTypes!.getElem!_eq {op : OperationPtr} :
    index < op.getNumOperands! ctx →
    (op.getOperandTypes! ctx)[index]! = (op.getOperand! ctx index).getType! ctx := by
  grind [getOperandTypes!, getNumOperands!, getOperand!, ValuePtr.getType!,
    OpResultPtr.get!, BlockArgumentPtr.get!, BlockPtr.get!]

@[simp, grind =]
theorem getOperandTypes!.getElem_eq {op : OperationPtr}
    {h : index < (op.getOperandTypes! ctx).size} :
    (op.getOperandTypes! ctx)[index]'h = (op.getOperand! ctx index).getType! ctx := by
  grind [getOperandTypes!, getOperand!, ValuePtr.getType!, OpResultPtr.get!,
    BlockArgumentPtr.get!, BlockPtr.get!]

end OperationPtr

/-!
  OpOperandPtrPtr accessors
-/

namespace OpOperandPtrPtr

inductive InBounds (ctx : IRContext OpInfo) : OpOperandPtrPtr → Prop
  | operandNextUseInBounds ptr : ptr.InBounds ctx → (operandNextUse ptr).InBounds ctx
  | valueFirstUseInBounds ptr : ptr.InBounds ctx → (valueFirstUse ptr).InBounds ctx

@[simp, grind=]
theorem inBounds_operandNextUse (ptr : OpOperandPtr) (ctx : IRContext OpInfo) :
    (operandNextUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [InBounds]

@[simp, grind=]
theorem inBounds_valueFirstUse (ptr : ValuePtr) (ctx : IRContext OpInfo) :
    (valueFirstUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind [InBounds]

@[no_expose]
instance : Decidable (InBounds ctx value) := by
  cases value
  · rw [inBounds_operandNextUse]
    infer_instance
  · rw [inBounds_valueFirstUse]
    infer_instance

def get (ptrPtr : OpOperandPtrPtr) (ctx : IRContext OpInfo) (ptrPtrIn : ptrPtr.InBounds ctx := by grind) : Option OpOperandPtr :=
  match ptrPtr with
  | operandNextUse ptr => (ptr.get ctx).nextUse
  | valueFirstUse val => val.getFirstUse ctx (by grind)

def get! (ptrPtr : OpOperandPtrPtr) (ctx : IRContext OpInfo) : Option OpOperandPtr :=
  match ptrPtr with
  | operandNextUse ptr => (ptr.get! ctx).nextUse
  | valueFirstUse val => val.getFirstUse! ctx

@[grind =_, eq_bang ←]
theorem get!_eq_get {ptrPtr : OpOperandPtrPtr} (hin : ptrPtr.InBounds ctx) :
    ptrPtr.get! ctx = ptrPtr.get ctx hin := by
  unfold get get!; grind

theorem get!_of_not_inBounds {ptrPtr : OpOperandPtrPtr} (notInBounds : ¬ ptrPtr.InBounds ctx) :
    ptrPtr.get! ctx = none := by
  grind [get!, OpOperand.default_nextUse_eq, OpOperandPtr.get!_of_not_inBounds,
    OpResult.default_firstUse_eq, OpResultPtr.get!_of_not_inBounds,
    BlockArgument.default_firstUse_eq, BlockArgumentPtr.get!_of_not_inBounds,
    cases ValuePtr, cases OpOperandPtrPtr]

@[simp, grind =]
theorem get_operandNextUse_eq {ptr : OpOperandPtr} {ctx : IRContext OpInfo} {ptrIn : ptr.InBounds ctx} :
    (operandNextUse ptr).get ctx (by grind) = (ptr.get ctx).nextUse := by
  grind [get]

@[simp, grind =]
theorem get!_operandNextUse_eq {ptr : OpOperandPtr} {ctx : IRContext OpInfo} :
    (operandNextUse ptr).get! ctx = (ptr.get! ctx).nextUse := by
  grind [get!]

@[simp, grind =]
theorem get_valueFirstUse_eq {ptr : ValuePtr} {ctx : IRContext OpInfo} {ptrIn : ptr.InBounds ctx} :
    (valueFirstUse ptr).get ctx (by grind) = ptr.getFirstUse ctx := by
  grind [get]

@[simp, grind =]
theorem get!_valueFirstUse_eq {ptr : ValuePtr} {ctx : IRContext OpInfo} :
    (valueFirstUse ptr).get! ctx = ptr.getFirstUse! ctx := by
  grind [get!]

end OpOperandPtrPtr

/-!
  RegionPtr accessors
-/

namespace RegionPtr

def InBounds (region : RegionPtr) (ctx : IRContext OpInfo) : Prop :=
  region ∈ ctx.regions

theorem inBounds_def : region.InBounds ctx ↔ region ∈ ctx.regions := by rfl

@[no_expose]
instance : Decidable (InBounds region ctx) := by
  unfold InBounds; infer_instance

def get (ptr : RegionPtr) (ctx : IRContext OpInfo) (inBounds : ptr.InBounds ctx := by grind) : Region :=
  ctx.regions[ptr]'(by unfold InBounds at inBounds; grind)

def get! (ptr : RegionPtr) (ctx : IRContext OpInfo) : Region := ctx.regions[ptr]!

@[grind =_, eq_bang ←]
theorem get!_eq_get {ptr : RegionPtr} (hin : ptr.InBounds ctx) :
    ptr.get! ctx = ptr.get ctx hin := by
  grind [get, get!]

theorem get!_of_not_inBounds {ptr : RegionPtr} (notInBounds : ¬ ptr.InBounds ctx) :
    ptr.get! ctx = default := by
  grind [get!, InBounds]

def getParent (region : RegionPtr) (ctx : IRContext OpInfo) (inBounds : region.InBounds ctx := by grind) : Option OperationPtr :=
  (region.get ctx (by grind)).parent

def getParent! (region : RegionPtr) (ctx : IRContext OpInfo) : Option OperationPtr :=
  (region.get! ctx).parent

@[grind =_, eq_bang ←]
theorem getParent!_eq_getParent {region : RegionPtr} (hin : region.InBounds ctx) :
    region.getParent! ctx = region.getParent ctx hin := by
  grind [getParent, getParent!]

def getFirstBlock (region : RegionPtr) (ctx : IRContext OpInfo) (inBounds : region.InBounds ctx := by grind) : Option BlockPtr :=
  (region.get ctx (by grind)).firstBlock

def getFirstBlock! (region : RegionPtr) (ctx : IRContext OpInfo) : Option BlockPtr :=
  (region.get! ctx).firstBlock

@[grind =_, eq_bang ←]
theorem getFirstBlock!_eq_getFirstBlock {region : RegionPtr} (hin : region.InBounds ctx) :
    region.getFirstBlock! ctx = region.getFirstBlock ctx hin := by
  grind [getFirstBlock, getFirstBlock!]

def getLastBlock (region : RegionPtr) (ctx : IRContext OpInfo) (inBounds : region.InBounds ctx := by grind) : Option BlockPtr :=
  (region.get ctx (by grind)).lastBlock

def getLastBlock! (region : RegionPtr) (ctx : IRContext OpInfo) : Option BlockPtr :=
  (region.get! ctx).lastBlock

@[grind =_, eq_bang ←]
theorem getLastBlock!_eq_getLastBlock {region : RegionPtr} (hin : region.InBounds ctx) :
    region.getLastBlock! ctx = region.getLastBlock ctx hin := by
  grind [getLastBlock, getLastBlock!]

end RegionPtr

/-!
  BlockOperandPtrPtr accessors
-/

namespace BlockOperandPtrPtr

@[local grind]
inductive InBounds (ctx : IRContext OpInfo) : BlockOperandPtrPtr → Prop
  | blockOperandNextUseInBounds ptr : ptr.InBounds ctx → (blockOperandNextUse ptr).InBounds ctx
  | blockFirstUseInBounds ptr : ptr.InBounds ctx → (blockFirstUse ptr).InBounds ctx

@[simp, grind=]
theorem inBounds_operandNextUse (ptr : BlockOperandPtr) (ctx : IRContext OpInfo) :
    (blockOperandNextUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[simp, grind=]
theorem inBounds_valueFirstUse (ptr : BlockPtr) (ctx : IRContext OpInfo) :
    (blockFirstUse ptr).InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[no_expose]
instance : Decidable (InBounds ctx ptr) := by
  cases ptr
  · rw [inBounds_operandNextUse]
    infer_instance
  · rw [inBounds_valueFirstUse]
    infer_instance

def get (ptrPtr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) (ptrPtrIn : ptrPtr.InBounds ctx := by grind) : Option BlockOperandPtr :=
  match ptrPtr with
  | blockOperandNextUse ptr => (ptr.get ctx).nextUse
  | blockFirstUse val => (val.get ctx (by grind)).firstUse

def get! (ptrPtr : BlockOperandPtrPtr) (ctx : IRContext OpInfo) : Option BlockOperandPtr :=
  match ptrPtr with
  | blockOperandNextUse ptr => (ptr.get! ctx).nextUse
  | blockFirstUse val => (val.get! ctx).firstUse

@[grind =_, eq_bang ←]
theorem get!_eq_get {ptrPtr : BlockOperandPtrPtr} (hin : ptrPtr.InBounds ctx) :
    ptrPtr.get! ctx = ptrPtr.get ctx hin := by
  unfold get get!; grind

theorem get!_of_not_inBounds {ptrPtr : BlockOperandPtrPtr} (notInBounds : ¬ ptrPtr.InBounds ctx) :
    ptrPtr.get! ctx = none := by
  grind [get!, BlockOperandPtr.get!_of_not_inBounds, BlockOperand.default_nextUse_eq,
    BlockPtr.get!_of_not_inBounds, Block.default_firstUse_eq, cases BlockOperandPtrPtr]

@[grind =]
theorem get!_nextUse_eq {bo : BlockOperandPtr} :
    (blockOperandNextUse bo).get! ctx = (bo.get! ctx).nextUse := by
  grind [get!]

@[grind =]
theorem get!_firstUse_eq {bl : BlockPtr} :
    (blockFirstUse bl).get! ctx = (bl.get! ctx).firstUse := by
  grind [get!]

end BlockOperandPtrPtr

namespace OperationPtr

/-- Return the region directly containing an operation, if one exists. -/
def getParentRegion! (op : OperationPtr) (ctx : IRContext OpInfo) : Option RegionPtr := do
  let block ← (op.get! ctx).parent
  (block.get! ctx).parent

@[grind =]
theorem getParentRegion!_eq_some_iff {op : OperationPtr} :
    op.getParentRegion! ctx = some region ↔
      ∃ block,
        (op.get! ctx).parent = some block ∧
        (block.get! ctx).parent = some region := by
  simp only [OperationPtr.getParentRegion!, bind, Option.bind]
  grind

theorem getParentRegion!_eq_some_of_parent_of_parent {op : OperationPtr} :
    (op.get! ctx).parent = some block →
    (block.get! ctx).parent = some region →
    op.getParentRegion! ctx = some region := by
  grind [OperationPtr.getParentRegion!]

@[expose]
def getParentOp! (op : OperationPtr) (ctx : IRContext OpInfo) : Option OperationPtr := do
  let region ← op.getParentRegion! ctx
  (region.get! ctx).parent

theorem getParentOp!_eq_some_iff {child parent : OperationPtr} {ctx : IRContext OpInfo} :
    child.getParentOp! ctx = some parent ↔
      ∃ block region,
        (child.get! ctx).parent = some block ∧
        (block.get! ctx).parent = some region ∧
        (region.get! ctx).parent = some parent := by
  simp only [OperationPtr.getParentOp!, bind, Option.bind]
  grind

def hasUses.loop (op : OperationPtr) (ctx : IRContext OpInfo) (index : Nat)
    (opIn : op.InBounds ctx := by grind)
    (hresult : index < op.getNumResults ctx := by grind) : Bool :=
  if ((op.getResult index).get ctx).firstUse.isSome then
    true
  else
    match index with
    | 0 => false
    | index' + 1 => hasUses.loop op ctx index'

def hasUses (op : OperationPtr) (ctx : IRContext OpInfo) (opIn : op.InBounds ctx := by grind) : Bool :=
  let numResults := op.getNumResults ctx
  if h : numResults = 0 then
    false
  else
    hasUses.loop op ctx (numResults - 1)

def hasUses!.loop (op : OperationPtr) (ctx : IRContext OpInfo) (index : Nat) : Bool :=
  if ((op.getResult index).get! ctx).firstUse.isSome then
    true
  else
    match index with
    | 0 => false
    | index' + 1 => hasUses!.loop op ctx index'

def hasUses! (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  let numResults := op.getNumResults! ctx
  if numResults = 0 then
    false
  else
    hasUses!.loop op ctx (numResults - 1)

theorem hasUses!.loop_eq_hasUses_loop {op : OperationPtr} (ctx : IRContext OpInfo) (index : Nat)
    (opIn : op.InBounds ctx)
    (hresult : index < op.getNumResults ctx := by grind) :
    hasUses!.loop op ctx index = hasUses.loop op ctx index opIn hresult := by
  induction index
  · grind [hasUses!.loop, hasUses.loop]
  · simp only [hasUses!.loop, hasUses.loop]
    grind

@[grind =_, eq_bang ←]
theorem hasUses!_eq_hasUses {op : OperationPtr} (hin : op.InBounds ctx) :
    op.hasUses! ctx = op.hasUses ctx hin := by
  grind [hasUses!.loop_eq_hasUses_loop, hasUses!, hasUses]

theorem hasUses!.loop_eq_true_iff {op : OperationPtr} {index : Nat} :
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

/-- Return the region containing a value's definition, if it is linked into one. -/
def ValuePtr.getParentRegion! (value : ValuePtr) (ctx : IRContext OpInfo) : Option RegionPtr :=
  match value with
  | .opResult result => result.op.getParentRegion! ctx
  | .blockArgument argument => (argument.block.get! ctx).parent

/-- `ops` is a contiguous chain of operations in a block `parent` in context `ctx`: each operation's
`.next` field points to the following operation in the list, and each operation's `.parent` field
points to `parent`. -/
@[expose]
def BlockPtr.OpChainSlice (ctx : IRContext OpInfo) (parent : BlockPtr) : List OperationPtr → Prop
  | [] => True
  | a :: l =>
    a.InBounds ctx ∧
    (a.get! ctx).parent = some parent ∧
    (∀ b, l.head? = some b → (a.get! ctx).next = some b) ∧
    BlockPtr.OpChainSlice ctx parent l

namespace BlockPtr.OpChainSlice

/-- All operations in an operation chain slice are in bounds. -/
@[grind →]
theorem inBounds_of_mem {ctx : IRContext OpInfo} {parent : BlockPtr} {ops : List OperationPtr}
    (h : BlockPtr.OpChainSlice ctx parent ops) :
    ∀ op, op ∈ ops → op.InBounds ctx := by
  induction ops <;> simp [BlockPtr.OpChainSlice] at h <;> grind

/-- All operations in an operation chain slice have the expected parent. -/
@[grind →]
theorem parent_of_mem {ctx : IRContext OpInfo} {parent : BlockPtr} {ops : List OperationPtr}
    (h : BlockPtr.OpChainSlice ctx parent ops) :
    ∀ op, op ∈ ops → (op.get! ctx).parent = some parent := by
  induction ops <;> simp [BlockPtr.OpChainSlice] at h <;> grind

/-- The empty list is always an operation chain slice. -/
@[simp, grind .]
theorem nil {ctx : IRContext OpInfo} {parent : BlockPtr} :
    BlockPtr.OpChainSlice ctx parent [] := by
  simp [BlockPtr.OpChainSlice]

/-- An `head :: tail` list is an operation chain slice iff the tail is an operation chain slice,
and the head is in bounds, has the same parent, and points to the tail. -/
theorem cons_iff {ctx : IRContext OpInfo} {parent : BlockPtr} {head : OperationPtr} {tail : List OperationPtr} :
    BlockPtr.OpChainSlice ctx parent (head :: tail) ↔
    head.InBounds ctx ∧
    (head.get! ctx).parent = some parent ∧
    (∀ b, tail.head? = some b → (head.get! ctx).next = some b) ∧
    BlockPtr.OpChainSlice ctx parent tail := by
  simp [BlockPtr.OpChainSlice]

end BlockPtr.OpChainSlice

/-- Get the successors of a block. This is defined as the successors of the terminator operation.
In case the block has no terminator, this function returns an empty array. -/
def BlockPtr.getSuccessors! (block : BlockPtr) (ctx : IRContext OpInfo) : Array BlockPtr :=
  let term := (block.get! ctx).lastOp
  match term with
  | none => #[]
  | some term => term.getSuccessors! ctx

/--
  Run a function on all operations in the context.
  In particular, the function provides a proof that the operation pointer is in bounds.
-/
def IRContext.forOpsDepM (ctx : IRContext OpInfo) {m : Type w → Type w'} [Monad m]
    (p : ∀ (op : OperationPtr), op.InBounds ctx → m PUnit) : m PUnit :=
  ctx.operations.forKeysDepM (fun opPtr h => p opPtr (by grind [OperationPtr.InBounds]))

/--
  Run a function on all blocks in the context, providing each callback with a
  proof that the block pointer is in bounds.
-/
def IRContext.forBlocksDepM (ctx : IRContext OpInfo) {m : Type w → Type w'} [Monad m]
    (p : ∀ (block : BlockPtr), block.InBounds ctx → m PUnit) : m PUnit :=
  ctx.blocks.forKeysDepM (fun blockPtr h => p blockPtr (by grind [BlockPtr.InBounds]))

/-- A `forOpsDepM` in `Except` that succeeds ran its body successfully on every operation. -/
theorem IRContext.forOpsDepM_except_ok {ctx : IRContext OpInfo} {ε : Type}
    {p : ∀ (op : OperationPtr), op.InBounds ctx → Except ε PUnit}
    (h : ctx.forOpsDepM p = .ok ⟨⟩) (op : OperationPtr) (opIn : op.InBounds ctx) :
    p op opIn = .ok ⟨⟩ :=
  Std.HashMap.forKeysDepM_except_ok (f := fun opPtr h => p opPtr (by grind [OperationPtr.InBounds]))
    h op (by grind [OperationPtr.InBounds])

/-- A `forBlocksDepM` in `Except` that succeeds ran its body successfully on every block. -/
theorem IRContext.forBlocksDepM_except_ok {ctx : IRContext OpInfo} {ε : Type}
    {p : ∀ (block : BlockPtr), block.InBounds ctx → Except ε PUnit}
    (h : ctx.forBlocksDepM p = .ok ⟨⟩) (block : BlockPtr) (blockIn : block.InBounds ctx) :
    p block blockIn = .ok ⟨⟩ :=
  Std.HashMap.forKeysDepM_except_ok (f := fun blockPtr h => p blockPtr (by grind [BlockPtr.InBounds]))
    h block (by grind [BlockPtr.InBounds])

/-! Generic pointers -/

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

def InBounds (ptr : GenericPtr) (ctx : IRContext OpInfo) : Prop :=
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

variable {ctx : IRContext OpInfo}

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

@[no_expose]
instance : Decidable (InBounds ptr ctx) := by
  cases ptr <;>
  simp only [iff_block, iff_operation, iff_result, iff_opOperand,
    iff_blockOperand, iff_blockOperandPtr, iff_blockArgument, iff_region,
    iff_value, iff_opOperandPtr] <;>
  infer_instance

end generic_ptr
end GenericPtr
