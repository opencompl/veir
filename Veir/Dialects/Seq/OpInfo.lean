module

public import Veir.IR.OpInfo
public import Veir.Dialects.Seq.Properties
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

/-- `__` in a constructor name becomes `.` in the operation name, so `firmem__read_port` is
`seq.firmem.read_port`. -/
@[opcodes]
inductive Seq where
| to_clock
| firreg
| firmem
| firmem__read_port
| firmem__write_port
| firmem__read_write_port
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Seq.propertiesOf (op : Seq) : Type :=
match op with
| .to_clock => Unit
| .firreg => SeqFirRegProperties
| .firmem => SeqFirMemProperties
-- A read port has one optional operand, `enable`, and it comes last, so MLIR reads its
-- presence off the operand count and CIRCT gives the op no `operandSegmentSizes`.
| .firmem__read_port => Unit
| .firmem__write_port | .firmem__read_write_port => SeqFirMemPortProperties

def Seq.fromAttrDict
    (op : Seq) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Seq.propertiesOf op) := by
  cases op
  case to_clock => exact .ok ()
  case firreg => exact SeqFirRegProperties.fromAttrDict attrDict
  case firmem => exact SeqFirMemProperties.fromAttrDict attrDict
  case firmem__read_port => exact .ok ()
  case firmem__write_port =>
    exact SeqFirMemPortProperties.fromAttrDict "seq.firmem.write_port" attrDict
  case firmem__read_write_port =>
    exact SeqFirMemPortProperties.fromAttrDict "seq.firmem.read_write_port" attrDict

def Seq.toAttrDict
    (op : Seq) (props : Seq.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .to_clock => Std.HashMap.emptyWithCapacity 0
  | .firreg => Id.run do
    let dict : Std.HashMap ByteArray Attribute := Std.HashMap.emptyWithCapacity 3
    let dict := dict.insert "name".toUTF8 (.stringAttr props.name)
    let dict :=
      if props.isAsync then dict.insert "isAsync".toUTF8 (.unitAttr .mk) else dict
    let dict :=
      match props.preset with
      | some preset => dict.insert "preset".toUTF8 (.integerAttr preset)
      | none => dict
    dict
  | .firmem => Id.run do
    let dict : Std.HashMap ByteArray Attribute := Std.HashMap.emptyWithCapacity 5
    let dict :=
      match props.name with
      | some name => dict.insert "name".toUTF8 (.stringAttr name)
      | none => dict
    let dict := dict.insert "readLatency".toUTF8 (.integerAttr props.readLatency)
    let dict := dict.insert "writeLatency".toUTF8 (.integerAttr props.writeLatency)
    let dict := dict.insert "ruw".toUTF8 (.integerAttr props.ruw)
    let dict := dict.insert "wuw".toUTF8 (.integerAttr props.wuw)
    dict
  | .firmem__read_port => Std.HashMap.emptyWithCapacity 0
  | .firmem__write_port | .firmem__read_write_port =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "operandSegmentSizes".toUTF8 (.denseArrayAttr props.operandSegmentSizes)

def Seq.propagatesPoison (op : Seq) : Bool :=
  match op with
  | .to_clock | .firreg => true
  | .firmem | .firmem__read_port | .firmem__write_port | .firmem__read_write_port => false

@[is_terminator]
def Seq.isTerminator (_op : Seq) : Bool :=
  false

@[get_effects]
def Seq.getEffects
    (op : Seq) (_props : Seq.propertiesOf op) : MemoryEffects :=
  match op with
  | .to_clock | .firreg => .none
  | .firmem => .allocate
  | .firmem__read_port => .read
  | .firmem__write_port => .write
  | .firmem__read_write_port => .readWrite

def Seq.isConstantLike (_op : Seq) : Bool :=
  false

def Seq.hasSSADominance (_op : Seq) (_index : Nat) : Bool :=
  true

def Seq.isIsolatedFromAbove (_op : Seq) : Bool :=
  false

#generate_dialect Seq

instance : IsOpCode Seq where
  fromName := Seq.fromName
  name := Seq.name
  propertiesOf := Seq.propertiesOf
  fromAttrDict := Seq.fromAttrDict
  toAttrDict := Seq.toAttrDict

/--
The address width CIRCT gives a `seq.firmem` port: the number of bits needed to index `depth`
words, i.e. the ceiling of its base-2 logarithm.
-/
def Seq.firMemAddressWidth (depth : Nat) : Nat :=
  if depth ≤ 1 then 0 else Nat.log2 (depth - 1) + 1

/--
Resolve a `seq.firmem` port's `operandSegmentSizes` into the actual operand index of each of its
declared operands. `required` says, in declaration order, whether each operand must be present;
the result holds `none` at a position whose optional operand was omitted.
-/
private def Seq.firMemPortOperands (opName : String) (required : Array Bool)
    (sizes : Array Int) (numOperands : Nat) : Except String (Array (Option Nat)) := do
  if sizes.size ≠ required.size then
    throw s!"{opName}: expected 'operandSegmentSizes' to have {required.size} entries, \
      but got {sizes.size}"
  let mut indices : Array (Option Nat) := #[]
  let mut next := 0
  for (size, isRequired) in sizes.zip required do
    if size = 0 then
      if isRequired then
        throw s!"{opName}: operand #{indices.size} is required, but its segment size is 0"
      indices := indices.push none
    else if size = 1 then
      indices := indices.push (some next)
      next := next + 1
    else
      throw s!"{opName}: every 'operandSegmentSizes' entry must be 0 or 1, but got {size}"
  if next ≠ numOperands then
    throw s!"{opName}: 'operandSegmentSizes' accounts for {next} operands, \
      but the operation has {numOperands}"
  return indices

/-- The signless integer width of the type of operand `index`. -/
private def Seq.firMemOperandWidth {OpInfo : Type} [IsOpCode OpInfo] (opName what : String)
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (index : Nat) : Except String Nat := do
  let .integerType ty := ((op.getOperand! ctx.raw index).getType! ctx.raw).val
    | throw s!"{opName}: expected {what} to be a signless integer"
  return ty.bitwidth

/--
Verify the shape shared by all three `seq.firmem` port operations: the memory, the address and
the clock, plus the optional enable. Returns the memory's type and the resolved operand indices
so the caller can go on to check its own data and mask operands.
-/
private def Seq.verifyFirMemPort {OpInfo : Type} [IsOpCode OpInfo] (opName : String)
    (required : Array Bool) (sizes : Array Int) (results : Nat) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) :
    Except String (Seq.FirMemType × Array (Option Nat)) := do
  if op.getNumResults ctx.raw opIn ≠ results then
    throw s!"{opName}: Expected {results} result(s)"
  if op.getNumRegions ctx.raw opIn ≠ 0 then
    throw s!"{opName}: Expected 0 regions"
  if op.getNumSuccessors ctx.raw opIn ≠ 0 then
    throw s!"{opName}: Expected 0 successors"
  let indices ← Seq.firMemPortOperands opName required sizes (op.getNumOperands ctx.raw opIn)
  let .seqFirMemType memType := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
    | throw s!"{opName}: expected the memory operand to be a '!seq.firmem'"
  let addressWidth ← Seq.firMemOperandWidth opName "the address" op ctx 1
  let expected := Seq.firMemAddressWidth memType.depth
  if addressWidth ≠ expected then
    throw s!"{opName}: a memory of depth {memType.depth} takes an i{expected} address, \
      but got i{addressWidth}"
  let .seqClockType _ := ((op.getOperand! ctx.raw 2).getType! ctx.raw).val
    | throw s!"{opName}: expected the clock operand to be a '!seq.clock'"
  if let some enable := indices[3]! then
    let enableWidth ← Seq.firMemOperandWidth opName "the enable" op ctx enable
    if enableWidth ≠ 1 then
      throw s!"{opName}: expected the enable to be an i1, but got i{enableWidth}"
  return (memType, indices)

/-- Verify a `seq.firmem` port's optional mask against the memory's mask granularity. -/
private def Seq.verifyFirMemMask {OpInfo : Type} [IsOpCode OpInfo] (opName : String)
    (memType : Seq.FirMemType) (mask : Option Nat) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) : Except String PUnit := do
  match memType.maskWidth, mask with
  | none, none => pure ()
  | none, some _ => throw s!"{opName}: the memory is unmasked, so it takes no mask operand"
  | some width, none => throw s!"{opName}: the memory has an i{width} mask, which is missing"
  | some width, some mask =>
    let maskWidth ← Seq.firMemOperandWidth opName "the mask" op ctx mask
    if maskWidth ≠ width then
      throw s!"{opName}: expected an i{width} mask, but got i{maskWidth}"

/--
Verify the local invariants of a `seq` operation in any operation-info type
containing the `seq` dialect.
-/
def Seq.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Seq] (opType : Seq) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .to_clock => do
    op.verifyPlainOpCounts ctx opIn 1 1
  | .firreg => do
    let numOps := op.getNumOperands ctx.raw opIn
    if ¬(numOps >= 2 ∧ numOps ≤ 4) then
      throw "Expected 2, 3 or 4 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
  | .firmem => do
    op.verifyPlainOpCounts ctx opIn 0 1
    let .seqFirMemType _ := ((op.getResult 0).getType! ctx.raw).val
      | throw "seq.firmem: expected the result to be a '!seq.firmem'"
    let props := op.getProperties! ctx.raw Seq.firmem
    if props.ruw.value < 0 ∨ props.ruw.value > 2 then
      throw s!"seq.firmem: 'ruw' is 0 undefined, 1 old or 2 new, but got {props.ruw.value}"
    if props.wuw.value < 0 ∨ props.wuw.value > 1 then
      throw s!"seq.firmem: 'wuw' is 0 undefined or 1 port_order, but got {props.wuw.value}"
    if props.readLatency.value < 0 then
      throw s!"seq.firmem: 'readLatency' cannot be negative, but got {props.readLatency.value}"
    if props.writeLatency.value < 1 then
      throw s!"seq.firmem: 'writeLatency' must be at least 1, but got {props.writeLatency.value}"
  | .firmem__read_port => do
    let opName := "seq.firmem.read_port"
    -- No `operandSegmentSizes` to consult, so the segments are reconstructed from the count.
    let numOps := op.getNumOperands ctx.raw opIn
    if numOps < 3 ∨ numOps > 4 then
      throw s!"{opName}: Expected 3 or 4 operands"
    let sizes := if numOps = 3 then #[1, 1, 1, 0] else #[1, 1, 1, 1]
    let (memType, _) ←
      Seq.verifyFirMemPort opName #[true, true, true, false] sizes 1 op ctx opIn
    let .integerType dataType := ((op.getResult 0).getType! ctx.raw).val
      | throw s!"{opName}: expected the result to be a signless integer"
    if dataType.bitwidth ≠ memType.width then
      throw s!"{opName}: a memory of width {memType.width} reads i{memType.width}, \
        but the result is i{dataType.bitwidth}"
  | .firmem__write_port => do
    let opName := "seq.firmem.write_port"
    let sizes := (op.getProperties! ctx.raw Seq.firmem__write_port).operandSegmentSizes.values
    let (memType, indices) ←
      Seq.verifyFirMemPort opName #[true, true, true, false, true, false] sizes 0 op ctx opIn
    let dataWidth ← Seq.firMemOperandWidth opName "the data" op ctx indices[4]!.get!
    if dataWidth ≠ memType.width then
      throw s!"{opName}: a memory of width {memType.width} takes i{memType.width} data, \
        but got i{dataWidth}"
    Seq.verifyFirMemMask opName memType indices[5]! op ctx
  | .firmem__read_write_port => do
    let opName := "seq.firmem.read_write_port"
    let sizes :=
      (op.getProperties! ctx.raw Seq.firmem__read_write_port).operandSegmentSizes.values
    let (memType, indices) ←
      Seq.verifyFirMemPort opName #[true, true, true, false, true, true, false] sizes 1 op ctx opIn
    let dataWidth ← Seq.firMemOperandWidth opName "the write data" op ctx indices[4]!.get!
    if dataWidth ≠ memType.width then
      throw s!"{opName}: a memory of width {memType.width} takes i{memType.width} data, \
        but got i{dataWidth}"
    let modeWidth ← Seq.firMemOperandWidth opName "the mode" op ctx indices[5]!.get!
    if modeWidth ≠ 1 then
      throw s!"{opName}: expected the mode to be an i1, but got i{modeWidth}"
    let .integerType readType := ((op.getResult 0).getType! ctx.raw).val
      | throw s!"{opName}: expected the result to be a signless integer"
    if readType.bitwidth ≠ memType.width then
      throw s!"{opName}: a memory of width {memType.width} reads i{memType.width}, \
        but the result is i{readType.bitwidth}"
    Seq.verifyFirMemMask opName memType indices[6]! op ctx

instance : HasOpInfo Seq where
  verifyLocalInvariants := Seq.verifyLocalInvariants
  getEffects := Seq.getEffects
  isConstantLike := Seq.isConstantLike
  hasSSADominance := Seq.hasSSADominance
  isTerminator := Seq.isTerminator
  isIsolatedFromAbove := Seq.isIsolatedFromAbove

end
