module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLVM.Properties
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
public import Veir.Interpreter.Memory
public import Veir.Data.LLVM.Int.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive GMIR where
| g_add
| g_sub
| g_icmp
| g_anyext
| g_sext
| g_zext
| g_trunc
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def GMIR.propertiesOf : GMIR → Type
  | .g_add | .g_sub | .g_trunc => NswNuwProperties
  | .g_icmp => IcmpProperties
  | .g_zext => NnegProperties
  | .g_anyext | .g_sext => Unit

def GMIR.fromAttrDict
    (op : GMIR) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (GMIR.propertiesOf op) := by
  cases op
  case g_add | g_sub | g_trunc => exact NswNuwProperties.fromAttrDict attrDict
  case g_icmp => exact IcmpProperties.fromAttrDictFor "gmir.g_icmp" attrDict
  case g_zext => exact NnegProperties.fromAttrDict attrDict
  case g_anyext | g_sext => exact .ok ()

def GMIR.toAttrDict
    (op : GMIR) (props : GMIR.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .g_add | .g_sub | .g_trunc => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    let val := (if props.nsw then 1 else 0) + (if props.nuw then 2 else 0)
    if val > 0 then
      dict := dict.insert "overflowFlags".toUTF8
        (.integerAttr (IntegerAttr.mk (Int.ofNat val) (IntegerType.signless 32)))
    dict
  | .g_icmp =>
    let value := IntegerAttr.mk (Int.ofNat props.predicate.toNat) (IntegerType.signless 64)
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr value)
  | .g_zext => props.toAttrDict
  | .g_anyext | .g_sext => {}

#generate_dialect GMIR

instance : IsOpCode GMIR where
  fromName := GMIR.fromName
  name := GMIR.name
  propertiesOf := GMIR.propertiesOf
  fromAttrDict := GMIR.fromAttrDict
  toAttrDict := GMIR.toAttrDict

/--
This replicates the type-group information in LLVM's `GenericOpcodes.td`
(llvm/include/llvm/Target/GenericOpcodes.td).

Immediate operands and operands with LLVM's `unknown` (special) type are omitted and represented
as operation properties instead.

Operands/results of the same type group must have the same concrete type.
Different type groups are unconstrained relative to each other, so they may share a type.
The meaning of a type group is local to a single operation
-/
inductive TypeGroup where
| type (group_id : Nat)
deriving Inhabited, Repr, BEq, DecidableEq, Hashable

structure GenericOpInfo where
  outOperandList : Array TypeGroup
  inOperandList : Array TypeGroup
deriving Inhabited, Repr

def GMIR.genericOpInfo : GMIR → GenericOpInfo
  | .g_add | .g_sub =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 0, .type 0] }
  | .g_icmp =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 1, .type 1] }
  | .g_anyext | .g_sext | .g_zext | .g_trunc =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 1] }

/-- Each result and operand type of `op`, paired with its type group in `opCode`. -/
def GMIR.getTypedGroups! {OpInfo : Type} [IsOpCode OpInfo] (opCode : GMIR) (op : OperationPtr)
    (ctx : IRContext OpInfo) : Array (TypeGroup × TypeAttr) :=
  let info := opCode.genericOpInfo
  info.outOperandList.zip (op.getResultTypes! ctx) ++
    info.inOperandList.zip (op.getOperandTypes! ctx)

private def OperationPtr.verifyGMIRICmp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  -- `gmir.icmp` also compares pointers.
  for i in [0, 1]  do
    ((op.getOperand! ctx.raw i).getType! ctx.raw).verifyIntegerOrPointerType
      s!"{instrName}: Expected operand {i} to have integer or pointer type"
  let resultType := ((op.getResult 0).get! ctx.raw).type
  resultType.verifyIntegerType s!"{instrName}: Expected result to have integer type"

def GMIR.interpretOp' (opType : Veir.GMIR) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .g_anyext => do
    /- TDOO: the semantics need to be updated once we support nondeterminism. -/
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (.val (BitVec.zeroExtend resBw.bitwidth val.getValueD))], mem, none)
  | .g_add => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.add lhs rhs properties.nsw properties.nuw)], mem, none)
  | .g_icmp => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int 1 (Data.LLVM.Int.icmp lhs rhs properties.predicate)], mem, none)
  | .g_sub => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], mem, none)
  | .g_zext => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (Data.LLVM.Int.zext val resBw.bitwidth properties.nneg (by omega))], mem, none)
  | .g_sext => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (Data.LLVM.Int.sext val resBw.bitwidth (by omega))], mem, none)
  | .g_trunc => do
    let [val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    match val with
    | .int w val =>
        let .integerType resBw := resType.val | none
        if h: resBw.bitwidth >= w then none else
        return (#[.int resBw.bitwidth (Data.LLVM.Int.trunc val resBw.bitwidth properties.nsw properties.nuw (by omega))], mem, none)
    | .byte w val =>
        let .byteType resBw := resType.val | none
        if h: resBw.bitwidth >= w then none else
        return (#[.byte resBw.bitwidth (Data.LLVM.Byte.trunc val resBw.bitwidth)], mem, none)
    | _ => none

/--
Verify the local invariants of a `gmir` operation in any operation-info type
containing the `gmir` dialect.
-/
def GMIR.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo GMIR] (opCode : GMIR) (opPtr : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : opPtr.InBounds ctx.raw) :
    Except String PUnit := do
  let info := opCode.genericOpInfo
  -- Verify operand and result counts.
  opPtr.verifyPlainOpCounts ctx opIn info.inOperandList.size info.outOperandList.size
  -- Verify that every member of a type group has the same concrete type.
  let typedGroups := opCode.getTypedGroups! opPtr ctx.raw
  let canon : Std.HashMap TypeGroup TypeAttr :=
    typedGroups.foldl (init := {}) fun canon (slot, ty) => canon.insertIfNew slot ty
  for (group, type) in typedGroups do
    let expected := canon[group]!
    if expected != type then
      let instrName := String.fromUTF8! (IsOpCode.name (opPtr.getOpType ctx.raw opIn))
      throw s!"{instrName}: type mismatch: expected {expected}, got {type}"
  -- Verify opcode-specific type invariants
  match opCode with
  | .g_add | .g_sub =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyIntegerBinop ctx opIn
  | .g_icmp =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRICmp ctx opIn
  | .g_anyext | .g_sext | .g_zext =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyIntegerExtTypes ctx opIn
  | .g_trunc =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyTruncTypes ctx opIn (allowByte := false)

def GMIR.propagatesPoison : GMIR → Bool
  | .g_add | .g_sub | .g_icmp | .g_anyext | .g_sext | .g_zext | .g_trunc => true

def GMIR.getEffects (_op : GMIR) (_props : GMIR.propertiesOf _op) : MemoryEffects :=
  .none

def GMIR.isConstantLike (_op : GMIR) : Bool :=
  false

def GMIR.hasSSADominance (_op : GMIR) (_index : Nat) : Bool :=
  true

def GMIR.isTerminator (_op : GMIR) : Bool :=
  false

instance : HasOpInfo GMIR where
  verifyLocalInvariants := GMIR.verifyLocalInvariants
  propagatesPoison := GMIR.propagatesPoison
  getEffects := GMIR.getEffects
  isConstantLike := GMIR.isConstantLike
  hasSSADominance := GMIR.hasSSADominance
  isTerminator := GMIR.isTerminator

end

end Veir
