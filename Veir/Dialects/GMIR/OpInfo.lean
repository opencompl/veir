module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLVM.Properties
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
        (.integerAttr (IntegerAttr.mk (Int.ofNat val) (IntegerType.mk 32)))
    dict
  | .g_icmp =>
    let value := IntegerAttr.mk (Int.ofNat props.predicate.toNat) (IntegerType.mk 64)
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
  let typedGroups := info.outOperandList.zip (opPtr.getResultTypes! ctx.raw) ++
                     info.inOperandList.zip (opPtr.getOperandTypes! ctx.raw)
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
