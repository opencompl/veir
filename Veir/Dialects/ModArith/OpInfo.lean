module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.ModArith.Properties
public import Veir.ConstantMaterialization
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
meta import Veir.Meta.OpCode

open Veir.Data

namespace Veir

public section

@[opcodes]
inductive Mod_Arith where
| add
| constant
| mul
| sub
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Mod_Arith.propertiesOf (op : Mod_Arith) : Type :=
match op with
| .constant => ModArithConstantProperties
| .add | .sub | .mul => Unit

def Mod_Arith.fromAttrDict
    (op : Mod_Arith) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Mod_Arith.propertiesOf op) := by
  cases op
  case constant => exact ModArithConstantProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Mod_Arith.toAttrDict
    (op : Mod_Arith) (props : Mod_Arith.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert
      "value".toUTF8 (Attribute.integerAttr props.value)
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Mod_Arith.getEffects
    (_op : Mod_Arith) (_props : Mod_Arith.propertiesOf _op) : MemoryEffects :=
  .none

def Mod_Arith.isConstantLike (op : Mod_Arith) : Bool :=
  match op with
  | .constant => true
  | _ => false

def Mod_Arith.hasSSADominance (_op : Mod_Arith) (_index : Nat) : Bool :=
  true

#generate_dialect Mod_Arith

instance : IsOpCode Mod_Arith where
  fromName := Mod_Arith.fromName
  name := Mod_Arith.name
  propertiesOf := Mod_Arith.propertiesOf
  fromAttrDict := Mod_Arith.fromAttrDict
  toAttrDict := Mod_Arith.toAttrDict

/--
Materialize concrete modular-integer fold results.
-/
def Mod_Arith.materializeConstant {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo Mod_Arith]
    (_op : Mod_Arith) (value : RuntimeValue) (type : TypeAttr) : Option (Materialized OpInfo) :=
  match value, type.val with
  | .int bw (.val value), .modArithType modType =>
    if bw = modType.modulus.type.bitwidth then
      some (.of Mod_Arith.constant
        (ModArithConstantProperties.mk
          (IntegerAttr.mk (Int.ofNat value.toNat) modType.modulus.type)))
    else none
  | _, _ => none

def TypeAttr.verifyModArithType (ty : TypeAttr) (msg : String) : Except String ModArithType :=
  match ty.val with
  | .modArithType type => do
    let modulus := type.modulus.value
    let bitWidth := type.modulus.type.bitwidth
    if modulus ≤ 0 then
      throw s!"{msg} but found invalid ModArithType type: modulus {modulus} must be positive."
    if modulus ≥ (2 ^ bitWidth) then
      throw s!"{msg} but found invalid ModArithType type: modulus {modulus} does not fit into the underlying storage type 'i{bitWidth}'."
    pure type
  | type => throw s!"{msg} but found {type} instead."

def OperationPtr.verifyModArithBinOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"
  let _ ← operandType.verifyModArithType s!"{instrName}: Expected ModArithType"

def OperationPtr.verifyModArithConstantOp {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Mod_Arith] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 0 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let mat ← ((op.getResult 0).get! ctx.raw).type.verifyModArithType
    s!"{instrName}: Expected result to have ModArithType"
  let value := (op.getProperties! ctx.raw Mod_Arith.constant).value.value
  let bw := mat.modulus.type.bitwidth
  -- Slightly odd range because the storage type is signless.
  if value < -(2 ^ (bw - 1) : Int) ∨ (2 ^ bw : Int) ≤ value then
    throw s!"{instrName}: constant value {value} does not fit in storage type 'i{bw}'."

/--
Verify the local invariants of a `mod_arith` operation in any operation-info
type containing the `mod_arith` dialect.
-/
def Mod_Arith.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Mod_Arith] (opType : Mod_Arith) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .add | .mul | .sub => do
    op.verifyModArithBinOp ctx opIn
    pure ()
  | .constant => do
    op.verifyModArithConstantOp ctx opIn
    pure ()

/-- Matches two integer operands and casts them to the expected bitwidth `bw`. -/
private def ModArith.binaryOperands (bw : Nat) (operands : Array RuntimeValue) :
    Option (LLVM.Int bw × LLVM.Int bw) := do
  let [RuntimeValue.int bw' lhs, RuntimeValue.int bw'' rhs] := operands.toList | none
  if h : bw' = bw ∧ bw'' = bw then
    return (lhs.cast h.left, rhs.cast h.right)
  else
    none

def ModArith.interpretOp' (opType : Veir.Mod_Arith) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Interp ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .constant => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw⟩⟩⟩ := resType.val | none
    let res := LLVM.Int.constant bw (properties.value.value % mod)
    return (#[RuntimeValue.int bw res], none)
  | .add => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw⟩⟩⟩ := resType.val | none
    let some (lhs, rhs) := ModArith.binaryOperands bw operands | none
    let res :=
      match lhs.toNat?, rhs.toNat? with
      | some lhs, some rhs => LLVM.Int.constant bw ((lhs + rhs) % mod)
      | _, _ => LLVM.Int.poison
    return (#[RuntimeValue.int bw res], none)
  | .sub => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw⟩⟩⟩ := resType.val | none
    let some (lhs, rhs) := ModArith.binaryOperands bw operands | none
    let res :=
      match lhs.toNat?, rhs.toNat? with
      | some lhs, some rhs => LLVM.Int.constant bw ((Int.ofNat lhs - rhs) % mod)
      | _, _ => LLVM.Int.poison
    return (#[RuntimeValue.int bw res], none)
  | .mul => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw⟩⟩⟩ := resType.val | none
    let some (lhs, rhs) := ModArith.binaryOperands bw operands | none
    let res :=
      match lhs.toNat?, rhs.toNat? with
      | some lhs, some rhs => LLVM.Int.constant bw ((lhs * rhs) % mod)
      | _, _ => LLVM.Int.poison
    return (#[RuntimeValue.int bw res], none)

instance : HasOpInfo Mod_Arith where
  verifyLocalInvariants := Mod_Arith.verifyLocalInvariants
  getEffects := Mod_Arith.getEffects
  isConstantLike := Mod_Arith.isConstantLike
  hasSSADominance := Mod_Arith.hasSSADominance
