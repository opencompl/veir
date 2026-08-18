module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Comb.Properties
public import Veir.Dialects.HW.OpInfo
public import Veir.ConstantMaterialization
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Comb where
| add
| and
| concat
| divs
| divu
| extract
| icmp
| mods
| modu
| mul
| mux
| or
| parity
| replicate
| reverse
| shl
| shrs
| shru
| sub
| xor
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Comb.propertiesOf (op : Comb) : Type :=
match op with
| .extract => CombExtractProperties
| .icmp => CombIcmpProperties
| _ => Unit

def Comb.fromAttrDict
    (op : Comb) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Comb.propertiesOf op) := by
  cases op
  case extract => exact CombExtractProperties.fromAttrDict attrDict
  case icmp => exact CombIcmpProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Comb.toAttrDict
    (op : Comb) (props : Comb.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .extract =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "lowBit".toUTF8 (Attribute.integerAttr props.lowBit)
  | .icmp =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr props.predicate)
  | _ => Std.HashMap.emptyWithCapacity 0

def Comb.getEffects
    (_op : Comb) (_props : Comb.propertiesOf _op) : MemoryEffects :=
  .none

def Comb.isConstantLike (_op : Comb) : Bool :=
  false

def Comb.hasSSADominance (_op : Comb) (_index : Nat) : Bool :=
  true

#generate_dialect Comb

instance : HasOpInfo Comb where
  fromName := Comb.fromName
  name := Comb.name
  propertiesOf := Comb.propertiesOf
  fromAttrDict := Comb.fromAttrDict
  toAttrDict := Comb.toAttrDict
  getEffects := Comb.getEffects
  isConstantLike := Comb.isConstantLike
  hasSSADominance := Comb.hasSSADominance

/-- CIRCT combinational folds use the HW dialect's integer constant. -/
def Comb.materializeConstant {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo HW]
    (_op : Comb) (value : RuntimeValue) (type : TypeAttr) : Option (Materialized OpInfo) :=
  match value, type.val with
  | .int bw (.val value), .integerType intType =>
    if bw = intType.bitwidth then
      some (.of HW.constant (HWConstantProperties.mk (IntegerAttr.mk value.toInt intType)))
    else none
  | _, _ => none

/--
Verify the local invariants of a `comb` operation in any operation-info type
containing the `comb` dialect.
-/
def Comb.verifyLocalInvariants {OpInfo : Type} [HasOpInfo OpInfo]
    [HasDialect OpInfo Comb] (opType : Comb) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .add | .and | .mul | .or | .xor => do
    if op.getNumOperands ctx.raw opIn < 1 then
      throw "Expected 1 or more operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .concat => do
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .divs | .divu | .icmp | .mods | .modu | .shl | .shrs | .shru | .sub => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .extract | .parity | .replicate | .reverse => do
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()
  | .mux => do
    op.verifyPlainOpCounts ctx opIn 3 1
    pure ()

end

end Veir
