module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.Builtin.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Builtin where
| unregistered
| module
| unrealized_conversion_cast
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Builtin.propertiesOf (op : Builtin) : Type :=
match op with
| .unregistered => UnregisteredProperties
| _ => Unit

def Builtin.fromAttrDict
    (op : Builtin) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Builtin.propertiesOf op) := by
  cases op
  case unregistered => exact UnregisteredProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Builtin.toAttrDict
    (op : Builtin) (props : Builtin.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .unregistered => Std.HashMap.ofList props.properties.entries.toList
  | _ => Std.HashMap.emptyWithCapacity 0

def Builtin.getEffects
    (op : Builtin) (_props : Builtin.propertiesOf op) : MemoryEffects :=
  match op with
  | .unrealized_conversion_cast => .none
  | _ => .unknown

def Builtin.isConstantLike (_op : Builtin) : Bool :=
  false

def Builtin.isIsolatedFromAbove (op : Builtin) : Bool :=
  match op with
  | .module => true
  | _ => false

def Builtin.getRegionKind (op : Builtin) (_index : Nat) : RegionKind :=
  match op with
  | .module | .unregistered => .Graph
  | _ => .SSACFG

def Builtin.hasSSADominance (op : Builtin) (_index : Nat) : Bool :=
  match op with
  | .module | .unregistered => false
  | _ => true

/-- A `builtin.module` body holds no terminator, and an unregistered operation
    makes no promise about its regions. -/
def Builtin.hasNoTerminator (op : Builtin) (_index : Nat) : Bool :=
  match op with
  | .module | .unregistered => true
  | _ => false

#generate_dialect Builtin

instance : IsOpCode Builtin where
  fromName := Builtin.fromName
  name := Builtin.name
  propertiesOf := Builtin.propertiesOf
  fromAttrDict := Builtin.fromAttrDict
  toAttrDict := Builtin.toAttrDict

/--
Verify the local invariants of a `builtin` operation in any operation-info type
containing the `builtin` dialect.
-/
@[expose]
def Builtin.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Builtin] (opType : Builtin) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .unregistered => pure ()
  | .unrealized_conversion_cast => do
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()
  | .module => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()

instance : HasOpInfo Builtin where
  verifyLocalInvariants := Builtin.verifyLocalInvariants
  getEffects := Builtin.getEffects
  isConstantLike := Builtin.isConstantLike
  getRegionKind := Builtin.getRegionKind
  hasSSADominance := Builtin.hasSSADominance
  hasNoTerminator := Builtin.hasNoTerminator
  isIsolatedFromAbove := Builtin.isIsolatedFromAbove

end

end Veir
