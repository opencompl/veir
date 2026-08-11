module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.Cf.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Cf where
| br
| cond_br
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Cf.propertiesOf (op : Cf) : Type :=
match op with
| .cond_br => CondBrProperties
| _ => Unit

def Cf.fromAttrDict
    (op : Cf) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Cf.propertiesOf op) := by
  cases op
  case cond_br => exact CondBrProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Cf.toAttrDict
    (op : Cf) (props : Cf.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .cond_br =>
    let dict := (Std.HashMap.emptyWithCapacity 2).insert
      "branch_weights".toUTF8 (.denseArrayAttr props.branch_weights)
    dict.insert "operandSegmentSizes".toUTF8
      (Attribute.denseArrayAttr props.operandSegmentSizes)
  | _ => Std.HashMap.emptyWithCapacity 0

def Cf.hasSideEffects (_op : Cf) (_props : Cf.propertiesOf _op) : Bool :=
  true

def Cf.getEffects
    (_op : Cf) (_props : Cf.propertiesOf _op) : MemoryEffects :=
  .none

def Cf.isConstantLike (_op : Cf) : Bool :=
  false

def Cf.hasSSADominance (_op : Cf) (_index : Nat) : Bool :=
  true

/-- Every `cf` operation is a branch, and so terminates its block. -/
def Cf.isTerminator (_op : Cf) : Bool :=
  true

#generate_dialect Cf

instance : HasOpInfo Cf where
  fromName := Cf.fromName
  name := Cf.name
  propertiesOf := Cf.propertiesOf
  fromAttrDict := Cf.fromAttrDict
  toAttrDict := Cf.toAttrDict
  hasSideEffects := Cf.hasSideEffects
  getEffects := Cf.getEffects
  isConstantLike := Cf.isConstantLike
  hasSSADominance := Cf.hasSSADominance
  isTerminator := Cf.isTerminator

/--
Verify the local invariants of a `cf` operation in any operation-info type
containing the `cf` dialect.
-/
def Cf.verifyLocalInvariants {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo Cf]
    (opType : Cf) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .br =>
    op.verifyUnconditionalBranch ctx opIn
  | .cond_br =>
    op.verifyTerminatorCounts ctx opIn 2
    let props : Cf.propertiesOf .cond_br :=
      HasDialect.toDialectProperties (OpInfo := OpInfo) Cf.cond_br
        (op.getProperties! ctx.raw (ofDialect OpInfo Cf.cond_br))
    if props.branch_weights.values.size ≠ 2 && props.branch_weights.values.size ≠ 0 then
      throw "Expected 0 or 2 branch weights"
    op.verifyCondBranchOperandSegmentSizes ctx opIn props.operandSegmentSizes 1

end

end Veir
