module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.PDL.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive PDL where
| attribute
| operand
| type
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def PDL.propertiesOf (op : PDL) : Type :=
match op with
| .attribute => PDLAttributeProperties
| .operand => Unit
| .type => PDLTypeProperties

def PDL.fromAttrDict
    (op : PDL) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (PDL.propertiesOf op) :=
  match op with
  | .attribute => PDLAttributeProperties.fromAttrDict attrDict
  | .operand =>
    if attrDict.size > 0 then
      let plural := if attrDict.size = 1 then "property" else "properties"
      .error s!"pdl.operand: expected no properties, but got {attrDict.size} {plural}"
    else
      .ok ()
  | .type => PDLTypeProperties.fromAttrDict attrDict

def PDL.toAttrDict
    (op : PDL) (props : PDL.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .attribute =>
    match props.value with
    | some value => (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 value
    | none => Std.HashMap.emptyWithCapacity 0
  | .operand => Std.HashMap.emptyWithCapacity 0
  | .type =>
    match props.constantType with
    | some constantType =>
      (Std.HashMap.emptyWithCapacity 1).insert "constantType".toUTF8 constantType
    | none => Std.HashMap.emptyWithCapacity 0

/-- The `pdl` operations are declarative pattern descriptions and are `Pure`. -/
def PDL.hasSideEffects (_op : PDL) (_props : PDL.propertiesOf _op) : Bool :=
  false

def PDL.readsMemory (_op : PDL) : Bool :=
  false

def PDL.isConstantLike (_op : PDL) : Bool :=
  false

def PDL.hasSSADominance (_op : PDL) (_index : Nat) : Bool :=
  true

#generate_dialect PDL

instance : HasDialectOpInfo PDL where
  fromName := PDL.fromName
  name := PDL.name
  propertiesOf := PDL.propertiesOf
  fromAttrDict := PDL.fromAttrDict
  toAttrDict := PDL.toAttrDict
  hasSideEffects := PDL.hasSideEffects
  readsMemory := PDL.readsMemory
  isConstantLike := PDL.isConstantLike
  hasSSADominance := PDL.hasSSADominance

/--
Verify the local invariants of a `pdl` operation in any operation-info type
containing the `pdl` dialect.

TODO: An unconstrained `pdl.type` needs a use that binds it, but that invariant
only applies inside the matcher body of a `pdl.pattern`, which is not modelled
yet.
-/
def PDL.verifyLocalInvariants {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo PDL]
    (opType : PDL) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .attribute =>
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyResultTypeMatches ctx (PDL.AttributeType.mk : TypeAttr)
      "Expected the result to be of type '!pdl.attribute'"
    /- The `valueType` operand is optional. -/
    let numOperands := op.getNumOperands ctx.raw opIn
    if numOperands > 1 then
      throw "Expected at most 1 operand"
    if numOperands = 1 then
      let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
      if operandType.val ≠ (PDL.TypeType.mk : TypeAttr).val then
        throw "Expected the `valueType` operand to be of type '!pdl.type'"
    let props : PDL.propertiesOf .attribute :=
      HasDialect.toDialectProperties (OpInfo := OpInfo) PDL.attribute
        (op.getProperties! ctx.raw (ofDialect OpInfo PDL.attribute))
    /- A `pdl.attribute` is constrained either by an expected type or by a
       constant value, but never by both, as the constant provides its own type. -/
    if props.value.isSome && numOperands = 1 then
      throw "Expected only one of [`type`, `value`] to be set"
  | .operand =>
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyResultTypeMatches ctx (PDL.ValueType.mk : TypeAttr)
      "Expected the result to be of type '!pdl.value'"
    /- The `valueType` operand is optional. -/
    let numOperands := op.getNumOperands ctx.raw opIn
    if numOperands > 1 then
      throw "Expected at most 1 operand"
    if numOperands = 1 then
      let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
      if operandType.val ≠ (PDL.TypeType.mk : TypeAttr).val then
        throw "Expected the `valueType` operand to be of type '!pdl.type'"
  | .type =>
    /- The optional `constantType` is a property, so `pdl.type` takes no
       operands. -/
    op.verifyPlainOpCounts ctx opIn 0 1
    op.verifyResultTypeMatches ctx (PDL.TypeType.mk : TypeAttr)
      "Expected the result to be of type '!pdl.type'"

end

end Veir
