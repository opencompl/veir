module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.Match.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
  The `match` dialect: an intermediate representation between `pdl` and
  `pdl_interp` that makes pattern navigation and the matcher-tree structure
  explicit in IR.

  This is the value-producing subset: the constant and navigation operations,
  all of which are `Pure`. The test operations (`match.has_name`,
  `match.equal`, ...) carry an implicit control effect -- on failure control
  transfers to the enclosing failure scope -- and the structural operations
  (`match.matcher`, `match.try`, the switches, `match.success`) need region and
  symbol-reference features VeIR does not have yet. Both groups follow.
-/
@[opcodes]
inductive Match where
| constant_attribute
| constant_type
| constant_types
| extract
| get_attribute
| get_attribute_type
| get_defining_op
| get_each
| get_operand
| get_operands
| get_result
| get_results
| get_users
| get_value_type
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Match.propertiesOf (op : Match) : Type :=
match op with
| .constant_attribute => MatchConstantAttributeProperties
| .constant_type => MatchConstantTypeProperties
| .constant_types => MatchConstantTypesProperties
| .extract => MatchIndexProperties
| .get_attribute => MatchGetAttributeProperties
| .get_attribute_type => Unit
| .get_defining_op => Unit
| .get_each => Unit
| .get_operand => MatchIndexProperties
| .get_operands => MatchOptionalIndexProperties
| .get_result => MatchIndexProperties
| .get_results => MatchOptionalIndexProperties
| .get_users => Unit
| .get_value_type => Unit

/-- Reject any property on an operation that carries none. -/
private def noProperties (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Unit :=
  if attrDict.size > 0 then
    let plural := if attrDict.size = 1 then "property" else "properties"
    .error s!"{opName}: expected no properties, but got {attrDict.size} {plural}"
  else
    .ok ()

def Match.fromAttrDict
    (op : Match) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Match.propertiesOf op) :=
  match op with
  | .constant_attribute => MatchConstantAttributeProperties.fromAttrDict attrDict
  | .constant_type => MatchConstantTypeProperties.fromAttrDict attrDict
  | .constant_types => MatchConstantTypesProperties.fromAttrDict attrDict
  | .extract => MatchIndexProperties.fromAttrDict "match.extract" attrDict
  | .get_attribute => MatchGetAttributeProperties.fromAttrDict attrDict
  | .get_attribute_type => noProperties "match.get_attribute_type" attrDict
  | .get_defining_op => noProperties "match.get_defining_op" attrDict
  | .get_each => noProperties "match.get_each" attrDict
  | .get_operand => MatchIndexProperties.fromAttrDict "match.get_operand" attrDict
  | .get_operands => MatchOptionalIndexProperties.fromAttrDict "match.get_operands" attrDict
  | .get_result => MatchIndexProperties.fromAttrDict "match.get_result" attrDict
  | .get_results => MatchOptionalIndexProperties.fromAttrDict "match.get_results" attrDict
  | .get_users => noProperties "match.get_users" attrDict
  | .get_value_type => noProperties "match.get_value_type" attrDict

def Match.toAttrDict
    (op : Match) (props : Match.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant_attribute =>
    (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 props.value
  | .constant_type =>
    (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 props.value
  | .constant_types =>
    (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 (.arrayAttr props.value)
  | .extract | .get_operand | .get_result =>
    (Std.HashMap.emptyWithCapacity 1).insert "index".toUTF8 (.integerAttr props.index)
  | .get_attribute =>
    (Std.HashMap.emptyWithCapacity 1).insert "name".toUTF8 (.stringAttr props.name)
  | .get_operands | .get_results =>
    match props.index with
    | some index => (Std.HashMap.emptyWithCapacity 1).insert "index".toUTF8 (.integerAttr index)
    | none => Std.HashMap.emptyWithCapacity 0
  | .get_attribute_type | .get_defining_op | .get_each | .get_users | .get_value_type =>
    Std.HashMap.emptyWithCapacity 0

/-- Every operation in this subset is `Pure`, exactly as MLIR marks them. -/
def Match.hasSideEffects (_op : Match) (_props : Match.propertiesOf _op) : Bool :=
  false

def Match.readsMemory (_op : Match) (_props : Match.propertiesOf _op) : Bool :=
  false

def Match.writesMemory (_op : Match) (_props : Match.propertiesOf _op) : Bool :=
  false

def Match.isConstantLike (_op : Match) : Bool :=
  false

def Match.hasSSADominance (_op : Match) (_index : Nat) : Bool :=
  true

def Match.hasNoTerminator (_op : Match) (_index : Nat) : Bool :=
  false

#generate_dialect Match

instance : HasDialectOpInfo Match where
  fromName := Match.fromName
  name := Match.name
  propertiesOf := Match.propertiesOf
  fromAttrDict := Match.fromAttrDict
  toAttrDict := Match.toAttrDict
  hasSideEffects := Match.hasSideEffects
  readsMemory := Match.readsMemory
  writesMemory := Match.writesMemory
  isConstantLike := Match.isConstantLike
  hasSSADominance := Match.hasSSADominance
  hasNoTerminator := Match.hasNoTerminator

/-- The element kind of a `!pdl.range<...>`, or `none` for any other type. -/
private def rangeElement? (ty : Attribute) : Option PDL.RangeElement :=
  match ty with
  | .pdlRangeType rangeType => some rangeType.element
  | _ => none

/-- The type wrapped by a `!match.optional<...>`, or `none` for any other type. -/
private def optionalInner? (ty : Attribute) : Option Attribute :=
  match ty with
  | .matchOptionalType optionalType => some optionalType.innerType
  | _ => none

/--
Verify the local invariants of a `match` operation in any operation-info type
containing the `match` dialect.

Navigation that can fail returns `!match.optional<...>`; the wrapped type is
checked here, which is the narrowing MLIR does in its type verifier and the
type itself deliberately does not.
-/
def Match.verifyLocalInvariants {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo Match]
    (opType : Match) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let operandType (i : Nat) : Attribute := ((op.getOperand! ctx.raw i).getType! ctx.raw).val
  let resultType : Attribute := ((op.getResult 0).get! ctx.raw).type.val
  /- The wrapped type of a nullable navigation result. -/
  let expectOptionalOf (expected : TypeAttr) (what : String) : Except String PUnit := do
    let some inner := optionalInner? resultType
      | throw s!"Expected the result to be of type '!match.optional<{what}>'"
    if inner ≠ expected.val then
      throw s!"Expected the result to be of type '!match.optional<{what}>'"
  match opType with
  | .constant_attribute =>
    op.verifyPlainOpCounts ctx opIn 0 1
    op.verifyResultTypeMatches ctx (PDL.AttributeType.mk : TypeAttr)
      "Expected the result to be of type '!pdl.attribute'"
  | .constant_type =>
    op.verifyPlainOpCounts ctx opIn 0 1
    op.verifyResultTypeMatches ctx (PDL.TypeType.mk : TypeAttr)
      "Expected the result to be of type '!pdl.type'"
  | .constant_types =>
    op.verifyPlainOpCounts ctx opIn 0 1
    op.verifyResultTypeMatches ctx (PDL.RangeType.mk .type : TypeAttr)
      "Expected the result to be of type '!pdl.range<type>'"
  | .get_operand | .get_result =>
    op.verifyPlainOpCounts ctx opIn 1 1
    if operandType 0 ≠ (PDL.OperationType.mk : TypeAttr).val then
      throw "Expected the operand to be of type '!pdl.operation'"
    expectOptionalOf (PDL.ValueType.mk : TypeAttr) "!pdl.value"
  | .get_operands | .get_results =>
    op.verifyPlainOpCounts ctx opIn 1 1
    if operandType 0 ≠ (PDL.OperationType.mk : TypeAttr).val then
      throw "Expected the operand to be of type '!pdl.operation'"
    expectOptionalOf (PDL.RangeType.mk .value : TypeAttr) "!pdl.range<value>"
  | .get_attribute =>
    op.verifyPlainOpCounts ctx opIn 1 1
    if operandType 0 ≠ (PDL.OperationType.mk : TypeAttr).val then
      throw "Expected the operand to be of type '!pdl.operation'"
    expectOptionalOf (PDL.AttributeType.mk : TypeAttr) "!pdl.attribute"
  | .get_defining_op =>
    op.verifyPlainOpCounts ctx opIn 1 1
    /- A value or a range of values: the defining op of the first is used. -/
    if operandType 0 ≠ (PDL.ValueType.mk : TypeAttr).val
        && rangeElement? (operandType 0) ≠ some .value then
      throw "Expected the operand to be of type '!pdl.value' or '!pdl.range<value>'"
    expectOptionalOf (PDL.OperationType.mk : TypeAttr) "!pdl.operation"
  | .get_value_type =>
    op.verifyPlainOpCounts ctx opIn 1 1
    /- Never fails, so the result is a bare handle; a range in gives a range
       out. -/
    if operandType 0 = (PDL.ValueType.mk : TypeAttr).val then
      if resultType ≠ (PDL.TypeType.mk : TypeAttr).val then
        throw "Expected the result to be of type '!pdl.type'"
    else if rangeElement? (operandType 0) = some .value then
      if rangeElement? resultType ≠ some .type then
        throw "Expected the result to be of type '!pdl.range<type>'"
    else
      throw "Expected the operand to be of type '!pdl.value' or '!pdl.range<value>'"
  | .get_attribute_type =>
    op.verifyPlainOpCounts ctx opIn 1 1
    if operandType 0 ≠ (PDL.AttributeType.mk : TypeAttr).val then
      throw "Expected the operand to be of type '!pdl.attribute'"
    op.verifyResultTypeMatches ctx (PDL.TypeType.mk : TypeAttr)
      "Expected the result to be of type '!pdl.type'"
  | .get_users =>
    op.verifyPlainOpCounts ctx opIn 1 1
    if operandType 0 ≠ (PDL.ValueType.mk : TypeAttr).val then
      throw "Expected the operand to be of type '!pdl.value'"
    op.verifyResultTypeMatches ctx (PDL.RangeType.mk .operation : TypeAttr)
      "Expected the result to be of type '!pdl.range<operation>'"
  | .extract =>
    op.verifyPlainOpCounts ctx opIn 1 1
    /- The result is one element of the range, so their element kinds agree. -/
    let some element := rangeElement? (operandType 0)
      | throw "Expected the operand to be of type '!pdl.range<...>'"
    let expected : TypeAttr := match element with
      | .attribute => PDL.AttributeType.mk
      | .operation => PDL.OperationType.mk
      | .type => PDL.TypeType.mk
      | .value => PDL.ValueType.mk
    if resultType ≠ expected.val then
      throw s!"Expected the result to have the element type of the range, '!pdl.{element}'"
  | .get_each =>
    op.verifyPlainOpCounts ctx opIn 1 1
    let some element := rangeElement? (operandType 0)
      | throw "Expected the operand to be of type '!pdl.range<...>'"
    let expected : TypeAttr := match element with
      | .attribute => PDL.AttributeType.mk
      | .operation => PDL.OperationType.mk
      | .type => PDL.TypeType.mk
      | .value => PDL.ValueType.mk
    if resultType ≠ expected.val then
      throw s!"Expected the result to have the element type of the range, '!pdl.{element}'"

end

end Veir
