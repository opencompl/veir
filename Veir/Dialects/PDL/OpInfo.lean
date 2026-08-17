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
| erase
| operand
| operands
| operation
| pattern
| range
| replace
| result
| results
| rewrite
| type
| types
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def PDL.propertiesOf (op : PDL) : Type :=
match op with
| .attribute => PDLAttributeProperties
| .erase => Unit
| .operand => Unit
| .operands => Unit
| .operation => PDLOperationProperties
| .pattern => PDLPatternProperties
| .range => Unit
| .replace => PDLReplaceProperties
| .result => PDLResultProperties
| .results => PDLResultsProperties
| .rewrite => PDLRewriteProperties
| .type => PDLTypeProperties
| .types => PDLTypesProperties

/-- Reject any property on an operation that carries none. -/
private def noProperties (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Unit :=
  if attrDict.size > 0 then
    let plural := if attrDict.size = 1 then "property" else "properties"
    .error s!"{opName}: expected no properties, but got {attrDict.size} {plural}"
  else
    .ok ()

def PDL.fromAttrDict
    (op : PDL) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (PDL.propertiesOf op) :=
  match op with
  | .attribute => PDLAttributeProperties.fromAttrDict attrDict
  | .erase => noProperties "pdl.erase" attrDict
  | .operand => noProperties "pdl.operand" attrDict
  | .operands => noProperties "pdl.operands" attrDict
  | .operation => PDLOperationProperties.fromAttrDict attrDict
  | .pattern => PDLPatternProperties.fromAttrDict attrDict
  | .range => noProperties "pdl.range" attrDict
  | .replace => PDLReplaceProperties.fromAttrDict attrDict
  | .result => PDLResultProperties.fromAttrDict attrDict
  | .results => PDLResultsProperties.fromAttrDict attrDict
  | .rewrite => PDLRewriteProperties.fromAttrDict attrDict
  | .type => PDLTypeProperties.fromAttrDict attrDict
  | .types => PDLTypesProperties.fromAttrDict attrDict

def PDL.toAttrDict
    (op : PDL) (props : PDL.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .attribute =>
    match props.value with
    | some value => (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 value
    | none => Std.HashMap.emptyWithCapacity 0
  | .erase => Std.HashMap.emptyWithCapacity 0
  | .operand => Std.HashMap.emptyWithCapacity 0
  | .operands => Std.HashMap.emptyWithCapacity 0
  | .range => Std.HashMap.emptyWithCapacity 0
  | .replace =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "operandSegmentSizes".toUTF8 (.denseArrayAttr props.operandSegmentSizes)
  | .operation => Id.run do
    let mut dict : Std.HashMap ByteArray Attribute := Std.HashMap.emptyWithCapacity 3
    if let some opName := props.opName then
      dict := dict.insert "opName".toUTF8 (.stringAttr opName)
    dict := dict.insert "attributeValueNames".toUTF8 (.arrayAttr props.attributeValueNames)
    dict := dict.insert "operandSegmentSizes".toUTF8 (.denseArrayAttr props.operandSegmentSizes)
    dict
  | .pattern => Id.run do
    let mut dict : Std.HashMap ByteArray Attribute := Std.HashMap.emptyWithCapacity 2
    dict := dict.insert "benefit".toUTF8 (.integerAttr props.benefit)
    if let some symName := props.sym_name then
      dict := dict.insert "sym_name".toUTF8 (.stringAttr symName)
    dict
  | .result =>
    (Std.HashMap.emptyWithCapacity 1).insert "index".toUTF8 (.integerAttr props.index)
  | .results =>
    match props.index with
    | some index => (Std.HashMap.emptyWithCapacity 1).insert "index".toUTF8 (.integerAttr index)
    | none => Std.HashMap.emptyWithCapacity 0
  | .rewrite => Id.run do
    let mut dict : Std.HashMap ByteArray Attribute := Std.HashMap.emptyWithCapacity 2
    if let some name := props.name then
      dict := dict.insert "name".toUTF8 (.stringAttr name)
    dict.insert "operandSegmentSizes".toUTF8 (.denseArrayAttr props.operandSegmentSizes)
  | .type =>
    match props.constantType with
    | some constantType =>
      (Std.HashMap.emptyWithCapacity 1).insert "constantType".toUTF8 constantType
    | none => Std.HashMap.emptyWithCapacity 0
  | .types =>
    match props.constantTypes with
    | some constantTypes =>
      (Std.HashMap.emptyWithCapacity 1).insert "constantTypes".toUTF8 (.arrayAttr constantTypes)
    | none => Std.HashMap.emptyWithCapacity 0

/-- MLIR marks only `pdl.range`, `pdl.result` and `pdl.results` `Pure`. The rest
    describe or perform rewrite actions, so treating them as side-effect free
    lets dead-code elimination delete a pattern body. -/
def PDL.hasSideEffects (op : PDL) (_props : PDL.propertiesOf op) : Bool :=
  match op with
  | .range | .result | .results => false
  | _ => true

def PDL.getEffects
    (_op : PDL) (_props : PDL.propertiesOf _op) : MemoryEffects :=
  .none

def PDL.isConstantLike (_op : PDL) : Bool :=
  false

def PDL.hasSSADominance (_op : PDL) (_index : Nat) : Bool :=
  true

/-- MLIR marks the body of a `pdl.rewrite` `NoTerminator`; it is an ordinary
    SSACFG region otherwise. -/
def PDL.hasNoTerminator (op : PDL) (_index : Nat) : Bool :=
  match op with
  | .rewrite => true
  | _ => false

/-- MLIR marks `pdl.rewrite` itself a `Terminator`: it is the last operation of
    the `pdl.pattern` body it lives in. -/
def PDL.isTerminator (op : PDL) : Bool :=
  match op with
  | .rewrite => true
  | _ => false

#generate_dialect PDL

instance : HasOpInfo PDL where
  fromName := PDL.fromName
  name := PDL.name
  propertiesOf := PDL.propertiesOf
  fromAttrDict := PDL.fromAttrDict
  toAttrDict := PDL.toAttrDict
  hasSideEffects := PDL.hasSideEffects
  getEffects := PDL.getEffects
  isConstantLike := PDL.isConstantLike
  hasSSADominance := PDL.hasSSADominance
  hasNoTerminator := PDL.hasNoTerminator
  isTerminator := PDL.isTerminator

/--
  The element kind of a PDL handle type, treating a non-range handle as a range
  of itself. Mirrors MLIR's `getRangeElementTypeOrSelf`.
-/
private def pdlElementOrSelf (ty : Attribute) : Option PDL.RangeElement :=
  match ty with
  | .pdlRangeType rangeType => some rangeType.element
  | .pdlAttributeType _ => some .attribute
  | .pdlOperationType _ => some .operation
  | .pdlTypeType _ => some .type
  | .pdlValueType _ => some .value
  | _ => none

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
  | .erase =>
    op.verifyPlainOpCounts ctx opIn 1 0
    /- A `pdl.erase` only appears inside the body of a `pdl.rewrite`. -/
    match op.getParentOp! ctx.raw with
    | some parent =>
      if toDialect? PDL (parent.getOpType! ctx.raw) ≠ some PDL.rewrite then
        throw "Expected the parent operation to be a `pdl.rewrite`"
    | none => throw "Expected the parent operation to be a `pdl.rewrite`"
    if ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
        ≠ (PDL.OperationType.mk : TypeAttr).val then
      throw "Expected the `opValue` operand to be of type '!pdl.operation'"
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
  | .operands =>
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyResultTypeMatches ctx (PDL.RangeType.mk .value : TypeAttr)
      "Expected the result to be of type '!pdl.range<value>'"
    /- The `valueType` operand is optional. -/
    let numOperands := op.getNumOperands ctx.raw opIn
    if numOperands > 1 then
      throw "Expected at most 1 operand"
    if numOperands = 1 then
      if ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
          ≠ (PDL.RangeType.mk .type : TypeAttr).val then
        throw "Expected the `valueType` operand to be of type '!pdl.range<type>'"
  | .operation =>
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyResultTypeMatches ctx (PDL.OperationType.mk : TypeAttr)
      "Expected the result to be of type '!pdl.operation'"
    let props : PDL.propertiesOf .operation :=
      HasDialect.toDialectProperties (OpInfo := OpInfo) PDL.operation
        (op.getProperties! ctx.raw (ofDialect OpInfo PDL.operation))
    /- The operands are the `operandValues`, `attributeValues` and `typeValues`
       groups, laid out consecutively in that order. -/
    let segments ← op.verifyOperandSegmentSizes ctx opIn props.operandSegmentSizes 3
    let valueCount := segments[0]!
    let attributeCount := segments[1]!
    let typeCount := segments[2]!
    /- Every attribute operand is named positionally by `attributeValueNames`. -/
    let nameCount := props.attributeValueNames.value.size
    if nameCount ≠ attributeCount then
      throw s!"Expected the same number of attribute values and attribute names, got {attributeCount} values and {nameCount} names"
    /- The value and type groups take single handles or ranges of them. -/
    for i in [0:valueCount] do
      if pdlElementOrSelf ((op.getOperand! ctx.raw i).getType! ctx.raw).val ≠ some .value then
        throw s!"Expected operand {i} to be of type '!pdl.value' or '!pdl.range<value>'"
    for i in [valueCount:valueCount + attributeCount] do
      if ((op.getOperand! ctx.raw i).getType! ctx.raw).val ≠ (PDL.AttributeType.mk : TypeAttr).val then
        throw s!"Expected operand {i} to be of type '!pdl.attribute'"
    for i in [valueCount + attributeCount:valueCount + attributeCount + typeCount] do
      if pdlElementOrSelf ((op.getOperand! ctx.raw i).getType! ctx.raw).val ≠ some .type then
        throw s!"Expected operand {i} to be of type '!pdl.type' or '!pdl.range<type>'"
  | .pattern =>
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    let props : PDL.propertiesOf .pattern :=
      HasDialect.toDialectProperties (OpInfo := OpInfo) PDL.pattern
        (op.getProperties! ctx.raw (ofDialect OpInfo PDL.pattern))
    /- MLIR confines `benefit` to a non-negative 16-bit attribute. -/
    if props.benefit.type.bitwidth ≠ 16 then
      throw "Expected 'benefit' to be a 16-bit signless integer attribute"
    if props.benefit.value < 0 then
      throw s!"Expected 'benefit' to be non-negative, but got {props.benefit.value}"
    /- The matcher body is a single block terminated by a `pdl.rewrite`. -/
    let body := (op.getRegion! ctx.raw 0).get! ctx.raw
    let some bodyBlock := body.firstBlock
      | throw "Expected the body to contain exactly 1 block"
    if body.lastBlock ≠ some bodyBlock then
      throw "Expected the body to contain exactly 1 block"
    let some terminator := (bodyBlock.get! ctx.raw).lastOp
      | throw "Expected the body to terminate with a `pdl.rewrite`"
    if toDialect? PDL (terminator.getOpType! ctx.raw) ≠ some PDL.rewrite then
      throw "Expected the body to terminate with a `pdl.rewrite`"
  | .range =>
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    /- A `pdl.range` only appears inside the body of a `pdl.rewrite`. -/
    match op.getParentOp! ctx.raw with
    | some parent =>
      if toDialect? PDL (parent.getOpType! ctx.raw) ≠ some PDL.rewrite then
        throw "Expected the parent operation to be a `pdl.rewrite`"
    | none => throw "Expected the parent operation to be a `pdl.rewrite`"
    let .pdlRangeType resultRange := ((op.getResult 0).get! ctx.raw).type.val
      | throw "Expected the result to be of type '!pdl.range<...>'"
    /- MLIR builds ranges of types and values only. -/
    match resultRange.element with
    | .type | .value => pure ()
    | _ => throw "Expected the result to be a range of '!pdl.type' or '!pdl.value'"
    /- Every argument contributes elements of the result's element kind, either
       one at a time or as a range. -/
    for i in [0 : op.getNumOperands ctx.raw opIn] do
      let operandType := ((op.getOperand! ctx.raw i).getType! ctx.raw).val
      if pdlElementOrSelf operandType ≠ some resultRange.element then
        throw s!"Expected operand {i} to have element type '!pdl.{resultRange.element}'"
  | .replace =>
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    /- A `pdl.replace` only appears inside the body of a `pdl.rewrite`. -/
    match op.getParentOp! ctx.raw with
    | some parent =>
      if toDialect? PDL (parent.getOpType! ctx.raw) ≠ some PDL.rewrite then
        throw "Expected the parent operation to be a `pdl.rewrite`"
    | none => throw "Expected the parent operation to be a `pdl.rewrite`"
    let props : PDL.propertiesOf .replace :=
      HasDialect.toDialectProperties (OpInfo := OpInfo) PDL.replace
        (op.getProperties! ctx.raw (ofDialect OpInfo PDL.replace))
    /- The operands are the replaced `opValue`, the optional `replOperation`,
       and the `replValues`, in that order. -/
    let segments ← op.verifyOperandSegmentSizes ctx opIn props.operandSegmentSizes 3
    let replOperationCount := segments[1]!
    let replValueCount := segments[2]!
    if segments[0]! ≠ 1 then
      throw "Expected exactly 1 replaced operation"
    if replOperationCount > 1 then
      throw "Expected at most 1 replacement operation"
    if ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
        ≠ (PDL.OperationType.mk : TypeAttr).val then
      throw "Expected the `opValue` operand to be of type '!pdl.operation'"
    if replOperationCount = 1 then
      if ((op.getOperand! ctx.raw 1).getType! ctx.raw).val
          ≠ (PDL.OperationType.mk : TypeAttr).val then
        throw "Expected the `replOperation` operand to be of type '!pdl.operation'"
    /- TODO: `!pdl.range<...>` is not modelled yet, so `replValues` accepts
       single handles only. -/
    for i in [1 + replOperationCount : 1 + replOperationCount + replValueCount] do
      if ((op.getOperand! ctx.raw i).getType! ctx.raw).val
          ≠ (PDL.ValueType.mk : TypeAttr).val then
        throw s!"Expected operand {i} to be of type '!pdl.value'"
    /- The replacement is either an operation or a list of values, never both. -/
    if replOperationCount = 1 && replValueCount ≠ 0 then
      throw "Expected no replacement values when the replacement operation is present"
  | .result =>
    op.verifyPlainOpCounts ctx opIn 1 1
    op.verifyResultTypeMatches ctx (PDL.ValueType.mk : TypeAttr)
      "Expected the result to be of type '!pdl.value'"
    if ((op.getOperand! ctx.raw 0).getType! ctx.raw).val ≠ (PDL.OperationType.mk : TypeAttr).val then
      throw "Expected the `parent` operand to be of type '!pdl.operation'"
    let props : PDL.propertiesOf .result :=
      HasDialect.toDialectProperties (OpInfo := OpInfo) PDL.result
        (op.getProperties! ctx.raw (ofDialect OpInfo PDL.result))
    /- MLIR constrains `index` to a 32-bit signless integer attribute and
       nothing more: it range-checks neither the sign nor the parent's result
       count, so neither does this. -/
    if props.index.type.bitwidth ≠ 32 then
      throw "Expected 'index' to be a 32-bit signless integer attribute"
  | .rewrite =>
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    /- A `pdl.rewrite` only ever terminates the body of a `pdl.pattern`. -/
    match op.getParentOp! ctx.raw with
    | some parent =>
      if toDialect? PDL (parent.getOpType! ctx.raw) ≠ some PDL.pattern then
        throw "Expected the parent operation to be a `pdl.pattern`"
    | none => throw "Expected the parent operation to be a `pdl.pattern`"
    let props : PDL.propertiesOf .rewrite :=
      HasDialect.toDialectProperties (OpInfo := OpInfo) PDL.rewrite
        (op.getProperties! ctx.raw (ofDialect OpInfo PDL.rewrite))
    /- The operands are the optional `root` followed by the `externalArgs`. -/
    let segments ← op.verifyOperandSegmentSizes ctx opIn props.operandSegmentSizes 2
    let rootCount := segments[0]!
    if rootCount > 1 then
      throw "Expected at most 1 `root` operand"
    if rootCount = 1 then
      if ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
          ≠ (PDL.OperationType.mk : TypeAttr).val then
        throw "Expected the `root` operand to be of type '!pdl.operation'"
    /- An external rewrite names a native function and leaves its region empty;
       an inline rewrite supplies a body and takes no external arguments. -/
    let body := (op.getRegion! ctx.raw 0).get! ctx.raw
    /- MLIR gives `pdl.rewrite` `SingleBlock`, so the body holds no more than
       one block. -/
    if body.firstBlock ≠ body.lastBlock then
      throw "Expected the rewrite region to contain at most 1 block"
    if props.name.isSome then
      if body.firstBlock.isSome then
        throw "Expected the rewrite region to be empty when the rewrite is external"
    else
      if body.firstBlock.isNone then
        throw "Expected the rewrite region to be non-empty when no external name is specified"
      if segments[1]! ≠ 0 then
        throw "Expected no external arguments when the rewrite is specified inline"
  | .results =>
    op.verifyPlainOpCounts ctx opIn 1 1
    if ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
        ≠ (PDL.OperationType.mk : TypeAttr).val then
      throw "Expected the `parent` operand to be of type '!pdl.operation'"
    let props : PDL.propertiesOf .results :=
      HasDialect.toDialectProperties (OpInfo := OpInfo) PDL.results
        (op.getProperties! ctx.raw (ofDialect OpInfo PDL.results))
    let resultType := ((op.getResult 0).get! ctx.raw).type.val
    /- A single result group is one value; the whole result range is a range. -/
    match resultType with
    | .pdlValueType _ =>
      if props.index.isNone then
        throw "Expected a '!pdl.range<value>' result type when no index is specified"
    | .pdlRangeType rangeType =>
      if rangeType.element ≠ .value then
        throw "Expected the result to be of type '!pdl.value' or '!pdl.range<value>'"
    | _ => throw "Expected the result to be of type '!pdl.value' or '!pdl.range<value>'"
  | .type =>
    /- The optional `constantType` is a property, so `pdl.type` takes no
       operands. -/
    op.verifyPlainOpCounts ctx opIn 0 1
    op.verifyResultTypeMatches ctx (PDL.TypeType.mk : TypeAttr)
      "Expected the result to be of type '!pdl.type'"
  | .types =>
    /- The optional `constantTypes` is a property, so `pdl.types` takes no
       operands. -/
    op.verifyPlainOpCounts ctx opIn 0 1
    op.verifyResultTypeMatches ctx (PDL.RangeType.mk .type : TypeAttr)
      "Expected the result to be of type '!pdl.range<type>'"

end

end Veir
