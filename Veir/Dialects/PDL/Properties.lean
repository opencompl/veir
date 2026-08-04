module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `pdl.attribute` operation.

  `value` is the optional constant value the attribute is constrained to. It is
  absent when the attribute is unconstrained or only constrained by the
  `valueType` operand, so it is modelled as an `Option` and omitted again when
  printing.
-/
structure PDLAttributeProperties where
  value : Option Attribute
deriving Inhabited, Repr, Hashable, DecidableEq

def PDLAttributeProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String PDLAttributeProperties := do
  let value := attrDict["value".toUTF8]?
  if attrDict.size > (if value.isSome then 1 else 0) then
    throw s!"pdl.attribute: expected only the 'value' property, but got {attrDict.size} properties"
  return { value := value }

/--
  Properties of the `pdl.type` operation.

  `constantType` is the optional constant type the handle is constrained to. It
  is absent when the type is unconstrained, so it is modelled as an `Option` and
  omitted again when printing.
-/
structure PDLTypeProperties where
  constantType : Option TypeAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def PDLTypeProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String PDLTypeProperties := do
  let constantType ← match attrDict["constantType".toUTF8]? with
    | some attr =>
      if _ : attr.isType = false then
        throw s!"pdl.type: expected 'constantType' to be a type attribute, but got {attr}"
      else pure (some attr.asType)
    | none => pure none
  if attrDict.size > (if constantType.isSome then 1 else 0) then
    throw s!"pdl.type: expected only the 'constantType' property, but got {attrDict.size} properties"
  return { constantType := constantType }

/--
  Properties of the `pdl.operation` operation.

  `opName` is the optional name of the operation being matched or created; it is
  absent when the pattern matches an operation of any name.

  `attributeValueNames` names the `attributeValues` operands positionally, so it
  holds one string attribute per attribute operand.

  `operandSegmentSizes` splits the operands into the `operandValues`,
  `attributeValues`, and `typeValues` groups, in that order.
-/
structure PDLOperationProperties where
  opName : Option StringAttr
  attributeValueNames : ArrayAttr
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def PDLOperationProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String PDLOperationProperties := do
  let opName ← match attrDict["opName".toUTF8]? with
    | some (.stringAttr attr) => pure (some attr)
    | some attr =>
      throw s!"pdl.operation: expected 'opName' to be a string attribute, but got {attr}"
    | none => pure none
  let some namesAttr := attrDict["attributeValueNames".toUTF8]?
    | throw "pdl.operation: missing 'attributeValueNames' property"
  let .arrayAttr attributeValueNames := namesAttr
    | throw s!"pdl.operation: expected 'attributeValueNames' to be an array attribute, but got {namesAttr}"
  for name in attributeValueNames.value do
    let .stringAttr _ := name
      | throw s!"pdl.operation: expected 'attributeValueNames' to hold string attributes, but got {name}"
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "pdl.operation: missing 'operandSegmentSizes' property"
  let .denseArrayAttr operandSegmentSizes := sizesAttr
    | throw s!"pdl.operation: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  if attrDict.size > (if opName.isSome then 3 else 2) then
    throw s!"pdl.operation: expected only the 'opName', 'attributeValueNames' and 'operandSegmentSizes' properties, but got {attrDict.size} properties"
  return { opName, attributeValueNames, operandSegmentSizes }

/--
  Properties of the `pdl.result` operation.

  `index` is the zero-based index of the result to extract from the `parent`
  operation handle. It counts concrete results, so it is not an index into the
  range of results of a variadic result group.
-/
structure PDLResultProperties where
  index : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def PDLResultProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String PDLResultProperties := do
  let some indexAttr := attrDict["index".toUTF8]?
    | throw "pdl.result: missing 'index' property"
  let .integerAttr index := indexAttr
    | throw s!"pdl.result: expected 'index' to be an integer attribute, but got {indexAttr}"
  if attrDict.size > 1 then
    throw s!"pdl.result: expected only the 'index' property, but got {attrDict.size} properties"
  return { index }

/--
  Properties of the `pdl.pattern` operation.

  `benefit` is the pattern's benefit, mirroring the benefit of the
  `RewritePattern` it stands for. MLIR constrains it to a non-negative 16-bit
  attribute.

  `sym_name` is optional: a pattern may, but need not, define a symbol.
-/
structure PDLPatternProperties where
  benefit : IntegerAttr
  sym_name : Option StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def PDLPatternProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String PDLPatternProperties := do
  let some benefitAttr := attrDict["benefit".toUTF8]?
    | throw "pdl.pattern: missing 'benefit' property"
  let .integerAttr benefit := benefitAttr
    | throw s!"pdl.pattern: expected 'benefit' to be an integer attribute, but got {benefitAttr}"
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr attr) => pure (some attr)
    | some attr =>
      throw s!"pdl.pattern: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => pure none
  if attrDict.size > (if symName.isSome then 2 else 1) then
    throw s!"pdl.pattern: expected only the 'benefit' and 'sym_name' properties, but got {attrDict.size} properties"
  return { benefit, sym_name := symName }

/--
  Properties of the `pdl.rewrite` operation.

  `name` names an external rewrite function. It is absent when the rewrite is
  given inline by the body region instead.

  `operandSegmentSizes` splits the operands into the optional `root` and the
  variadic `externalArgs` groups, in that order.
-/
structure PDLRewriteProperties where
  name : Option StringAttr
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def PDLRewriteProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String PDLRewriteProperties := do
  let name ← match attrDict["name".toUTF8]? with
    | some (.stringAttr attr) => pure (some attr)
    | some attr =>
      throw s!"pdl.rewrite: expected 'name' to be a string attribute, but got {attr}"
    | none => pure none
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "pdl.rewrite: missing 'operandSegmentSizes' property"
  let .denseArrayAttr operandSegmentSizes := sizesAttr
    | throw s!"pdl.rewrite: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  if attrDict.size > (if name.isSome then 2 else 1) then
    throw s!"pdl.rewrite: expected only the 'name' and 'operandSegmentSizes' properties, but got {attrDict.size} properties"
  return { name, operandSegmentSizes }

/--
  Properties of the `pdl.replace` operation.

  `operandSegmentSizes` splits the operands into the `opValue`, the optional
  `replOperation`, and the variadic `replValues` groups, in that order.
-/
structure PDLReplaceProperties where
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def PDLReplaceProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String PDLReplaceProperties := do
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "pdl.replace: missing 'operandSegmentSizes' property"
  let .denseArrayAttr operandSegmentSizes := sizesAttr
    | throw s!"pdl.replace: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  if attrDict.size > 1 then
    throw s!"pdl.replace: expected only the 'operandSegmentSizes' property, but got {attrDict.size} properties"
  return { operandSegmentSizes }

end

end Veir
