module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `hw.constant` operation.
-/
structure HWConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def HWConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String HWConstantProperties := do
  if attrDict.size > 1 then
    throw s!"hw.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "hw.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"hw.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of `hw.module`.
-/
structure HWModuleProperties where
  module_type : HW.ModuleType
  sym_name : StringAttr
  per_port_attrs : ArrayAttr
  parameters : ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

structure HWInstanceProperties where
  instanceName : StringAttr
  moduleName : FlatSymbolRefAttr
  argNames : ArrayAttr
  resultNames : ArrayAttr
  parameters : ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def HWModuleProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String HWModuleProperties := do
  let some module_type := attrDict["module_type".toUTF8]? | throw "hw.module: requires attribute 'module_type'"
  let .hwModuleType module_type := module_type | throw s!"hw.module: expected 'module_type' to be `!hw.modty`, but got {module_type}"

  let some sym_name := attrDict["sym_name".toUTF8]? | throw "hw.module: requires attribute 'sym_name'"
  let .stringAttr sym_name := sym_name | throw s!"hw.module: expected 'sym_name' to be a string attribute, but got {sym_name}"

  let per_port_attrs := attrDict["per_port_attrs".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr per_port_attrs := per_port_attrs | throw s!"hw.module: expected 'per_port_attrs' to be an array attribute, but got {per_port_attrs}"

  let parameters := attrDict["parameters".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr parameters := parameters | throw s!"hw.module: expected 'parameters' to be an array attribute, but got {parameters}"

  return { module_type, sym_name, per_port_attrs, parameters }

def HWInstanceProperties.fromAttrDict
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String HWInstanceProperties := do
  let some instanceName := attrDict["instanceName".toUTF8]? | throw "hw.instance: requires attribute 'instanceName'"
  let .stringAttr instanceName := instanceName | throw s!"hw.instance: expected 'instanceName' to be a string attribute, but got {instanceName}"

  let some moduleName := attrDict["moduleName".toUTF8]? | throw "hw.instance: requires attribute 'moduleName'"
  let .flatSymbolRefAttr moduleName := moduleName | throw s!"hw.instance: expected 'moduleName' to be a flat symbol reference attribute, but got {moduleName}"

  let some argNames := attrDict["argNames".toUTF8]? | throw "hw.instance: requires attribute 'argNames'"
  let .arrayAttr argNames := argNames | throw s!"hw.instance: expected 'argNames' to be an array attribute, but got {argNames}"

  let some resultNames := attrDict["resultNames".toUTF8]? | throw "hw.instance: requires attribute 'resultNames'"
  let .arrayAttr resultNames := resultNames | throw s!"hw.instance: expected 'resultNames' to be an array attribute, but got {resultNames}"

  let some parameters := attrDict["parameters".toUTF8]? | throw "hw.instance: requires attribute 'parameters'"
  let .arrayAttr parameters := parameters | throw s!"hw.instance: expected 'parameters' to be an array attribute, but got {parameters}"

  return { instanceName, moduleName, argNames, resultNames, parameters }

end

end Veir
