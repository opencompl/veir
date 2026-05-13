module

public import Veir.OpCode
public import Veir.IR.Attribute
public import Veir.IR.Simp
public import Veir.ForLean
public import Veir.IR.OpInfo

namespace Veir

public section

def getUnitAttr (key : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Bool := do
  match attrDict[key.toUTF8]? with
  | some (.unitAttr _) => .ok true
  | some attr => .error s!"expected '{key}' to be an optional unit attribute, but got {attr}"
  | none => .ok false

/--
  Properties of the `arith.constant` operation.
-/
structure ArithConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def ArithConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ArithConstantProperties := do
  if attrDict.size > 1 then
    throw s!"arith.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "arith.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"arith.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of operations that can have `nsw` and `nuw` flags, such as `arith.addi`, `arith.muli`,
  `llvm.add`, or `llvm.mul`.
-/
structure NswNuwProperties where
  nsw : Bool
  nuw : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def NswNuwProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String NswNuwProperties := do
  let nsw ← getUnitAttr "nsw" attrDict
  let nuw ← getUnitAttr "nuw" attrDict
  return { nsw := nsw, nuw := nuw }

/--
  Properties of operations that can have the `exact` flags, such as
  `llvm.udiv`, or `llvm.sdiv`.
-/
structure ExactProperties where
  exact : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def ExactProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ExactProperties := do
  let exact ← getUnitAttr "exact" attrDict
  return { exact := exact }

/--
  Properties of operations that can have the `disjoint` flags, such as
  `llvm.or`.
-/
structure DisjointProperties where
  disjoint : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def DisjointProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String DisjointProperties := do
  let disjoint ← getUnitAttr "disjoint" attrDict
  return { disjoint := disjoint }

/--
  Properties of operations that can have the `nneg` flag, such as `llvm.zext`.
-/
structure NnegProperties where
  nneg : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def NnegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String NnegProperties := do
  let nneg ← getUnitAttr "nneg" attrDict
  return { nneg := nneg }

/--
  Properties of the `llvm.constant` operation.
-/
structure LLVMConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMConstantProperties := do
  if attrDict.size > 1 then
    throw s!"llvm.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "llvm.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"llvm.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of `llvm.icmp` operation, describing predicates for integer comparison.
-/
structure IcmpProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def IcmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String IcmpProperties := do
  if attrDict.size > 1 then
    throw s!"llvm.icmp: expected only one property, but got {attrDict.size} properties"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "llvm.icmp: missing predicate"
  let .integerAttr intAttr := attr
    | throw s!"llvm.icmp: expected predicate to be a string attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of the RISC-V immediate operations.
-/
structure RISCVImmediateProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVImmediateProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVImmediateProperties := do
  if attrDict.size > 1 then
    throw s!"RISC-V immediate operation: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "RISC-V immediate operation: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"RISC-V immediate operation: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of the `mod_arith.constant` operation.
-/
structure ModArithConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def ModArithConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ModArithConstantProperties := do
  if attrDict.size > 1 then
    throw s!"mod_arith.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "mod_arith.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"mod_arith.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of the `cond_br` operation.
-/

structure CondBrProperties where
  branch_weights : DenseArrayAttr
  operandSegmentSizes : DenseArrayAttr

deriving Inhabited, Repr, Hashable, DecidableEq

def CondBrProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CondBrProperties := do
  if attrDict.size > 2 then
    throw s!"cf.cond_br: expected only 'branch_weights' and 'operandSegmentSizes' properties, but got {attrDict.size} properties"
  let weightsAttr ← match attrDict["weightsAttr".toUTF8]? with
    | some (.denseArrayAttr weightsAttr) => .ok weightsAttr
    | some attr => .error s!"expected 'branch_weights' to be an optional dense array attribute, but got {attr}"
    | none => .ok { elementType := { bitwidth := 32 }, values := #[] }
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "cf.cond_br: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizesAttr := sizesAttr
    | throw s!"cf.cond_br: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  return { branch_weights := weightsAttr, operandSegmentSizes := sizesAttr }

/--
  Properties of LLVM memory operations.
-/

structure AllocaProperties where
  alignment : IntegerAttr
  elem_type : TypeAttr
  inalloca : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def AllocaProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String AllocaProperties := do
  let alignAttr ← match attrDict["alignment".toUTF8]? with
    | some (.integerAttr alignAttr) => .ok alignAttr
    | some attr => .error s!"expected 'alignment' to be an optional integer attribute, but got {attr}"
    | none => .ok { value := 0, type := { bitwidth := 64 } }
  let some typeAttr := attrDict["elem_type".toUTF8]?
    | throw "alloca: missing 'elem_type' property"
  if _ : typeAttr.isType = false then throw "alloca: expected 'elem_type' to be a type attribute" else
  let inallocaAttr ← getUnitAttr "inalloca" attrDict
  return { alignment := alignAttr, elem_type := typeAttr.asType, inalloca := inallocaAttr }

structure LoadProperties where
  alignment : IntegerAttr
  volatile_ : Bool
  nontemporal : Bool
  invariant : Bool
  invariantGroup : Bool
  --ordering
  syncscope : Option StringAttr
  --dereferenceable
  access_groups : ArrayAttr
  alias_scopes : ArrayAttr
  noalias_scopes : ArrayAttr
  tbaa : ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LoadProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LoadProperties := do
  let alignAttr ← match attrDict["alignment".toUTF8]? with
  | some (.integerAttr alignAttr) => .ok alignAttr
  | some attr => .error s!"expected 'alignment' to be an optional integer attribute, but got {attr}"
  | none => .ok { value := 0, type := { bitwidth := 64 } }
  let volatileAttr ← getUnitAttr "volatile_" attrDict
  let nontemporalAttr ← getUnitAttr "nontemporal" attrDict
  let invariantAttr ← getUnitAttr "invariant" attrDict
  let invariantGroupAttr ← getUnitAttr "invariantGroup" attrDict
  let syncscopeAttr ← match attrDict["syncscope".toUTF8]? with
    | some (.stringAttr syncscopeAttr) => .ok (some syncscopeAttr)
    | some attr => .error s!"expected 'syncscope' to be an optional string attribute, but got {attr}"
    | none => .ok none
  let accessAttr := attrDict["access_groups".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr accessAttr := accessAttr
    | throw s!"store: expected 'access_groups' to be an array attribute, but got {accessAttr}"
  let aliasAttr := attrDict["alias_scopes".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr aliasAttr := aliasAttr
    | throw s!"store: expected 'alias_scopes' to be an array attribute, but got {aliasAttr}"
  let noaliasAttr := attrDict["noalias_scopes".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr noaliasAttr := noaliasAttr
    | throw s!"store: expected 'noalias_scopes' to be an array attribute, but got {noaliasAttr}"
  let tbaaAttr := attrDict["tbaa".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr tbaaAttr := tbaaAttr
    | throw s!"store: expected 'tbaa' to be an array attribute, but got {tbaaAttr}"
  return { alignment := alignAttr, volatile_ := volatileAttr, nontemporal := nontemporalAttr, invariant := invariantAttr, invariantGroup := invariantGroupAttr, syncscope := syncscopeAttr, access_groups := accessAttr, alias_scopes := aliasAttr, noalias_scopes := noaliasAttr, tbaa := tbaaAttr }

structure StoreProperties where
  alignment : IntegerAttr
  volatile_ : Bool
  nontemporal : Bool
  invariantGroup : Bool
  --ordering
  syncscope : Option StringAttr
  access_groups : ArrayAttr
  alias_scopes : ArrayAttr
  noalias_scopes : ArrayAttr
  tbaa : ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def StoreProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StoreProperties := do
  let alignAttr ← match attrDict["alignment".toUTF8]? with
  | some (.integerAttr alignAttr) => .ok alignAttr
  | some attr => .error s!"expected 'alignment' to be an optional integer attribute, but got {attr}"
  | none => .ok { value := 0, type := { bitwidth := 64 } }
  let volatileAttr ← getUnitAttr "volatile_" attrDict
  let nontemporalAttr ← getUnitAttr "nontemporal" attrDict
  let invariantGroupAttr ← getUnitAttr "invariantGroup" attrDict
  let syncscopeAttr ← match attrDict["syncscope".toUTF8]? with
    | some (.stringAttr syncscopeAttr) => .ok (some syncscopeAttr)
    | some attr => .error s!"expected 'syncscope' to be an optional string attribute, but got {attr}"
    | none => .ok none
  let accessAttr := attrDict["access_groups".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr accessAttr := accessAttr
    | throw s!"store: expected 'access_groups' to be an array attribute, but got {accessAttr}"
  let aliasAttr := attrDict["alias_scopes".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr aliasAttr := aliasAttr
    | throw s!"store: expected 'alias_scopes' to be an array attribute, but got {aliasAttr}"
  let noaliasAttr := attrDict["noalias_scopes".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr noaliasAttr := noaliasAttr
    | throw s!"store: expected 'noalias_scopes' to be an array attribute, but got {noaliasAttr}"
  let tbaaAttr := attrDict["tbaa".toUTF8]?.getD (.arrayAttr .empty)
  let .arrayAttr tbaaAttr := tbaaAttr
    | throw s!"store: expected 'tbaa' to be an array attribute, but got {tbaaAttr}"
  return { alignment := alignAttr, volatile_ := volatileAttr, nontemporal := nontemporalAttr, invariantGroup := invariantGroupAttr, syncscope := syncscopeAttr, access_groups := accessAttr, alias_scopes := aliasAttr, noalias_scopes := noaliasAttr, tbaa := tbaaAttr }

/--
  Properties of the `llvm.getelementptr` operation
-/
structure GetelementptrProperties where
  rawConstantIndices : DenseArrayAttr
  elem_type : TypeAttr
  noWrapFlags : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def GetelementptrProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GetelementptrProperties := do
  let noWrapFlags ← match attrDict["noWrapFlags".toUTF8]? with
    | some (.integerAttr noWrapFlag) => .ok noWrapFlag
    | some attr => .error s!"expected 'noWrapFlag' to be an optional integer attribute, but got {attr}"
    | none => .ok { value := 0, type := { bitwidth := 32 } }
  let rawConstantIndices ← match attrDict["rawConstantIndices".toUTF8]? with
    | some (.denseArrayAttr arr) => .ok arr
    | some attr => .error s!"getelementptr: expected 'rawConstantIndices' to be a dense array attribute, 
        but got {attr}"
    | none => .error "getelementptr: missing 'rawConstantIndices' property"
  let some typeAttr := attrDict["elem_type".toUTF8]?
    | throw "getelementptr: missing 'elem_type' property"
  if h : typeAttr.isType = false then
    throw "getelementptr: expected 'elem_type' to be a type attribute" else
  return {rawConstantIndices, elem_type := typeAttr.asType, noWrapFlags}

/--
  Properties of the `comb.extract` operation.
-/
structure CombExtractProperties where
  lowBit : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CombExtractProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CombExtractProperties := do
  if attrDict.size > 1 then
    throw s!"comb.extract: expected only one property, but got {attrDict.size} properties"
  let some attr := attrDict["lowBit".toUTF8]?
    | throw "comb.extract: missing 'lowBit' property"
  let .integerAttr intAttr := attr
    | throw s!"comb.extract: expected 'lowBit' to be an integer attribute, but got {attr}"
  return { lowBit := intAttr }

/--
  Properties of `comb.icmp` operation, describing predicates for integer comparison.
-/
structure CombIcmpProperties where
  predicate : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CombIcmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CombIcmpProperties := do
  if attrDict.size > 1 then
    throw s!"comb.icmp: expected only one property, but got {attrDict.size} properties"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "comb.icmp: missing 'predicate' property"
  let .integerAttr intAttr := attr
    | throw s!"comb.icmp: expected 'predicate' to be an integer attribute, but got {attr}"
  return { predicate := intAttr }

/--
  Properties of `hw.module`.
-/
structure HWModuleProperties where
  module_type : HW.ModuleType
  sym_name : StringAttr
  per_port_attrs : ArrayAttr
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

end
end Veir
