module

public import Veir.Data.LLVM.Int.Basic
public import Std.Data.HashMap
public import Veir.IR.Attribute

import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/-- Properties of LLVM operations that can have `nsw` and `nuw` flags, such as `llvm.add` or `llvm.mul`. -/
structure NswNuwProperties where
  nsw : Bool
  nuw : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def NswNuwProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String NswNuwProperties := do
  let value ← match attrDict["overflowFlags".toUTF8]? with
    | some (.integerAttr flags) =>
      if flags.type.bitwidth ≠ 32 then
        .error s!"expected 'overflowFlags' to be an integer attribute of bitwidth 32, but got i{flags.type.bitwidth}"
      else
        .ok flags.value
    | some attr => .error s!"expected 'overflowFlags' to be an optional integer attribute, but got {attr}"
    | none => .ok 0

  let nsw := (value.toNat &&& 1) ≠ 0
  let nuw := (value.toNat &&& 2) ≠ 0
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
  Properties of LLVM count-zero intrinsics. In LLVM IR, the second intrinsic
  argument is an immediate `i1` named `is_zero_poison`.
-/
structure ZeroPoisonProperties where
  is_zero_poison : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def ZeroPoisonProperties.fromAttrDictFor (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ZeroPoisonProperties := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only 'is_zero_poison' property, but got {attrDict.size} properties"
  let some attr := attrDict["is_zero_poison".toUTF8]?
    | throw s!"{opName}: missing 'is_zero_poison' property"
  let .integerAttr intAttr := attr
    | throw s!"{opName}: expected 'is_zero_poison' to be an i1 integer attribute, but got {attr}"
  if intAttr.type.bitwidth ≠ 1 then
    throw s!"{opName}: expected 'is_zero_poison' to be an i1 integer attribute, but got i{intAttr.type.bitwidth}"
  if intAttr.value = 0 then
    return { is_zero_poison := false }
  else if intAttr.value = 1 then
    return { is_zero_poison := true }
  else
    throw s!"{opName}: expected 'is_zero_poison' to be 0 or 1, but got {intAttr.value}"

def ZeroPoisonProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ZeroPoisonProperties :=
  ZeroPoisonProperties.fromAttrDictFor "llvm.intr.ctlz" attrDict

/--
  Properties of the `llvm.intr.abs` intrinsic. In LLVM IR, the second intrinsic
  argument is an immediate `i1` named `is_int_min_poison` indicating whether the
  result is poison when the operand is `INT_MIN`.
-/
structure IntMinPoisonProperties where
  is_int_min_poison : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def IntMinPoisonProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String IntMinPoisonProperties := do
  if attrDict.size > 1 then
    throw s!"llvm.intr.abs: expected only 'is_int_min_poison' property, but got {attrDict.size} properties"
  let some attr := attrDict["is_int_min_poison".toUTF8]?
    | throw "llvm.intr.abs: missing 'is_int_min_poison' property"
  let .integerAttr intAttr := attr
    | throw s!"llvm.intr.abs: expected 'is_int_min_poison' to be an i1 integer attribute, but got {attr}"
  if intAttr.type.bitwidth ≠ 1 then
    throw s!"llvm.intr.abs: expected 'is_int_min_poison' to be an i1 integer attribute, but got i{intAttr.type.bitwidth}"
  if intAttr.value = 0 then
    return { is_int_min_poison := false }
  else if intAttr.value = 1 then
    return { is_int_min_poison := true }
  else
    throw s!"llvm.intr.abs: expected 'is_int_min_poison' to be 0 or 1, but got {intAttr.value}"

structure FastMathFlagsProperties where
  attr : FastMathFlagsAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def FastMathFlagsProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FastMathFlagsProperties := do

  let value ← match attrDict["fastmathFlags".toUTF8]? with
    | none => .ok { nnan := false, ninf := false, nsz := false }
    | some (.fastMathFlagsAttr flags) => .ok flags
    | some (.unregisteredAttr attr) =>
        .error s!"expected 'fastmathFlags' to be a fast math flags attribute, but got unregistered {attr}"
    | some attr => .error s!"expected 'fastmathFlags' to be a float fast math flags attribute, but got {attr}"

  return ⟨value⟩

/--
The types of constants an LLVM constant can store.
-/
inductive LLVMConstantValue where
| integer (value : IntegerAttr)
| float (value : FloatAttr)
| dense (value : DenseElementsAttr)
deriving Inhabited, Repr, Hashable, DecidableEq

/--
  Properties of the `llvm.constant` operation.
-/
structure LLVMConstantProperties where
  value : LLVMConstantValue
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMConstantProperties := do
  if attrDict.size > 1 then
    throw s!"llvm.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "llvm.constant: missing 'value' property"
  match attr with
  | .integerAttr intAttr =>
    return { value := .integer intAttr }
  | .floatAttr floatAttr =>
    return { value := .float floatAttr }
  | .denseElementsAttr denseAttr =>
    return { value := .dense denseAttr }
  | _ =>
    throw s!"llvm.constant: expected 'value' to be an integer, float, or dense elements attribute, but got {attr}"

/--
  Properties of `llvm.mlir.global`. The properties needed to identify and lay
  out the global are modelled explicitly; less common LLVM global properties
  are preserved verbatim in `extra`.

  `alignment` is genuinely optional in MLIR (an absent alignment means "use the
  target's preferred alignment", which is not the same as any particular value),
  so it is modelled as an `Option` and omitted again when printing. `addr_space`
  instead has a default of `0 : i32`, which MLIR materializes on parse, so it is
  always present here.
-/
structure LLVMGlobalProperties where
  sym_name : StringAttr
  global_type : TypeAttr
  value : Option Attribute
  alignment : Option IntegerAttr
  addr_space : IntegerAttr
  linkage : LinkageAttr
  constant : Bool
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMGlobalProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMGlobalProperties := do
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr attr) => pure attr
    | some attr =>
      throw s!"llvm.mlir.global: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => throw "llvm.mlir.global: missing 'sym_name' property"
  let globalType ← match attrDict["global_type".toUTF8]? with
    | some attr =>
      if _ : attr.isType = false then
        throw "llvm.mlir.global: expected 'global_type' to be a type attribute"
      else
        pure attr.asType
    | none => throw "llvm.mlir.global: missing 'global_type' property"
  let alignment ← match attrDict["alignment".toUTF8]? with
    | some (.integerAttr attr) => pure (some attr)
    | some attr =>
      throw s!"llvm.mlir.global: expected 'alignment' to be an integer attribute, but got {attr}"
    | none => pure none
  let addrSpace ← match attrDict["addr_space".toUTF8]? with
    | some (.integerAttr attr) => pure attr
    | some attr =>
      throw s!"llvm.mlir.global: expected 'addr_space' to be an integer attribute, but got {attr}"
    | none => pure { value := 0, type := { bitwidth := 32 } }
  let linkage ← match attrDict["linkage".toUTF8]? with
    | some (.linkageAttr attr) => pure attr
    | some attr =>
      throw s!"llvm.mlir.global: expected 'linkage' to be an LLVM linkage attribute, but got {attr}"
    | none => throw "llvm.mlir.global: missing 'linkage' property"
  let constant ← getUnitAttr "constant" attrDict
  let value := attrDict["value".toUTF8]?
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) =>
      k ≠ "sym_name".toUTF8 &&
      k ≠ "global_type".toUTF8 &&
      k ≠ "value".toUTF8 &&
      k ≠ "alignment".toUTF8 &&
      k ≠ "addr_space".toUTF8 &&
      k ≠ "linkage".toUTF8 &&
      k ≠ "constant".toUTF8)
  return {
    sym_name := symName
    global_type := globalType
    value
    alignment
    addr_space := addrSpace
    linkage
    constant
    extra
  }

/-- Properties of `llvm.mlir.addressof`. -/
structure LLVMAddressOfProperties where
  global_name : FlatSymbolRefAttr
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMAddressOfProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMAddressOfProperties := do
  let globalName ← match attrDict["global_name".toUTF8]? with
    | some (.flatSymbolRefAttr attr) => pure attr
    | some attr =>
      throw s!"llvm.mlir.addressof: expected 'global_name' to be a flat symbol reference, but got {attr}"
    | none => throw "llvm.mlir.addressof: missing 'global_name' property"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "global_name".toUTF8)
  return { global_name := globalName, extra }

/-- Properties of integer comparison operations in the LLVM and arith dialects. -/
structure IcmpProperties where
  predicate : Data.LLVM.IntPred
deriving Inhabited, Repr, Hashable, DecidableEq

def IcmpProperties.fromAttrDictFor (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String IcmpProperties := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only one property, but got {attrDict.size} properties"
  let some attr := attrDict["predicate".toUTF8]?
    | throw s!"{opName}: missing predicate"
  let .integerAttr intAttr := attr
    | throw s!"{opName}: expected predicate to be an integer attribute, but got {attr}"
  if intAttr.value < 0 then
    throw s!"{opName}: invalid predicate {intAttr.value}"
  let some predicate := Data.LLVM.IntPred.fromNat intAttr.value.toNat
    | throw s!"{opName}: invalid predicate {intAttr.value}"
  return { predicate }

def IcmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String IcmpProperties :=
  IcmpProperties.fromAttrDictFor "llvm.icmp" attrDict

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
  Properties of the `llvm.call` operation. The `callee` is first-class; all
  other attributes are kept verbatim in `extra`. `callee` is optional because
  `llvm.call` doubles as an indirect-call operation.
-/
structure LLVMCallProperties where
  callee : Option FlatSymbolRefAttr
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMCallProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMCallProperties := do
  let callee ← match attrDict["callee".toUTF8]? with
    | some (.flatSymbolRefAttr s) => pure (some s)
    | some attr => throw s!"llvm.call: expected 'callee' to be a flat symbol reference, but got {attr}"
    | none => pure none
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "callee".toUTF8)
  return { callee, extra }

/--
  Properties of `llvm.func`. The `sym_name` and `function_type` attributes are
  modelled explicitly; all other attributes (e.g. `CConv`, `linkage`, `visibility_`)
  are preserved verbatim in `extra`.
-/
structure LLVMFuncProperties where
  sym_name : Option StringAttr
  function_type : Option TypeAttr
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMFuncProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMFuncProperties := do
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr s) => pure (some s)
    | some attr => throw s!"llvm.func: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => pure none
  let funcType ← match attrDict["function_type".toUTF8]? with
    | some attr =>
      if _ : attr.isType = false then
        throw "llvm.func: expected 'function_type' to be a type attribute"
      else pure (some attr.asType)
    | none => pure none
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "sym_name".toUTF8 && k ≠ "function_type".toUTF8)
  return { sym_name := symName, function_type := funcType, extra }

structure LLVMModuleFlagsProperties where
  flags : ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMModuleFlagsProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMModuleFlagsProperties := do
  let flagsAttr ← match attrDict["flags".toUTF8]? with
    | some (.arrayAttr flagsAttr) => .ok flagsAttr
    | some attr => .error s!"expected 'flags' to be an array attribute, but got {attr}"
    | none => .error "llvm.module_flags: missing 'flags' property"
  return { flags := flagsAttr }

end
end Veir
