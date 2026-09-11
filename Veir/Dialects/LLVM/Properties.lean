module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.LLVM.FloatPred
public import Veir.Data.LLVM.AtomicOrdering
public import Veir.Data.LLVM.ComdatKind
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
  let exact ← getUnitAttr "isExact" attrDict
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
  let disjoint ← getUnitAttr "isDisjoint" attrDict
  return { disjoint := disjoint }

/--
  Properties of operations that can have the `nneg` flag, such as `llvm.zext`.
-/
structure NnegProperties where
  nneg : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def NnegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String NnegProperties := do
  let nneg ← getUnitAttr "nonNeg" attrDict
  return { nneg := nneg }

def NnegProperties.toAttrDict (props : NnegProperties) : Std.HashMap ByteArray Attribute :=
  if props.nneg then
    (Std.HashMap.emptyWithCapacity 1).insert "nonNeg".toUTF8 (.unitAttr UnitAttr.mk)
  else
    Std.HashMap.emptyWithCapacity 0

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

/--
  Properties of the `llvm.intr.assume` intrinsic. The condition is followed by
  the operands of its operand bundles: `op_bundle_sizes` gives the operand
  count of each bundle and `op_bundle_tags` its name. MLIR omits
  `op_bundle_tags` when there are no bundles.
-/
structure LLVMAssumeProperties where
  op_bundle_sizes : DenseArrayAttr
  op_bundle_tags : Option ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMAssumeProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMAssumeProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) =>
      k ≠ "op_bundle_sizes".toUTF8 && k ≠ "op_bundle_tags".toUTF8) then
    throw s!"llvm.intr.assume: unexpected property '{String.fromUTF8! key}'"
  let sizes ← match attrDict["op_bundle_sizes".toUTF8]? with
    | some (.denseArrayAttr sizes) => pure sizes
    | some attr =>
      throw s!"llvm.intr.assume: expected 'op_bundle_sizes' to be a dense array attribute, \
        but got {attr}"
    | none => throw "llvm.intr.assume: missing 'op_bundle_sizes' property"
  let tags ← match attrDict["op_bundle_tags".toUTF8]? with
    | some (.arrayAttr tags) => pure (some tags)
    | some attr =>
      throw s!"llvm.intr.assume: expected 'op_bundle_tags' to be an array attribute, but got {attr}"
    | none => pure none
  return { op_bundle_sizes := sizes, op_bundle_tags := tags }

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
| string (value : StringAttr)
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
  | .stringAttr stringAttr =>
    return { value := .string stringAttr }
  | _ =>
    throw s!"llvm.constant: expected 'value' to be an integer, float, dense elements, or string attribute, but got {attr}"

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

/-- Properties of `llvm.fcmp`. -/
structure FcmpProperties where
  predicate : Data.LLVM.FloatPred
  fastmathFlags : FastMathFlagsAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def FcmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FcmpProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) =>
      k ≠ "predicate".toUTF8 && k ≠ "fastmathFlags".toUTF8) then
    throw s!"llvm.fcmp: unexpected property '{String.fromUTF8! key}'"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "llvm.fcmp: missing predicate"
  let .integerAttr intAttr := attr
    | throw s!"llvm.fcmp: expected predicate to be an integer attribute, but got {attr}"
  if intAttr.type.bitwidth ≠ 64 then
    throw s!"llvm.fcmp: expected predicate to be an i64 integer attribute, but got {attr}"
  if intAttr.value < 0 then
    throw s!"llvm.fcmp: invalid predicate {intAttr.value}"
  let some predicate := Data.LLVM.FloatPred.fromNat intAttr.value.toNat
    | throw s!"llvm.fcmp: invalid predicate {intAttr.value}"
  let flags ← match attrDict["fastmathFlags".toUTF8]? with
    | some (.fastMathFlagsAttr flags) => .ok flags
    | some attr =>
      throw s!"llvm.fcmp: expected 'fastmathFlags' to be a fast math flags attribute, but got {attr}"
    | none => .ok { nnan := false, ninf := false, nsz := false }
  return { predicate, fastmathFlags := flags }

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
  Properties of `llvm.func`. Its required `sym_name` and `function_type`
  attributes are modelled explicitly; all other attributes (e.g. `CConv`,
  `linkage`, `visibility_`) are preserved verbatim in `extra`.
-/
structure LLVMFuncProperties where
  sym_name : StringAttr
  function_type : FunctionType
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMFuncProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMFuncProperties := do
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr s) => pure s
    | some attr => throw s!"llvm.func: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => throw "llvm.func: missing 'sym_name' property"
  let funcType ← match attrDict["function_type".toUTF8]? with
    | some (.llvmFunctionType ft) => pure ft
    | some attr =>
      throw s!"llvm.func: expected 'function_type' to be an LLVM function type, but got {attr}"
    | none => throw "llvm.func: missing 'function_type' property"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "sym_name".toUTF8 && k ≠ "function_type".toUTF8)
  return { sym_name := symName, function_type := funcType, extra }

/--
  Properties of `llvm.br`
-/
structure LLVMBrProperties where
  loop_annotation : Option LoopAnnotationAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMBrProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMBrProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) => k ≠ "loop_annotation".toUTF8) then
    throw s!"llvm.br: unexpected property '{String.fromUTF8! key}'"
  match attrDict["loop_annotation".toUTF8]? with
  | some (.loopAnnotationAttr annotation) => return { loop_annotation := some annotation }
  | some attr =>
    throw s!"llvm.br: expected 'loop_annotation' to be a loop annotation attribute, but got {attr}"
  | none => return { loop_annotation := none }

/--
  Properties of `llvm.cond_br`
-/
structure LLVMCondBrProperties where
  branch_weights : DenseArrayAttr
  loop_annotation : Option LoopAnnotationAttr
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMCondBrProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMCondBrProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) =>
      k ≠ "branch_weights".toUTF8 && k ≠ "loop_annotation".toUTF8
        && k ≠ "operandSegmentSizes".toUTF8) then
    throw s!"llvm.cond_br: unexpected property '{String.fromUTF8! key}'"
  let weightsAttr ← match attrDict["branch_weights".toUTF8]? with
    | some (.denseArrayAttr weightsAttr) => .ok weightsAttr
    | some attr =>
      throw s!"llvm.cond_br: expected 'branch_weights' to be a dense array attribute, but got {attr}"
    | none => .ok { elementType := { bitwidth := 32 }, values := #[] }
  let annotation ← match attrDict["loop_annotation".toUTF8]? with
    | some (.loopAnnotationAttr annotation) => .ok (some annotation)
    | some attr =>
      throw s!"llvm.cond_br: expected 'loop_annotation' to be a loop annotation attribute, but got {attr}"
    | none => .ok none
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "llvm.cond_br: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizesAttr := sizesAttr
    | throw s!"llvm.cond_br: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  return { branch_weights := weightsAttr, loop_annotation := annotation,
           operandSegmentSizes := sizesAttr }

/--
  Properties of `llvm.switch`. `case_operand_segments` splits the trailing case
  operands one group per case; `operandSegmentSizes` splits the operands into
  the value, the default destination's operands, and all case operands. The
  optional `case_values` and `branch_weights` are omitted again when absent.

  `case_values` is a dense elements attribute VeIR keeps as text, so the number
  of case values is not checked against the number of cases here.
-/
structure LLVMSwitchProperties where
  case_values : Option DenseElementsAttr
  case_operand_segments : DenseArrayAttr
  branch_weights : Option DenseArrayAttr
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMSwitchProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMSwitchProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) =>
      k ≠ "case_values".toUTF8 && k ≠ "case_operand_segments".toUTF8
        && k ≠ "branch_weights".toUTF8 && k ≠ "operandSegmentSizes".toUTF8) then
    throw s!"llvm.switch: unexpected property '{String.fromUTF8! key}'"
  let caseValues ← match attrDict["case_values".toUTF8]? with
    | some (.denseElementsAttr values) => .ok (some values)
    | some attr =>
      throw s!"llvm.switch: expected 'case_values' to be a dense elements attribute, but got {attr}"
    | none => .ok none
  let some segmentsAttr := attrDict["case_operand_segments".toUTF8]?
    | throw "llvm.switch: missing 'case_operand_segments' property"
  let .denseArrayAttr segmentsAttr := segmentsAttr
    | throw s!"llvm.switch: expected 'case_operand_segments' to be a dense array attribute, but got {segmentsAttr}"
  let weights ← match attrDict["branch_weights".toUTF8]? with
    | some (.denseArrayAttr weights) => .ok (some weights)
    | some attr =>
      throw s!"llvm.switch: expected 'branch_weights' to be a dense array attribute, but got {attr}"
    | none => .ok none
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "llvm.switch: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizesAttr := sizesAttr
    | throw s!"llvm.switch: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  return { case_values := caseValues, case_operand_segments := segmentsAttr,
           branch_weights := weights, operandSegmentSizes := sizesAttr }

/--
  The case values as integers, `#[]` when the attribute is absent.

  `case_values` is a dense elements attribute VeIR keeps as text, so its body --
  `5` for one case, `[13, 35]` for several -- is read back here. `none` if the
  body is not a list of integer literals.
-/
def LLVMSwitchProperties.caseValues? (props : LLVMSwitchProperties) : Option (Array Int) := do
  let some attr := props.case_values | return #[]
  /- Strip the brackets a multi-element body carries, and all whitespace. -/
  let body := attr.value.foldl (init := "") fun acc c =>
    if c = '[' || c = ']' || c = ' ' || c = '\t' || c = '\n' then acc else acc.push c
  if body.isEmpty then
    return #[]
  let mut values : Array Int := #[]
  for piece in body.splitOn "," do
    let some value := piece.toInt? | none
    values := values.push value
  return values

/--
  An optional array-valued property, absent when the attribute is not there.
-/
private def optionalArrayAttr (opName name : String)
    (attrDict : Std.HashMap ByteArray Attribute) : Except String (Option ArrayAttr) :=
  match attrDict[name.toUTF8]? with
  | some (.arrayAttr value) => .ok (some value)
  | some attr => .error s!"{opName}: expected '{name}' to be an array attribute, but got {attr}"
  | none => .ok none

/--
  Properties of the memory intrinsics `memset`, `memcpy`, and `memmove`.
-/
structure LLVMMemIntrinsicProperties where
  isVolatile : Bool
  arg_attrs : Option ArrayAttr
  res_attrs : Option ArrayAttr
  access_groups : Option ArrayAttr
  alias_scopes : Option ArrayAttr
  noalias_scopes : Option ArrayAttr
  tbaa : Option ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

/--
  An optional array of dictionaries, as MLIR requires of `arg_attrs` and
  `res_attrs`. MLIR does not check the array's length against the operand or
  result count, so neither does this.
-/
private def optionalDictArrayAttr (opName name : String)
    (attrDict : Std.HashMap ByteArray Attribute) : Except String (Option ArrayAttr) := do
  let some value ← optionalArrayAttr opName name attrDict
    | return none
  if value.value.any (fun attr => match attr with | .dictionaryAttr _ => false | _ => true) then
    throw s!"{opName}: attribute '{name}' failed to satisfy constraint: \
      Array of dictionary attributes"
  return some value

def LLVMMemIntrinsicProperties.fromAttrDictFor (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMMemIntrinsicProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) =>
      k ≠ "isVolatile".toUTF8 && k ≠ "arg_attrs".toUTF8 && k ≠ "res_attrs".toUTF8
        && k ≠ "access_groups".toUTF8 && k ≠ "alias_scopes".toUTF8
        && k ≠ "noalias_scopes".toUTF8 && k ≠ "tbaa".toUTF8
        && k ≠ "op_bundle_sizes".toUTF8 && k ≠ "op_bundle_tags".toUTF8) then
    throw s!"{opName}: unexpected property '{String.fromUTF8! key}'"
  let some volatileAttr := attrDict["isVolatile".toUTF8]?
    | throw s!"{opName}: missing 'isVolatile' property"
  let .integerAttr volatileAttr := volatileAttr
    | throw s!"{opName}: expected 'isVolatile' to be an i1 integer attribute, but got {volatileAttr}"
  if volatileAttr.type.bitwidth ≠ 1 then
    throw s!"{opName}: expected 'isVolatile' to be an i1 integer attribute, but got i{volatileAttr.type.bitwidth}"
  let argAttrs ← optionalDictArrayAttr opName "arg_attrs" attrDict
  let resAttrs ← optionalDictArrayAttr opName "res_attrs" attrDict
  let accessGroups ← optionalArrayAttr opName "access_groups" attrDict
  let aliasScopes ← optionalArrayAttr opName "alias_scopes" attrDict
  let noaliasScopes ← optionalArrayAttr opName "noalias_scopes" attrDict
  let tbaa ← optionalArrayAttr opName "tbaa" attrDict
  /- Parse and drop `op_bundle_sizes` and `op_bundle_tags` to match MLIR. -/
  return { isVolatile := volatileAttr.value ≠ 0, arg_attrs := argAttrs,
           res_attrs := resAttrs, access_groups := accessGroups,
           alias_scopes := aliasScopes, noalias_scopes := noaliasScopes,
           tbaa := tbaa }

def LLVMMemIntrinsicProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMMemIntrinsicProperties :=
  LLVMMemIntrinsicProperties.fromAttrDictFor "llvm.intr.memset" attrDict

/--
  Properties of `llvm.call_intrinsic`.
-/
structure LLVMCallIntrinsicProperties where
  intrin : StringAttr
  operandSegmentSizes : DenseArrayAttr
  op_bundle_sizes : DenseArrayAttr
  op_bundle_tags : Option ArrayAttr
  fastmathFlags : FastMathFlagsAttr
  arg_attrs : Option ArrayAttr
  res_attrs : Option ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMCallIntrinsicProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMCallIntrinsicProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) =>
      k ≠ "intrin".toUTF8 && k ≠ "operandSegmentSizes".toUTF8 && k ≠ "op_bundle_sizes".toUTF8
        && k ≠ "op_bundle_tags".toUTF8 && k ≠ "fastmathFlags".toUTF8
        && k ≠ "arg_attrs".toUTF8 && k ≠ "res_attrs".toUTF8) then
    throw s!"llvm.call_intrinsic: unexpected property '{String.fromUTF8! key}'"
  let some intrin := attrDict["intrin".toUTF8]?
    | throw "llvm.call_intrinsic: missing 'intrin' property"
  let .stringAttr intrin := intrin
    | throw s!"llvm.call_intrinsic: expected 'intrin' to be a string attribute, but got {intrin}"
  let some sizes := attrDict["operandSegmentSizes".toUTF8]?
    | throw "llvm.call_intrinsic: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizes := sizes
    | throw s!"llvm.call_intrinsic: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizes}"
  let some bundleSizes := attrDict["op_bundle_sizes".toUTF8]?
    | throw "llvm.call_intrinsic: missing 'op_bundle_sizes' property"
  let .denseArrayAttr bundleSizes := bundleSizes
    | throw s!"llvm.call_intrinsic: expected 'op_bundle_sizes' to be a dense array attribute, but got {bundleSizes}"
  let tags ← optionalArrayAttr "llvm.call_intrinsic" "op_bundle_tags" attrDict
  let argAttrs ← optionalDictArrayAttr "llvm.call_intrinsic" "arg_attrs" attrDict
  let resAttrs ← optionalDictArrayAttr "llvm.call_intrinsic" "res_attrs" attrDict
  let ⟨flags⟩ ← (FastMathFlagsProperties.fromAttrDict attrDict).mapError
    (s!"llvm.call_intrinsic: {·}")
  return { intrin, operandSegmentSizes := sizes, op_bundle_sizes := bundleSizes,
           op_bundle_tags := tags, fastmathFlags := flags,
           arg_attrs := argAttrs, res_attrs := resAttrs }

/--
  Properties of `llvm.insertvalue` and `llvm.extractvalue`: the path into the
  aggregate.
-/
structure LLVMPositionProperties where
  position : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMPositionProperties.fromAttrDictFor (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) : Except String LLVMPositionProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) => k ≠ "position".toUTF8) then
    throw s!"{opName}: unexpected property '{String.fromUTF8! key}'"
  let some position := attrDict["position".toUTF8]?
    | throw s!"{opName}: missing 'position' property"
  let .denseArrayAttr position := position
    | throw s!"{opName}: expected 'position' to be a dense array attribute, but got {position}"
  return { position }

/-- Properties of `llvm.fence`: how strongly it orders, and over what scope. -/
structure LLVMFenceProperties where
  ordering : Data.LLVM.AtomicOrdering
  syncscope : Option StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMFenceProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMFenceProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) =>
      k ≠ "ordering".toUTF8 && k ≠ "syncscope".toUTF8) then
    throw s!"llvm.fence: unexpected property '{String.fromUTF8! key}'"
  let some attr := attrDict["ordering".toUTF8]?
    | throw "llvm.fence: missing 'ordering' property"
  let .integerAttr intAttr := attr
    | throw s!"llvm.fence: expected 'ordering' to be an integer attribute, but got {attr}"
  if intAttr.type.bitwidth ≠ 64 then
    throw s!"llvm.fence: expected 'ordering' to be an i64 integer attribute, but got {attr}"
  if intAttr.value < 0 then
    throw s!"llvm.fence: invalid ordering {intAttr.value}"
  let some ordering := Data.LLVM.AtomicOrdering.fromNat intAttr.value.toNat
    | throw s!"llvm.fence: invalid ordering {intAttr.value}"
  let syncscope ← match attrDict["syncscope".toUTF8]? with
    | some (.stringAttr syncscope) => .ok (some syncscope)
    | some attr =>
      throw s!"llvm.fence: expected 'syncscope' to be a string attribute, but got {attr}"
    | none => .ok none
  return { ordering, syncscope }

/-- Properties of `llvm.comdat`: the name of the comdat group. -/
structure LLVMComdatProperties where
  sym_name : StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMComdatProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMComdatProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) => k ≠ "sym_name".toUTF8) then
    throw s!"llvm.comdat: unexpected property '{String.fromUTF8! key}'"
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr s) => pure s
    | some attr => throw s!"llvm.comdat: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => throw "llvm.comdat: missing 'sym_name' property"
  return { sym_name := symName }

/-- Properties of `llvm.comdat_selector`: its name and how duplicates are resolved. -/
structure LLVMComdatSelectorProperties where
  sym_name : StringAttr
  comdat : Data.LLVM.ComdatKind
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMComdatSelectorProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMComdatSelectorProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) =>
      k ≠ "sym_name".toUTF8 && k ≠ "comdat".toUTF8) then
    throw s!"llvm.comdat_selector: unexpected property '{String.fromUTF8! key}'"
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr s) => pure s
    | some attr =>
      throw s!"llvm.comdat_selector: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => throw "llvm.comdat_selector: missing 'sym_name' property"
  let some attr := attrDict["comdat".toUTF8]?
    | throw "llvm.comdat_selector: missing 'comdat' property"
  let .integerAttr intAttr := attr
    | throw s!"llvm.comdat_selector: expected 'comdat' to be an integer attribute, but got {attr}"
  if intAttr.type.bitwidth ≠ 64 then
    throw s!"llvm.comdat_selector: expected 'comdat' to be an i64 integer attribute, but got {attr}"
  if intAttr.value < 0 then
    throw s!"llvm.comdat_selector: invalid comdat kind {intAttr.value}"
  let some kind := Data.LLVM.ComdatKind.fromNat intAttr.value.toNat
    | throw s!"llvm.comdat_selector: invalid comdat kind {intAttr.value}"
  return { sym_name := symName, comdat := kind }

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
