module

public import Veir.OpCode
public import Veir.IR.Attribute
public import Veir.IR.Simp
public import Veir.ForLean
public import Veir.IR.OpInfo

namespace Veir

public section

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
  let nsw ← match attrDict["nsw".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'nsw' to be an optional unit attribute, but got {attr}"
    | none => .ok false
  let nuw ← match attrDict["nuw".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'nuw' to be an optional unit attribute, but got {attr}"
    | none => .ok false
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
  let exact ← match attrDict["exact".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'exact' to be an optional unit attribute, but got {attr}"
    | none => .ok false
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
  let disjoint ← match attrDict["disjoint".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'disjoint' to be an optional unit attribute, but got {attr}"
    | none => .ok false
  return { disjoint := disjoint }

/--
  Properties of operations that can have the `nneg` flag, such as `llvm.zext`.
-/
structure NnegProperties where
  nneg : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def NnegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String NnegProperties := do
  let nneg ← match attrDict["nneg".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'nneg' to be an optional unit attribute, but got {attr}"
    | none => .ok false
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

structure CondBrConstantProperties where
  branch_weights : DenseArrayAttr
  operandSegmentSizes : DenseArrayAttr

deriving Inhabited, Repr, Hashable, DecidableEq

def CondBrConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CondBrConstantProperties := do
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

end
end Veir
