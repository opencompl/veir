module

public import Veir.IR.Attribute
public import Std.Data.HashMap

/- This is needed as some properties have ByteArray and require Repr instances -/
deriving instance Repr for ByteArray

namespace Veir

public section

/--
  Properties of a `builtin.unregistered` operation. Holds the original (parsed) operation name
  and the original `<{...}>` properties dictionary so that the operation can be printed back
  with its source representation preserved.
-/
structure UnregisteredProperties where
  opName : ByteArray
  properties : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def UnregisteredProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String UnregisteredProperties :=
  .ok { opName := .empty, properties := DictionaryAttr.fromArray attrDict.toArray }

/--
  Read a required integer attribute that must be declared `i64`, returning the
  value it denotes as a `BitVec 64`.

  A dialect whose integer width is fixed by the target rather than by upstream
  compatibility -- as the RISC-V dialects' is, they being ours alone -- uses this
  to check the width once, here at the parse boundary, and then store only the
  decoded value. Nothing downstream holds a width, so nothing downstream can
  disagree about one. Contrast `llvm.mlir.constant`, which must keep the
  attribute's own width because MLIR lets it differ from the result width; see
  `decodeLLVMIntegerConstant`.
-/
def getI64Attr (what key : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (BitVec 64) := do
  let some attr := attrDict[key.toUTF8]?
    | throw s!"{what}: missing '{key}' property"
  let .integerAttr intAttr := attr
    | throw s!"{what}: expected '{key}' to be an integer attribute, but got {attr}"
  if intAttr.type.bitwidth ≠ 64 then
    throw s!"{what}: expected '{key}' to be a 64-bit signless integer attribute, but got i{intAttr.type.bitwidth}"
  return BitVec.ofInt 64 intAttr.value

/-- Re-encode a `getI64Attr` value as the `i64` attribute it is printed as. -/
def i64Attr (value : BitVec 64) : Attribute :=
  .integerAttr (IntegerAttr.mk value.toInt (IntegerType.mk 64))

def getUnitAttr (key : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Bool := do
  match attrDict[key.toUTF8]? with
  | some (.unitAttr _) => .ok true
  | some attr => .error s!"expected '{key}' to be an optional unit attribute, but got {attr}"
  | none => .ok false

end

end Veir
