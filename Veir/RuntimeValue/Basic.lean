module

public import Veir.Data.LLVM.Byte.Basic
public import Veir.Data.RISCV.Reg.Basic
public import Veir.IR.Attribute

public section

namespace Veir

/--
  A pointer into interpreter memory: the object it may access and a byte
  offset into it. Pointers derived from different objects never alias, and an
  access outside the object is undefined behaviour. Stored to memory, cast to
  an integer or moved into a register, the pair is packed into 64 bits with
  the object above the offset, so objects are limited to 4 GiB.
-/
structure Pointer where
  object : UInt32
  offset : UInt32
deriving Inhabited, Repr, DecidableEq, Hashable

namespace Pointer

/-- The null pointer. Object 0 holds no bytes, so every access through it is UB. -/
def null : Pointer := ⟨0, 0⟩

def isNull (p : Pointer) : Bool := p == null

def toUInt64 (p : Pointer) : UInt64 := (p.object.toUInt64 <<< 32) ||| p.offset.toUInt64

def ofUInt64 (v : UInt64) : Pointer := ⟨(v >>> 32).toUInt32, v.toUInt32⟩

instance : ToString Pointer where
  toString p := s!"ptr({p.object}, {p.offset})"

end Pointer

/--
  The type-erased representation of a value used by interpretation and
  compile-time evaluation.
-/
inductive RuntimeValue where
| int (bitwidth : Nat) (value : Data.LLVM.Int bitwidth)
| byte (bitwidth : Nat) (value : Data.LLVM.Byte bitwidth)
| float (type : FloatType) (value : Data.Float.FloatValue type.format)
| addr (value : Pointer)
| reg (value : Data.RISCV.Reg)
/-- A canonical natural-number representative in the field identified by `fieldType`. -/
| felt (fieldType : FeltType) (value : Nat)
deriving Inhabited

instance : ToString RuntimeValue where
  toString
    | .int _ val => ToString.toString val
    | .byte _ val => ToString.toString val
    | .float _ val => ToString.toString val
    | .addr val => ToString.toString val
    | .reg val => ToString.toString val
    | .felt fieldType val => s!"{val} : {fieldType}"

/--
  Whether a runtime value is wholly poison. A `byte` is wholly poison when
  every one of its bits is, matching the value that `getPoisonForType`
  constructs.
-/
def RuntimeValue.isPoison : RuntimeValue → Bool
  | .int _ .poison => true
  | .byte width value => value.poison == BitVec.allOnes width
  | _ => false

/--
  The wholly-poisoned `RuntimeValue` of type `ty`, for the types that have one.
  Used to materialize a result for an operation whose evaluation triggers UB.
-/
def RuntimeValue.getPoisonForType (ty : TypeAttr) : Option RuntimeValue :=
  match ty.val with
  | .integerType intTy => some (.int intTy.bitwidth .poison)
  | .byteType byteTy => some (.byte byteTy.bitwidth Data.LLVM.Byte.allPoison)
  | _ => none

end Veir
