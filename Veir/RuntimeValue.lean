module

public import Veir.Data.LLVM.Byte.Basic
public import Veir.Data.RISCV.Reg.Basic
public import Veir.IR.Attribute

namespace Veir

public section

/--
  The type-erased representation of a value used by interpretation and
  compile-time evaluation.
-/
inductive RuntimeValue where
| int (bitwidth : Nat) (value : Data.LLVM.Int bitwidth)
| byte (bitwidth : Nat) (value : Data.LLVM.Byte bitwidth)
| float (bitwidth : Nat) (value : Float)
| floatPoison (bitwidth : Nat)
| addr (value : UInt64)
| reg (value : Data.RISCV.Reg)
deriving Inhabited

instance : ToString RuntimeValue where
  toString
    | .int _ val => ToString.toString val
    | .byte _ val => ToString.toString val
    | .float _ val => ToString.toString val
    | .floatPoison _ => "poison"
    | .addr val => ToString.toString val
    | .reg val => ToString.toString val

/-- Whether a runtime value is wholly poison. -/
def RuntimeValue.isPoison : RuntimeValue → Bool
  | .int _ .poison => true
  | .byte width value => value.poison == BitVec.allOnes width
  | .floatPoison _ => true
  | _ => false

/-- Construct the wholly-poisoned runtime value for a type that supports one. -/
def RuntimeValue.getPoisonForType (type : TypeAttr) : Option RuntimeValue :=
  match type.val with
  | .integerType intType => some (.int intType.bitwidth .poison)
  | .byteType byteType => some (.byte byteType.bitwidth Data.LLVM.Byte.allPoison)
  | .floatType floatType => some (.floatPoison floatType.bitwidth)
  | _ => none

end

end Veir
