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
| float (type : FloatType) (value : Data.Float.FloatValue type.format)
| addr (value : UInt64)
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

end

end Veir
