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
| addr (value : UInt64)
| reg (value : Data.RISCV.Reg)
deriving Inhabited

namespace RuntimeValue

/--
  A predicate indicating whether a `RuntimeValue` is a value that is a runtime value
  of a given `TypeAttr`.
-/
@[expose]
def Conforms (val : RuntimeValue) (ty : TypeAttr) : Prop :=
  match val, ty with
  | .int bw _, ⟨.integerType intType, _⟩ => intType.bitwidth = bw
  | .float bw _, ⟨.floatType floatType, _⟩ => floatType.bitwidth = bw
  | .byte bw _, ⟨.byteType byteType, _⟩ => byteType.bitwidth = bw
  | .int bw _, ⟨.modArithType modArithType, _⟩ => modArithType.modulus.type.bitwidth = bw
  | .reg _, ⟨.registerType _, _⟩ => True
  | .addr _, ⟨.llvmPointerType _, _⟩ => True
  | _, _ => False

instance : Decidable (Conforms val ty) := by
  unfold Conforms
  split <;> infer_instance

end RuntimeValue

instance : ToString RuntimeValue where
  toString
    | .int _ val => ToString.toString val
    | .byte _ val => ToString.toString val
    | .float _ val => ToString.toString val
    | .addr val => ToString.toString val
    | .reg val => ToString.toString val

end

end Veir
