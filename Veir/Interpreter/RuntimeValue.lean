module

public import Veir.Data.LLVM.Byte.Basic
public import Veir.Data.RISCV.Reg.Basic
public import Veir.IR.Attribute

public section

open Veir.Data

namespace Veir

/--
  The type-erased representation of a value in the interpreter.
-/
inductive RuntimeValue where
| int (bitwidth : Nat) (value : LLVM.Int bitwidth)
| byte (bitwidth : Nat) (value : LLVM.Byte bitwidth)
| float (bitwidth : Nat) (value : Float)
| addr (value : UInt64)
| reg (value : RISCV.Reg)
deriving Inhabited

instance : ToString (RuntimeValue) where
  toString
    | .int _ val => ToString.toString val
    | .byte _ val => ToString.toString val
    | .float _ val => ToString.toString val
    | .addr val => ToString.toString val
    | .reg val => ToString.toString val

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

@[grind <=]
theorem Conforms.integerType :
    Conforms runtimeValue ⟨.integerType intType, h⟩ →
    ∃ val, runtimeValue = .int intType.bitwidth val := by
  simp only [Conforms]
  cases runtimeValue
  case int bw val =>
    simp only [int.injEq, exists_and_left]
    intro _; subst bw
    grind
  all_goals grind

@[grind <=]
theorem Conforms.byteType {runtimeValue byteType h} :
    Conforms runtimeValue ⟨.byteType byteType, h⟩ →
    ∃ val, runtimeValue = .byte byteType.bitwidth val := by
  simp only [Conforms]
  cases runtimeValue
  case byte bw val =>
    simp only [byte.injEq, exists_and_left]
    intro _; subst bw
    grind
  all_goals grind

@[grind <=]
theorem Conforms.floatType :
    Conforms runtimeValue ⟨.floatType fltType, h⟩ →
    ∃ val, runtimeValue = .float fltType.bitwidth val := by
  simp only [Conforms]
  cases runtimeValue
  case float bw val =>
    simp only [float.injEq, exists_and_left]
    intro _; subst bw
    grind
  all_goals grind

@[grind <=]
theorem Conforms.modArithType {runtimeValue modArithType h} :
    Conforms runtimeValue ⟨.modArithType modArithType, h⟩ →
    ∃ val, runtimeValue = .int modArithType.modulus.type.bitwidth val := by
  simp only [Conforms]
  cases runtimeValue
  case int bw val =>
    simp only [int.injEq, exists_and_left]
    intro _; subst bw
    grind
  all_goals grind

@[grind <=]
theorem Conforms.registerType :
    Conforms runtimeValue ⟨.registerType regType, h⟩ →
    ∃ val, runtimeValue = .reg val := by
  simp only [Conforms]
  cases runtimeValue <;> grind

@[grind <=]
theorem Conforms.llvmPointerType :
    Conforms runtimeValue ⟨.llvmPointerType _, h⟩ →
    ∃ val, runtimeValue = .addr val := by
  simp only [Conforms]
  cases runtimeValue <;> grind

@[expose]
def ArrayConforms (source : Array RuntimeValue) (target : Array TypeAttr) : Prop :=
  source.size = target.size ∧ ∀ (i : Nat) (_ : i < source.size), source[i]!.Conforms target[i]!

theorem ArrayConforms.take_succ_eq {source : Array RuntimeValue} {target : Array TypeAttr} :
    source.size = target.size →
    n < source.size →
    (ArrayConforms (source.take (n + 1)) (target.take (n + 1)) ↔
    (ArrayConforms (source.take n) (target.take n) ∧ (source[n]!).Conforms target[n]!)) := by
  simp only [ArrayConforms]
  intro hsize hn
  constructor
  · rintro ⟨_, h⟩
    constructor
    · constructor; grind
      intro i hi
      grind [h i]
    · grind [h n]
  · rintro ⟨⟨_, h⟩, hn⟩
    constructor; grind
    intro i hi
    grind [h i]

end RuntimeValue

end Veir
