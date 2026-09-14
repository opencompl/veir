module

public import Veir.RuntimeValue.Basic
public import Veir.GlobalOpInfo
public import Veir.Data.Felt

public section

open Veir.Data

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

namespace RuntimeValue

/--
  A predicate indicating whether a `RuntimeValue` is a value that is a runtime value
  of a given `TypeAttr`.
-/
@[expose]
def Conforms (val : RuntimeValue) (ty : TypeAttr) : Prop :=
  match val, ty with
  | .int bw _, ⟨.integerType intType, _⟩ => intType.bitwidth = bw
  | .float type _, ⟨.floatType floatType, _⟩ => floatType = type
  | .byte bw _, ⟨.byteType byteType, _⟩ => byteType.bitwidth = bw
  | .int bw _, ⟨.modArithType modArithType, _⟩ => modArithType.modulus.type.bitwidth = bw
  | .reg _, ⟨.registerType _, _⟩ => True
  | .addr _, ⟨.llvmPointerType _, _⟩ => True
  | .felt fieldType value, ⟨.feltType expectedType, _⟩ =>
    fieldType = expectedType ∧ FeltSemantics.IsCanonical fieldType value
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
    ∃ val, runtimeValue = .float fltType val := by
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

@[grind <=]
theorem Conforms.feltType {runtimeValue feltTy h} :
    Conforms runtimeValue ⟨.feltType feltTy, h⟩ →
    ∃ val, runtimeValue = .felt feltTy val := by
  cases runtimeValue <;> simp_all [Conforms]

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
