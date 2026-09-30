module

public import Veir.Interpreter.RuntimeValue.Basic
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

@[simp, grind =]
theorem Conforms.integerType :
    Conforms runtimeValue (.of IntegerType intType) ↔
    ∃ val, runtimeValue = .int intType.bitwidth val := by
  simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject, Conforms]
  grind

@[simp, grind =]
theorem Conforms.byteType {runtimeValue byteType} :
    Conforms runtimeValue (.of LLVM.ByteType byteType) ↔
    ∃ val, runtimeValue = .byte byteType.bitwidth val := by
  simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject, Conforms]
  grind

@[simp, grind =]
theorem Conforms.floatType :
    Conforms runtimeValue (.of FloatType fltType) ↔
    ∃ val, runtimeValue = .float fltType val := by
  simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject, Conforms]
  grind

@[simp, grind =]
theorem Conforms.modArithType {runtimeValue modArithType} :
    Conforms runtimeValue (.of ModArithType modArithType) ↔
    ∃ val, runtimeValue = .int modArithType.modulus.type.bitwidth val := by
  simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject, Conforms]
  grind

@[simp, grind =]
theorem Conforms.registerType :
    Conforms runtimeValue (.of RegisterType regType) ↔
    ∃ val, runtimeValue = .reg val := by
  simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject, Conforms]
  grind

@[simp, grind =]
theorem Conforms.llvmPointerType :
    Conforms runtimeValue (.of LLVM.PointerType ptrType) ↔
    ∃ val, runtimeValue = .addr val := by
  simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject, Conforms]
  cases runtimeValue <;> grind

@[simp, grind =]
theorem Conforms.feltType {runtimeValue feltTy} :
    Conforms runtimeValue (.of FeltType feltTy) ↔
    ∃ val, runtimeValue = .felt feltTy val ∧ FeltSemantics.IsCanonical feltTy val := by
  simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject, Conforms]
  cases runtimeValue <;> simp_all <;> grind

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

/-! Pointwise conformance of a list of runtime values with a list of type attributes. -/
def ListConforms (source : List RuntimeValue) (target : List TypeAttr) : Prop :=
  match source, target with
  | [], [] => True
  | (x :: xs), (y :: ys) => x.Conforms y ∧ ListConforms xs ys
  | _, _ => False

theorem ListConforms.iff_arrayConforms_toArray :
    ListConforms source target ↔ ArrayConforms source.toArray target.toArray := by
  simp only [ArrayConforms, List.size_toArray, List.getElem!_toArray]
  induction source generalizing target with
  | nil => grind [ListConforms]
  | cons x xs ih =>
    cases target with
    | nil => grind [ListConforms]
    | cons y ys => simp [ListConforms, Nat.forall_lt_succ_left, ih, and_left_comm]

theorem ArrayConforms.iff_listConforms_toList :
    ArrayConforms source target ↔ ListConforms source.toList target.toList := by
  simpa using (ListConforms.iff_arrayConforms_toArray
    (source := source.toList) (target := target.toList)).symm

namespace ListConforms

@[grind .]
theorem cons_inv_right :
    ListConforms source (y :: target) →
    ∃ x xs, source = x :: xs ∧ x.Conforms y ∧ ListConforms xs target := by
  cases source <;> grind [ListConforms]

@[grind .]
theorem cons_inv_left :
    ListConforms (x :: source) target →
    ∃ y ys, target = y :: ys ∧ x.Conforms y ∧ ListConforms source ys := by
  cases target <;> grind [ListConforms]

@[grind .]
theorem nil_inv_right :
    ListConforms source [] → source = [] := by
  cases source <;> simp [ListConforms]

@[grind .]
theorem nil_inv_left :
    ListConforms [] target → target = [] := by
  cases target <;> simp [ListConforms]

end ListConforms

end RuntimeValue
