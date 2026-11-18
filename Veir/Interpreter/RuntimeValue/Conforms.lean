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
  | .int bw _, ⟨.indexType _, _⟩ => bw = IndexType.bitwidth
  | .reg _, ⟨.registerType _, _⟩ => True
  | .addr _, ⟨.llvmPointerType _, _⟩ => True
  | .felt fieldType value, ⟨.feltType expectedType, _⟩ =>
    fieldType = expectedType ∧ FeltSemantics.IsCanonical fieldType value
  | .tensor elements, ⟨.tensorType tensorType, _⟩ =>
    if h : tensorType.elementType.isType then
      elements.size = tensorType.numElements ∧
        ∀ i : Fin elements.size, Conforms elements[i] ⟨tensorType.elementType, h⟩
    else False
  | _, _ => False
termination_by val

/-- Decide conformance recursively, including tensor sizes and element types. -/
def decidableConforms (val : RuntimeValue) (ty : TypeAttr) : Decidable (Conforms val ty) := by
  unfold Conforms
  split <;> try infer_instance
  · next elements tensorType _ =>
      have (h) (i : Fin elements.size) := decidableConforms elements[i] ⟨tensorType.elementType, h⟩
      infer_instance
termination_by val

instance : Decidable (Conforms val ty) := decidableConforms val ty

@[simp, grind =]
theorem Conforms.integerType :
    Conforms runtimeValue (.of IntegerType intType) ↔
    ∃ val, runtimeValue = .int intType.bitwidth val := by
  cases runtimeValue <;> unfold Conforms <;>
    simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] <;>
    constructor <;> rintro ⟨⟩ <;> grind

@[simp, grind =]
theorem Conforms.byteType {runtimeValue byteType} :
    Conforms runtimeValue (.of LLVM.ByteType byteType) ↔
    ∃ val, runtimeValue = .byte byteType.bitwidth val := by
  cases runtimeValue <;> unfold Conforms <;>
    simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] <;>
    constructor <;> rintro ⟨⟩ <;> grind

@[simp, grind =]
theorem Conforms.floatType :
    Conforms runtimeValue (.of FloatType fltType) ↔
    ∃ val, runtimeValue = .float fltType val := by
  cases runtimeValue <;> unfold Conforms <;>
    simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] <;>
    constructor <;> rintro ⟨⟩ <;> grind

@[simp, grind =]
theorem Conforms.modArithType {runtimeValue modArithType} :
    Conforms runtimeValue (.of ModArithType modArithType) ↔
    ∃ val, runtimeValue = .int modArithType.modulus.type.bitwidth val := by
  cases runtimeValue <;> unfold Conforms <;>
    simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] <;>
    constructor <;> rintro ⟨⟩ <;> grind

@[simp, grind =]
theorem Conforms.indexType :
    Conforms runtimeValue (.of IndexType idxType) ↔
    ∃ val, runtimeValue = .int IndexType.bitwidth val := by
  cases runtimeValue <;> unfold Conforms <;>
    simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] <;>
    constructor <;> rintro ⟨⟩ <;> grind

@[simp, grind =]
theorem Conforms.registerType :
    Conforms runtimeValue (.of RegisterType regType) ↔
    ∃ val, runtimeValue = .reg val := by
  cases runtimeValue <;> unfold Conforms <;>
    simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] <;>
    constructor <;> rintro ⟨⟩ <;> grind

@[simp, grind =]
theorem Conforms.llvmPointerType :
    Conforms runtimeValue (.of LLVM.PointerType ptrType) ↔
    ∃ val, runtimeValue = .addr val := by
  cases runtimeValue <;> unfold Conforms <;>
    simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] <;>
    constructor <;> rintro ⟨⟩ <;> grind

@[simp, grind =]
theorem Conforms.feltType {runtimeValue feltTy} :
    Conforms runtimeValue (.of FeltType feltTy) ↔
    ∃ val, runtimeValue = .felt feltTy val ∧ FeltSemantics.IsCanonical feltTy val := by
  cases runtimeValue <;> unfold Conforms <;>
    simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] <;>
    constructor <;> rintro ⟨⟩ <;> grind

/--
  A tensor value is a row-major `.tensor` with one element per entry of the shape's
  product, every element conforming to the element type.
-/
@[simp, grind =]
theorem Conforms.tensorType {runtimeValue tensorType} :
    Conforms runtimeValue (.of TensorType tensorType) ↔
    ∃ elements, runtimeValue = .tensor elements ∧ elements.size = tensorType.numElements ∧
      ∃ h : tensorType.elementType.isType,
        ∀ e ∈ elements, Conforms e ⟨tensorType.elementType, h⟩ := by
  cases runtimeValue <;> unfold Conforms <;>
    simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject, reduceCtorEq, false_and,
      exists_false]
  next elements =>
    simp only [RuntimeValue.tensor.injEq, exists_eq_left']
    split
    · next h =>
      simp only [h, exists_true_left, and_congr_right_iff]
      intro _
      constructor
      · intro hall e he
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp he
        exact hall ⟨i, hi⟩
      · intro hall i
        exact hall _ (Array.getElem_mem i.isLt)
    · next h => simp [h]

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
