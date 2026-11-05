module

/-!
  # A model of tensor values

  This file gives a model of the values of the builtin `tensor` type, shared by the
  dialects that operate on tensors, such as `tensor` and `linalg`. It is a
  specification: an interpreter may store tensors differently, e.g. as flat row-major
  arrays, and relate them to this model.

  A tensor is a static shape together with a function from indices to elements. The
  shape is a `List Nat`, which is `TensorType.shape.toList` for a value of a
  `TensorType`. Only the elements at indices within the shape are meaningful, so
  tensors are compared with `Tensor.Rel`, which ignores the other elements, rather
  than with `=`. A scalar is a rank-0 tensor, which holds its value at the index `[]`.
-/

namespace Veir.Data

public section

/-- A tensor with a static `shape` and the element `get idx` at every index `idx`. -/
structure Tensor (α : Type) where
  shape : List Nat
  get : List Nat → α

namespace Tensor

/-! ## Indices -/

/-- `idx` is an index within `shape`: it has the same length, and is smaller pointwise. -/
@[expose]
def InBounds : List Nat → List Nat → Prop
  | [], [] => True
  | i :: is, d :: ds => i < d ∧ InBounds is ds
  | _, _ => False

instance instDecidableInBounds : ∀ idx shape, Decidable (InBounds idx shape)
  | [], [] => .isTrue trivial
  | i :: is, d :: ds =>
    have := instDecidableInBounds is ds
    inferInstanceAs (Decidable (i < d ∧ InBounds is ds))
  | [], _ :: _ | _ :: _, [] => .isFalse id

/-- All indices within `shape`, in row-major (lexicographic) order. -/
@[expose]
def indices : List Nat → List (List Nat)
  | [] => [[]]
  | d :: ds => (List.range d).flatMap fun i => (indices ds).map (i :: ·)

/-- The indices in `indices shape` are exactly those within `shape`. -/
theorem mem_indices {shape idx : List Nat} : idx ∈ indices shape ↔ InBounds idx shape := by
  induction shape generalizing idx with
  | nil => cases idx <;> simp [indices, InBounds]
  | cons d ds ih => cases idx <;> simp [indices, InBounds, ← ih]

/-! ## Operations -/

/-- Replace the element of `t` at `idx` by `v`. -/
@[expose]
def set (t : Tensor α) (idx : List Nat) (v : α) : Tensor α :=
  { t with get := fun i => if i = idx then v else t.get i }

/-- The elements of `t` in row-major order. -/
@[expose]
def toList (t : Tensor α) : List α :=
  (indices t.shape).map t.get

/-! ## Relating tensors -/

/--
  Two tensors are related by `r` if they have the same shape and their elements within
  it are related by `r`. For example, `Rel Eq` is equivalence, and `Rel` of the
  refinement of the elements is the refinement of tensors.
-/
@[expose]
def Rel (r : α → β → Prop) (t : Tensor α) (u : Tensor β) : Prop :=
  t.shape = u.shape ∧ ∀ idx, InBounds idx t.shape → r (t.get idx) (u.get idx)

theorem Rel.refl {r : α → α → Prop} (hr : ∀ a, r a a) (t : Tensor α) : Rel r t t :=
  ⟨rfl, fun _ _ => hr _⟩

theorem Rel.symm {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {t u : Tensor α}
    (h : Rel r t u) : Rel r u t :=
  ⟨h.1.symm, fun idx hidx => hr _ _ (h.2 idx (h.1 ▸ hidx))⟩

theorem Rel.trans {r : α → α → Prop} (hr : ∀ a b c, r a b → r b c → r a c)
    {t u v : Tensor α} (h₁ : Rel r t u) (h₂ : Rel r u v) : Rel r t v :=
  ⟨h₁.1.trans h₂.1, fun idx hidx => hr _ _ _ (h₁.2 idx hidx) (h₂.2 idx (h₁.1 ▸ hidx))⟩

/-- Writing related elements at the same index keeps tensors related. -/
theorem Rel.set {r : α → β → Prop} {t : Tensor α} {u : Tensor β} (h : Rel r t u)
    (idx : List Nat) (hv : r v w) : Rel r (t.set idx v) (u.set idx w) :=
  ⟨h.1, fun i hi => by
    simp only [Tensor.set]
    split
    · exact hv
    · exact h.2 i hi⟩

/-- Two tensors are equivalent if they have the same shape and agree within it. -/
abbrev Equiv : Tensor α → Tensor α → Prop :=
  Rel Eq

@[refl]
theorem Equiv.refl (t : Tensor α) : t.Equiv t :=
  Rel.refl (fun _ => rfl) t

@[symm]
theorem Equiv.symm {t u : Tensor α} (h : t.Equiv u) : u.Equiv t :=
  Rel.symm (r := Eq) (fun _ _ => Eq.symm) h

theorem Equiv.trans {t u v : Tensor α} (h₁ : t.Equiv u) (h₂ : u.Equiv v) : t.Equiv v :=
  Rel.trans (r := Eq) (fun _ _ _ => Eq.trans) h₁ h₂

/-- Writing outside the shape of a tensor gives an equivalent tensor. -/
theorem set_equiv {t : Tensor α} (h : ¬InBounds idx t.shape) (v : α) :
    (t.set idx v).Equiv t :=
  ⟨rfl, fun i hi => by
    simp only [set, ite_eq_right_iff]
    rintro rfl
    exact absurd hi h⟩

end Tensor

end

end Veir.Data
