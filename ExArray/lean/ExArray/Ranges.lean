module

public section

open Std

/--
Abbreviation for a "python-like" range
These are the only ranges we will use in this file
-/
abbrev CORange := Rco Nat

@[grind=]
theorem mem_range_nat (i: Nat) (r: CORange) : (i ∈ r) ↔ r.lower ≤ i ∧ i < r.upper := by
  simp only [Membership.mem]

/--
This is a syntactic definition of range inclusion, that is a subset of
the inclusion relation based on the set of elements in each range.
The definition only disagrees when the ranges are empty.
-/
@[expose, grind=]
def IsIncluded (range1 range2 : CORange) : Prop :=
  range2.lower ≤ range1.lower ∧ range1.upper ≤ range2.upper

@[expose, grind=]
def IsIncludedIN (range1 : Rco Int) (range2 : Rco Nat) : Prop :=
  range2.lower ≤ range1.lower ∧ range1.upper ≤ range2.upper

instance : Decidable (IsIncluded r₁ r₂) := by
  unfold IsIncluded
  infer_instance

@[grind→]
theorem isIncluded_mem (range1 range2 : CORange) :
    IsIncluded range1 range2 →
    ∀ (i: Nat), (i ∈ range1) → (i ∈ range2) := by
  simp only [IsIncluded, mem_range_nat]
  grind only

@[expose]
def IsDisjoint (range1 range2 : CORange) : Prop :=
  range1.upper ≤ range2.lower ∨ range2.upper ≤ range1.lower

instance : Decidable (IsDisjoint r₁ r₂) := by
  unfold IsDisjoint
  infer_instance

@[grind=]
theorem isDisjoint_def (range1 range2 : CORange) :
    IsDisjoint range1 range2 ↔
    (range1.upper ≤ range2.lower) ∨ (range2.upper ≤ range1.lower) := by rfl

theorem isDisjoint_comm (range1 range2 : CORange) :
    IsDisjoint range1 range2 ↔ IsDisjoint range2 range1 := by
  simp only [IsDisjoint, or_comm]

@[grind→]
theorem isDisjoint_mem_left (range1 range2 : CORange) :
    IsDisjoint range1 range2 →
    ∀ (i: Nat), (i ∈ range1) → (i ∉ range2) := by
  simp only [IsDisjoint, mem_range_nat]
  grind only

@[grind→]
theorem isDisjoint_mem_right (range1 range2 : CORange) :
    IsDisjoint range1 range2 →
    ∀ (i: Nat), (i ∈ range2) → (i ∉ range1) := by
  simp only [IsDisjoint, mem_range_nat]
  grind only
