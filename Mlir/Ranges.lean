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
@[grind=]
def is_included (range1 range2 : CORange) : Prop :=
  range2.lower ≤ range1.lower ∧ range1.upper ≤ range2.upper

@[grind→]
theorem is_included_mem (range1 range2 : CORange) :
    is_included range1 range2 →
    ∀ (i: Nat), (i ∈ range1) → (i ∈ range2) := by
  simp only [is_included, mem_range_nat]
  grind only

def is_disjoint (range1 range2 : CORange) : Prop :=
  range1.upper ≤ range2.lower ∨ range2.upper ≤ range1.lower

@[grind=]
theorem is_disjoint_def (range1 range2 : CORange) :
    is_disjoint range1 range2 ↔
    (range1.upper ≤ range2.lower) ∨ (range2.upper ≤ range1.lower) := by rfl

theorem is_disjoint_comm (range1 range2 : CORange) :
    is_disjoint range1 range2 ↔ is_disjoint range2 range1 := by
  simp only [is_disjoint, or_comm]

@[grind→]
theorem is_disjoint_mem_left (range1 range2 : CORange) :
    is_disjoint range1 range2 →
    ∀ (i: Nat), (i ∈ range1) → (i ∉ range2) := by
  simp only [is_disjoint, mem_range_nat]
  grind only

@[grind→]
theorem is_disjoint_mem_right (range1 range2 : CORange) :
    is_disjoint range1 range2 →
    ∀ (i: Nat), (i ∈ range2) → (i ∉ range1) := by
  simp only [is_disjoint, mem_range_nat]
  grind only
