module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Interpreter.Refinement.Basic
import Veir.Interpreter.Refinement.Lemmas

/-!
# Soundness vocabulary for the constant domain

`γ (constant c)` is every value that `c` refines.

`SoundFor a outcome i` says the fact `a`, which the analysis claims about result `i` of
an operation, is sound for one run of that operation: when the run produces a value for
result `i`, that value lies in `γ a`. It is stated against the interpreter outcome rather
than a value so that UB, which has no value, and `.fail` constrain nothing.
-/

public section

namespace Veir

namespace AbstractConstant

/-- Every value lies in `γ ⊤`. -/
@[simp]
theorem mem_γ_top (x : RuntimeValue) : x ∈ γ ⊤ := trivial

/-- No value lies in `γ ⊥`. -/
theorem not_mem_γ_bot (x : RuntimeValue) : x ∉ γ ⊥ := id

/-- A value lies in `γ (constant c)` exactly when `c` refines it. -/
theorem mem_γ_constant {x c : RuntimeValue} : x ∈ γ (.constant c) ↔ x ⊒ c := Iff.rfl

/-- `c` lies in `γ (constant c)`, by reflexivity of refinement. -/
theorem mem_γ_constant_self (c : RuntimeValue) : c ∈ γ (.constant c) :=
  RuntimeValue.isRefinedBy_refl c

/-- `γ` is closed under un-refinement: a value less defined than a member
    (`x ⊒ y`, `y ∈ γ a`) is a member. -/
theorem mem_γ_of_isRefinedBy {a : AbstractConstant} {x y : RuntimeValue}
    (hxy : x ⊒ y) (hy : y ∈ γ a) : x ∈ γ a := by
  cases a with
  | top => trivial
  | bottom => exact absurd hy (not_mem_γ_bot y)
  | constant c => exact RuntimeValue.isRefinedBy_trans hxy hy

/--
The fact `a` is sound for result `i` of `outcome`.

Only a successful interpretation constrains the fact:
* `.ub` means the source program's behaviour is unconstrained, so every fact is sound;
* `.fail` means the interpreter cannot model the operation, which likewise constrains
  nothing, so soundness is relative to the operations the interpreter models;
* on `.ok`, the result must lie in `γ a`.
-/
@[expose]
def SoundFor (a : AbstractConstant) (outcome : Interp (Array RuntimeValue)) (i : Nat) : Prop :=
  match outcome with
  | .ok results =>
      match results[i]? with
      | some actual => actual ∈ γ a
      | none => True
  | .ub _ => True
  | .fail _ => True

/-- `⊤` is sound for every outcome. -/
@[simp]
theorem soundFor_top (outcome : Interp (Array RuntimeValue)) (i : Nat) :
    SoundFor ⊤ outcome i := by
  cases outcome with
  | fail _ => trivial
  | ub _ => trivial
  | ok results =>
      simp only [SoundFor]
      cases results[i]? with
      | none => trivial
      | some actual => exact mem_γ_top actual

/-- Every fact is sound for UB. -/
@[simp]
theorem soundFor_ub (a : AbstractConstant) (i : Nat) {op : Option OperationPtr} :
    SoundFor a (.ub op) i := by
  unfold SoundFor; trivial

/-- Every fact is sound for an interpreter failure. -/
@[simp]
theorem soundFor_fail (a : AbstractConstant) (i : Nat) {op : Option OperationPtr} :
    SoundFor a (.fail op) i := by
  unfold SoundFor; trivial

/--
A fact sound for an outcome `outcome'` is sound for every outcome `outcome` that
`outcome'` refines.
-/
theorem soundFor_of_isRefinedBy {a : AbstractConstant}
    {outcome outcome' : Interp (Array RuntimeValue)} {i : Nat}
    (hRefines : Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy outcome outcome')
    (hSound : SoundFor a outcome' i) : SoundFor a outcome i := by
  cases outcome with
  | ub _ => trivial
  | fail _ => trivial
  | ok results =>
    cases outcome' with
    | ub _ => simp [Interp.isRefinedBy] at hRefines
    | fail _ => simp [Interp.isRefinedBy] at hRefines
    | ok results' =>
      simp only [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy] at hRefines
      obtain ⟨hSize, hEach⟩ := hRefines
      simp only [SoundFor] at hSound ⊢
      cases hResult : results[i]? with
      | none => trivial
      | some actual =>
        have hi : i < results.size := (Array.getElem?_eq_some_iff.mp hResult).1
        have hi' : i < results'.size := hSize ▸ hi
        have hActual : results[i] = actual := (Array.getElem?_eq_some_iff.mp hResult).2
        rw [Array.getElem?_eq_getElem hi'] at hSound
        have hStep := hEach i hi
        rw [getElem!_pos results i hi, getElem!_pos results' i hi', hActual] at hStep
        exact mem_γ_of_isRefinedBy hStep hSound

end AbstractConstant

end Veir
