import Veir.Data.LLVM

namespace Veir.Data.LLVM

def refines (before after : Int w) : Prop :=
  if before = Int.poison then True
  else if after = Int.poison then False
  else before = after

def mergeOverflowFlags (nsw1 nuw1 : Bool) (nsw2 nuw2 : Bool) : Bool × Bool :=
  (nsw1 && nsw2, nuw1 && nuw2)

def addAttrsNoOverflow (cst1 cst2 : BitVec w) (nsw nuw : Bool) : Bool :=
  Int.add (Int.val cst1) (Int.val cst2) nsw nuw ≠ Int.poison

theorem AddIAddConstant {x : Int 8} :
    (nsw, nuw) = mergeOverflowFlags nsw1 nuw1 nsw2 nuw2 →
    addAttrsNoOverflow cst1 cst2 nsw nuw →
    refines (Int.add (Int.add x (Int.val cst1) nsw1 nuw1) (Int.val cst2) nsw2 nuw2)
      (Int.add x (Int.val (cst1 + cst2)) nsw nuw) := by
  simp only [mergeOverflowFlags, Prod.mk.injEq, and_imp]
  simp only [addAttrsNoOverflow, Int.add, Id.run, pure, bind, ne_eq, decide_not,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, refines, if_false_left,
    if_true_left]
  cases x; rotate_left; grind
  intro hnsw hnuw
  cases nsw1 <;> cases nsw2 <;> cases nuw1 <;> cases nuw2 <;> simp_all <;> try grind
  · split; grind
    intro
    simp
    bv_decide
  · split; grind
    split; rotate_left; grind; rename_i h
    split at h; grind
    have := (Int.val.injEq _ _).mp h
    split; grind
    split; rotate_left; grind
    bv_decide
  · split; grind
    simp_all
    grind
  · split; grind
    split; grind
    simp_all
    bv_decide
  · split; grind
    split; rotate_left; grind; rename_i h
    split at h; grind
    have := (Int.val.injEq _ _).mp h
    split; grind
    simp_all
    split; grind
    split; rotate_left; grind
    bv_decide
  · split; grind
    split; rotate_left; grind
    rename_i h
    split at h; grind
    split at h; grind
    have := (Int.val.injEq _ _).mp h
    split; grind

    simp_all
  · sorry
