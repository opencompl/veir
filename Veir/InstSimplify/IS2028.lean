import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2028

/-- Scalar LLVM rule from upstream InstructionSimplify.cpp at 2028. -/
def pattern (sw0 sw1 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let ab ← MatchProg.operation (.llvm .or) (cond sw0 #[b, a] #[a, b]) #[ty]
    let r ← MatchProg.root (.llvm .and) (cond sw1 #[a, ab.res[0]!] #[ab.res[0]!, a]) #[ty]
    return a)
  pure (fun x => x)

theorem semantic (w : Nat) (a b : LLVM.Int w) (d0 : Bool) :
    RuntimeValue.int w (LLVM.Int.and (LLVM.Int.or a b d0) a) ⊒ .int w a := by
  cases a with
  | poison => simp [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, const_negOne]
  | val a =>
    cases b with
    | poison => simp [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, const_negOne]
    | val b =>
      all_goals by_cases h0 : d0 = true ∧ (a &&& b) ≠ 0
      all_goals simp only [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, Id.run, pure]
      all_goals simp only [h0, ↓reduceIte]
      all_goals simp [RuntimeValue.isRefinedBy, isRefinedBy, const_negOne]
      all_goals (try split at * <;> simp_all [RuntimeValue.isRefinedBy, isRefinedBy, const_negOne])
      all_goals (try split at * <;> simp_all [RuntimeValue.isRefinedBy, isRefinedBy, const_negOne])
      all_goals (try split at * <;> simp_all [RuntimeValue.isRefinedBy, isRefinedBy, const_negOne])
      all_goals (try split at * <;> simp_all [RuntimeValue.isRefinedBy, isRefinedBy, const_negOne])
      all_goals (try split at * <;> simp_all [RuntimeValue.isRefinedBy, isRefinedBy, const_negOne])
      all_goals (try split at * <;> simp_all [RuntimeValue.isRefinedBy, isRefinedBy, const_negOne])
      all_goals
        apply BitVec.eq_of_getLsbD_eq
        intro i h
        simp [h]
        try grind only

theorem valid (sw0 sw1 : Bool) : Pattern.Valid (pattern sw0 sw1) := by
  cases sw0 <;> cases sw1
  all_goals
    simp only [pattern, matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ a b
    intro abp abv abh
    obtain rfl := (or_iff _ _ _ _ _).mp abh
    intro rp rv rh
    obtain rfl := (and_iff _ _ _ _ _).mp rh
    simpa only [logic_and_comm, logic_or_comm, logic_xor_comm] using semantic _ a b abp.disjoint
end Veir.InstSimplify.IS2028
