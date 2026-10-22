import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2086

/-- Scalar LLVM rule from upstream InstructionSimplify.cpp at 2086. -/
def pattern (sw0 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let r ← MatchProg.root (.llvm .and) (cond sw0 #[a, a] #[a, a]) #[ty]
    return a)
  pure (fun x => x)

theorem semantic (w : Nat) (a : LLVM.Int w)  :
    RuntimeValue.int w (LLVM.Int.and a a) ⊒ .int w a := by
  cases a with
  | poison => simp [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, const_negOne]
  | val a =>
    all_goals simp only [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, Id.run, pure]
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

theorem valid (sw0 : Bool) : Pattern.Valid (pattern sw0) := by
  cases sw0
  all_goals
    simp only [pattern, matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ a
    intro rp rv rh
    obtain rfl := (and_iff _ _ _ _ _).mp rh
    simpa only [logic_and_comm, logic_or_comm, logic_xor_comm] using semantic _ a
end Veir.InstSimplify.IS2086
