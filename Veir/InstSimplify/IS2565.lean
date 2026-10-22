import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2565

/-- Scalar LLVM rule from upstream InstructionSimplify.cpp at 2565. -/
def pattern (sw0 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let c ← matchBitConstant ty (0)
    let r ← MatchProg.root (.llvm .xor) (cond sw0 #[c, a] #[a, c]) #[ty]
    return a)
  pure (fun x => x)

theorem semantic (w : Nat) (a : LLVM.Int w)  :
    RuntimeValue.int w (LLVM.Int.xor a (.val (BitVec.ofInt w (0)))) ⊒ .int w a := by
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
    intro cp cv hi
    intro rp rv rh
    intro hc
    obtain rfl := matched_bit_constant_eq _ _ (0) _ hi hc
    obtain rfl := (xor_iff _ _ _ _ _).mp rh
    simpa only [logic_and_comm, logic_or_comm, logic_xor_comm] using semantic _ a
end Veir.InstSimplify.IS2565
