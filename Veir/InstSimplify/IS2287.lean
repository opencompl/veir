import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2287

/-- Scalar LLVM rule from upstream InstructionSimplify.cpp at 2287. -/
def pattern (sw0 sw1 sw2 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let x ← MatchProg.operation (.llvm .xor) (cond sw0 #[b, a] #[a, b]) #[ty]
    let y ← MatchProg.operation (.llvm .or) (cond sw1 #[b, a] #[a, b]) #[ty]
    let r ← MatchProg.root (.llvm .or) (cond sw2 #[y.res[0]!, x.res[0]!] #[x.res[0]!, y.res[0]!]) #[ty]
    return y.res[0]!)
  pure (fun x => x)

theorem semantic (w : Nat) (a b : LLVM.Int w) (d0 d1 : Bool) :
    RuntimeValue.int w (LLVM.Int.or (LLVM.Int.xor a b) (LLVM.Int.or a b d0) d1) ⊒ .int w (LLVM.Int.or a b d0) := by
  cases a with
  | poison => simp [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, const_negOne]
  | val a =>
    cases b with
    | poison => simp [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, const_negOne]
    | val b =>
      all_goals by_cases h0 : d0 = true ∧ (a &&& b) ≠ 0
      all_goals by_cases h1 : d1 = true ∧ ((a ^^^ b) &&& (a ||| b)) ≠ 0
      all_goals simp only [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, Id.run, pure]
      all_goals simp only [h0, h1, ↓reduceIte]
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

theorem valid (sw0 sw1 sw2 : Bool) : Pattern.Valid (pattern sw0 sw1 sw2) := by
  cases sw0 <;> cases sw1 <;> cases sw2
  all_goals
    simp only [pattern, matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ a b
    intro xp xv xh
    obtain rfl := (xor_iff _ _ _ _ _).mp xh
    intro yp yv yh
    obtain rfl := (or_iff _ _ _ _ _).mp yh
    intro rp rv rh
    obtain rfl := (or_iff _ _ _ _ _).mp rh
    simpa only [logic_and_comm, logic_or_comm, logic_xor_comm] using semantic _ a b yp.disjoint rp.disjoint
end Veir.InstSimplify.IS2287
