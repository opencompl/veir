import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2580

/-- Scalar LLVM rule from upstream InstructionSimplify.cpp at 2580. -/
def pattern (sw0 sw1 sw2 sw3 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let c ← matchBitConstant ty (-1)
    let na ← MatchProg.operation (.llvm .xor) (cond sw0 #[c, a] #[a, c]) #[ty]
    let x ← MatchProg.operation (.llvm .and) (cond sw1 #[b, na.res[0]!] #[na.res[0]!, b]) #[ty]
    let y ← MatchProg.operation (.llvm .or) (cond sw2 #[b, a] #[a, b]) #[ty]
    let r ← MatchProg.root (.llvm .xor) (cond sw3 #[y.res[0]!, x.res[0]!] #[x.res[0]!, y.res[0]!]) #[ty]
    return a)
  pure (fun x => x)

theorem semantic (w : Nat) (a b : LLVM.Int w) (d0 : Bool) :
    RuntimeValue.int w (LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) b) (LLVM.Int.or a b d0)) ⊒ .int w a := by
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

theorem valid (sw0 sw1 sw2 sw3 : Bool) : Pattern.Valid (pattern sw0 sw1 sw2 sw3) := by
  cases sw0 <;> cases sw1 <;> cases sw2 <;> cases sw3
  all_goals
    simp only [pattern, matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ a b
    intro cp cv hi
    intro nap nav nah
    intro xp xv xh
    intro yp yv yh
    intro rp rv rh
    intro hc
    obtain rfl := matched_bit_constant_eq _ _ (-1) _ hi hc
    obtain rfl := (xor_iff _ _ _ _ _).mp nah
    obtain rfl := (and_iff _ _ _ _ _).mp xh
    obtain rfl := (or_iff _ _ _ _ _).mp yh
    obtain rfl := (xor_iff _ _ _ _ _).mp rh
    simpa only [logic_and_comm, logic_or_comm, logic_xor_comm] using semantic _ a b yp.disjoint
end Veir.InstSimplify.IS2580
