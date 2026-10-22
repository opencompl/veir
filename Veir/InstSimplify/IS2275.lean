import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2275

/-- Scalar LLVM rule from upstream InstructionSimplify.cpp at 2275. -/
def pattern (sw0 sw1 sw2 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let c ← matchBitConstant ty (-1)
    let ab ← MatchProg.operation (.llvm .and) (cond sw0 #[b, a] #[a, b]) #[ty]
    let nab ← MatchProg.operation (.llvm .xor) (cond sw1 #[c, ab.res[0]!] #[ab.res[0]!, c]) #[ty]
    let r ← MatchProg.root (.llvm .or) (cond sw2 #[nab.res[0]!, a] #[a, nab.res[0]!]) #[ty]
    return c)
  pure (fun x => x)

theorem semantic (w : Nat) (a b : LLVM.Int w) (d0 : Bool) :
    RuntimeValue.int w (LLVM.Int.or a (LLVM.Int.xor (LLVM.Int.and a b) (.val (BitVec.ofInt w (-1)))) d0) ⊒ .int w (.val (BitVec.ofInt w (-1))) := by
  cases a with
  | poison => simp [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, const_negOne]
  | val a =>
    cases b with
    | poison => simp [LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, const_negOne]
    | val b =>
      all_goals by_cases h0 : d0 = true ∧ (a &&& ((a &&& b) ^^^ (BitVec.ofInt w (-1)))) ≠ 0
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

theorem valid (sw0 sw1 sw2 : Bool) : Pattern.Valid (pattern sw0 sw1 sw2) := by
  cases sw0 <;> cases sw1 <;> cases sw2
  all_goals
    simp only [pattern, matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ a b
    intro cp cv hi
    intro abp abv abh
    intro nabp nabv nabh
    intro rp rv rh
    intro hc
    obtain rfl := matched_bit_constant_eq _ _ (-1) _ hi hc
    obtain rfl := (and_iff _ _ _ _ _).mp abh
    obtain rfl := (xor_iff _ _ _ _ _).mp nabh
    obtain rfl := (or_iff _ _ _ _ _).mp rh
    simpa only [logic_and_comm, logic_or_comm, logic_xor_comm] using semantic _ a b rp.disjoint
end Veir.InstSimplify.IS2275
