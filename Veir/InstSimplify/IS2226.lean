import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2226

/-- Scalar LLVM rule from upstream InstructionSimplify.cpp at 2226. -/
def pattern (sw0 sw1 sw2 sw3 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let ab ← MatchProg.operation (.llvm .or) (cond sw0 #[b, a] #[a, b]) #[ty]
    let x ← MatchProg.operation (.llvm .xor) (cond sw1 #[a, ab.res[0]!] #[ab.res[0]!, a]) #[ty]
    let y ← MatchProg.operation (.llvm .xor) (cond sw2 #[b, ab.res[0]!] #[ab.res[0]!, b]) #[ty]
    let r ← MatchProg.root (.llvm .and) (cond sw3 #[y.res[0]!, x.res[0]!] #[x.res[0]!, y.res[0]!]) #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let z ← CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p
    return z.res[0]!) (fun x => x)

theorem semantic (w : Nat) (a b : LLVM.Int w) (d0 : Bool) :
    RuntimeValue.int w (LLVM.Int.and (LLVM.Int.xor (LLVM.Int.or a b d0) a) (LLVM.Int.xor (LLVM.Int.or a b d0) b)) ⊒ .int w (.val 0) := by
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
    intro abp abv abh
    obtain rfl := (or_iff _ _ _ _ _).mp abh
    intro xp xv xh
    obtain rfl := (xor_iff _ _ _ _ _).mp xh
    intro yp yv yh
    obtain rfl := (xor_iff _ _ _ _ _).mp yh
    intro rp rv rh
    obtain rfl := (and_iff _ _ _ _ _).mp rh
    refine ⟨.int w (.val 0), ?_, ?_⟩
    · exact (zero_iff _ _ _).mpr rfl
    · simpa only [logic_and_comm, logic_or_comm, logic_xor_comm] using semantic _ a b abp.disjoint
end Veir.InstSimplify.IS2226
