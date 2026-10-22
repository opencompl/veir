import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2024

/-- Scalar LLVM rule from upstream InstructionSimplify.cpp at 2024. -/
def pattern (sw0 sw1 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let c ← matchBitConstant ty (-1)
    let na ← MatchProg.operation (.llvm .xor) (cond sw0 #[c, a] #[a, c]) #[ty]
    let r ← MatchProg.root (.llvm .and) (cond sw1 #[a, na.res[0]!] #[na.res[0]!, a]) #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let z ← CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p
    return z.res[0]!) (fun x => x)

theorem semantic (w : Nat) (a : LLVM.Int w)  :
    RuntimeValue.int w (LLVM.Int.and (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) a) ⊒ .int w (.val 0) := by
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

theorem valid (sw0 sw1 : Bool) : Pattern.Valid (pattern sw0 sw1) := by
  cases sw0 <;> cases sw1
  all_goals
    simp only [pattern, matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ a
    intro cp cv hi
    intro nap nav nah
    intro rp rv rh
    intro hc
    obtain rfl := matched_bit_constant_eq _ _ (-1) _ hi hc
    obtain rfl := (xor_iff _ _ _ _ _).mp nah
    obtain rfl := (and_iff _ _ _ _ _).mp rh
    refine ⟨.int w (.val 0), ?_, ?_⟩
    · exact (zero_iff _ _ _).mpr rfl
    · simpa only [logic_and_comm, logic_or_comm, logic_xor_comm] using semantic _ a
end Veir.InstSimplify.IS2024
