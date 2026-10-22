import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem IS2430_semantic (w : Nat) (a b c : LLVM.Int w) (exact d : Bool) :
    RuntimeValue.int w (LLVM.Int.or (LLVM.Int.fshr a b c) (LLVM.Int.lshr b c exact) d) ⊒ .int w (LLVM.Int.fshr a b c) := by
  cases a <;> cases b <;> cases c
  all_goals try (solve | simp [LLVM.Int.fshr, LLVM.Int.lshr, LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run])
  rename_i a b c
  have hc : LLVM.Int.lshr (.val b) (.val c) exact = .poison ∨
      LLVM.Int.lshr (.val b) (.val c) exact = .val (b >>> c) := by
    simp only [LLVM.Int.lshr, Id.run, pure]
    repeat' split <;> simp_all
    all_goals grind
  rcases hc with hc | hc
  · rw [hc]
    simp [LLVM.Int.fshr, LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · have hs : c.toNat < w := by
      by_cases hlt : c.toNat < w
      · exact hlt
      · have hg : BitVec.ofNat w w ≤ c := by
          simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_two_pow_self]
          omega
        have he := hc
        simp [LLVM.Int.lshr, hg, Id.run, pure] at he
    rw [hc]
    have hraw : ((a ++ b) >>> c.toNat).truncate w ||| (b >>> c) = ((a ++ b) >>> c.toNat).truncate w := by
      rw [funnel_right_decompose a b c.toNat hs]
      simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp only [BitVec.getLsbD_or]
      grind
    simp only [LLVM.Int.fshr, LLVM.Int.or, Id.run, pure, Nat.mod_eq_of_lt hs]
    split
    · simp [RuntimeValue.isRefinedBy, isRefinedBy]
    · simpa [RuntimeValue.isRefinedBy, isRefinedBy] using hraw

def IS2430 (swap : Bool := false) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let c ← MatchProg.value ty
    let f ← MatchProg.operation (.llvm .intr__fshr) #[a,b,c] #[ty]
    let sh ← MatchProg.operation (.llvm .lshr) #[b,c] #[ty]
    let _ ← MatchProg.root (.llvm .or) (match swap with | false => #[f.res[0]!,sh.res[0]!] | true => #[sh.res[0]!,f.res[0]!]) #[ty]
    return f.res[0]!)
  pure (fun x => x)
theorem IS2430_valid (swap : Bool := false) : Pattern.Valid (IS2430 swap) := by
  cases swap
  all_goals
    simp only [IS2430]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro a b c
    rintro fp fv fi sp sv si rp rv ri
    obtain rfl := (fshr_iff _ _ _ _ _ _).mp fi
    obtain rfl := (lshr_iff _ _ _ _ _).mp si
    obtain rfl := (or_iff _ _ _ _ _).mp ri
    first
    | exact IS2430_semantic _ _ _ _ sp.exact rp.disjoint
    | rw [logic_or_comm]
      exact IS2430_semantic _ _ _ _ sp.exact rp.disjoint
end Veir.InstSimplify
