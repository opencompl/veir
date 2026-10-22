import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1417
private theorem shifted_arith_logical (x : BitVec w) (n : Nat) :
    (x.sshiftRight n) <<< n = (x >>> n) <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight]
  grind

def pattern_lshr : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let a ← MatchProg.value ty
      let sh ← MatchProg.operation (.llvm .lshr) #[x,a] #[ty] (fun p => p.exact)
      let _ ← MatchProg.root (.llvm .shl) #[sh.res[0]!,a] #[ty]
      return x)
    pure (fun x => x)

private theorem cancel_lshr (x a : LLVM.Int w) (p : NswNuwProperties) :
    RuntimeValue.int w (LLVM.Int.shl (LLVM.Int.lshr x a true) a p.nsw p.nuw) ⊒ .int w x := by
  cases x <;> cases a <;>
    simp [LLVM.Int.lshr, LLVM.Int.shl, Id.run, pure,
      RuntimeValue.isRefinedBy, isRefinedBy, BitVec.sshiftRight_eq', shifted_arith_logical]
  grind

theorem pattern_lshr_valid : Pattern.Valid pattern_lshr := by
  simp only [pattern_lshr]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x a sp sv hs hp rp rv hr
  obtain rfl := (lshr_iff w sp x a sv).mp hp
  obtain rfl := (shl_iff w rp _ a rv).mp hr
  rw [hs]
  exact cancel_lshr _ _ _

def pattern_ashr : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let a ← MatchProg.value ty
      let sh ← MatchProg.operation (.llvm .ashr) #[x,a] #[ty] (fun p => p.exact)
      let _ ← MatchProg.root (.llvm .shl) #[sh.res[0]!,a] #[ty]
      return x)
    pure (fun x => x)

private theorem cancel_ashr (x a : LLVM.Int w) (p : NswNuwProperties) :
    RuntimeValue.int w (LLVM.Int.shl (LLVM.Int.ashr x a true) a p.nsw p.nuw) ⊒ .int w x := by
  cases x <;> cases a <;>
    simp [LLVM.Int.ashr, LLVM.Int.shl, Id.run, pure,
      RuntimeValue.isRefinedBy, isRefinedBy, BitVec.sshiftRight_eq', shifted_arith_logical]
  grind

theorem pattern_ashr_valid : Pattern.Valid pattern_ashr := by
  simp only [pattern_ashr]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x a sp sv hs hp rp rv hr
  obtain rfl := (ashr_iff w sp x a sv).mp hp
  obtain rfl := (shl_iff w rp _ a rv).mp hr
  rw [hs]
  exact cancel_ashr _ _ _
end Veir.InstSimplify.IS1417
