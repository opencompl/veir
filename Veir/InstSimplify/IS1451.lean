import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1451
/-- Right shift cancels the matching no-wrap left shift; arbitrary scalar widths. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let a ← MatchProg.value ty
      let sh ← MatchProg.operation (.llvm .shl) #[x,a] #[ty] (fun p => p.nuw)
      let _ ← MatchProg.root (.llvm .lshr) #[sh.res[0]!,a] #[ty]
      return x)
    pure (fun x => x)

private theorem cancel (x a : LLVM.Int w) (p : NswNuwProperties) (ex : Bool)
    (h : p.nuw = true) :
    RuntimeValue.int w (LLVM.Int.lshr (LLVM.Int.shl x a p.nsw p.nuw) a ex) ⊒ .int w x := by
  cases x <;> cases a <;>
    simp [LLVM.Int.lshr, LLVM.Int.shl, Id.run, pure, h,
      RuntimeValue.isRefinedBy, isRefinedBy]
  grind

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x a sp sv hs hp rp rv hr
  obtain rfl := (shl_iff w sp x a sv).mp hp
  obtain rfl := (lshr_iff w rp _ a rv).mp hr
  exact cancel _ _ _ _ hs
end Veir.InstSimplify.IS1451
