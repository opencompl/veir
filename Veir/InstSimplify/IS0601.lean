import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0601

/-- Scalar LLVM add simplification with poison on the right; all widths and flags. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .add) #[x,c] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_valid : Pattern.Valid pattern := by
  simp only [pattern, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain rfl := (add_iff w p x _ v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy, Id.run, pure]
  all_goals grind

/-- Scalar LLVM add simplification with poison on the right; all widths and flags. -/
def pattern_left : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .add) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_left_valid : Pattern.Valid pattern_left := by
  simp only [pattern_left, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain rfl := (add_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy, Id.run, pure]
  all_goals grind

end Veir.InstSimplify.IS0601
