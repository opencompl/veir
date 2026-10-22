import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1310

/-- Scalar LLVM shl simplification with poison on the left; all widths and flags. -/
def pattern_shl_left : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .shl) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_shl_left_valid : Pattern.Valid pattern_shl_left := by
  simp only [pattern_shl_left, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain rfl := (shl_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.shl, isRefinedBy, Id.run, pure]
  all_goals grind

/-- Scalar LLVM lshr simplification with poison on the left; all widths and flags. -/
def pattern_lshr_left : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .lshr) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_lshr_left_valid : Pattern.Valid pattern_lshr_left := by
  simp only [pattern_lshr_left, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain rfl := (lshr_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run, pure]
  all_goals grind

/-- Scalar LLVM ashr simplification with poison on the left; all widths and flags. -/
def pattern_ashr_left : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .ashr) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_ashr_left_valid : Pattern.Valid pattern_ashr_left := by
  simp only [pattern_ashr_left, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain rfl := (ashr_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run, pure]
  all_goals grind

end Veir.InstSimplify.IS1310
