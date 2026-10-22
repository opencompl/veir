import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0609
/-- LLVM InstSimplify: X + 0 → X, at every scalar integer width and all flags. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let z ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .add) #[x,z] #[ty]
      return x)
    pure (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain rfl := (add_iff w p x _ v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy, Id.run, pure]
  grind
/-- LLVM InstSimplify: X + 0 → X, at every scalar integer width and all flags. -/
def pattern_left : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let z ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .add) #[z,x] #[ty]
      return x)
    pure (fun x => x)

theorem valid_left : Pattern.Valid pattern_left := by
  simp only [pattern_left, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain rfl := (add_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy, Id.run, pure]
  grind
end Veir.InstSimplify.IS0609
