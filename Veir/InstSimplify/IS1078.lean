import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1078

/-- Scalar LLVM sdiv zero dividend branch, including its modeled UB behavior. -/
def pattern_sdiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .sdiv) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_sdiv_valid : Pattern.Valid pattern_sdiv := by
  simp only [pattern_sdiv, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain ⟨hu, rfl⟩ := (sdiv_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, isRefinedBy, Id.run, pure] at *
  all_goals grind

/-- Scalar LLVM udiv zero dividend branch, including its modeled UB behavior. -/
def pattern_udiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .udiv) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_udiv_valid : Pattern.Valid pattern_udiv := by
  simp only [pattern_udiv, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain ⟨hu, rfl⟩ := (udiv_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.udiv,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, isRefinedBy, Id.run, pure] at *
  all_goals grind

/-- Scalar LLVM srem zero dividend branch, including its modeled UB behavior. -/
def pattern_srem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .srem) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_srem_valid : Pattern.Valid pattern_srem := by
  simp only [pattern_srem, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain ⟨hu, rfl⟩ := (srem_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.srem,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, isRefinedBy, Id.run, pure] at *
  all_goals grind

/-- Scalar LLVM urem zero dividend branch, including its modeled UB behavior. -/
def pattern_urem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .urem) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_urem_valid : Pattern.Valid pattern_urem := by
  simp only [pattern_urem, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain ⟨hu, rfl⟩ := (urem_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.urem,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, isRefinedBy, Id.run, pure] at *
  all_goals grind
end Veir.InstSimplify.IS1078
