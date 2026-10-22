import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1068

/-- Scalar LLVM sdiv poison dividend branch, including its modeled UB behavior. -/
def pattern_sdiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .sdiv) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_sdiv_valid : Pattern.Valid pattern_sdiv := by
  simp only [pattern_sdiv, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain ⟨hu, rfl⟩ := (sdiv_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, isRefinedBy, Id.run, pure] at *
  all_goals grind

/-- Scalar LLVM udiv poison dividend branch, including its modeled UB behavior. -/
def pattern_udiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .udiv) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_udiv_valid : Pattern.Valid pattern_udiv := by
  simp only [pattern_udiv, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain ⟨hu, rfl⟩ := (udiv_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.udiv,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, isRefinedBy, Id.run, pure] at *
  all_goals grind

/-- Scalar LLVM srem poison dividend branch, including its modeled UB behavior. -/
def pattern_srem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .srem) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_srem_valid : Pattern.Valid pattern_srem := by
  simp only [pattern_srem, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain ⟨hu, rfl⟩ := (srem_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.srem,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, isRefinedBy, Id.run, pure] at *
  all_goals grind

/-- Scalar LLVM urem poison dividend branch, including its modeled UB behavior. -/
def pattern_urem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .urem) #[c,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_urem_valid : Pattern.Valid pattern_urem := by
  simp only [pattern_urem, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain ⟨hu, rfl⟩ := (urem_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.urem,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, isRefinedBy, Id.run, pure] at *
  all_goals grind
end Veir.InstSimplify.IS1068
