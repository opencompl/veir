import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1083

def pattern_sdiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .sdiv) #[x,x] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.applyNative ty (fun ty => match ty.val with
        | .integerType it => some ({ value := .integer { type := it, value := 1 } } : LLVMConstantProperties)
        | _ => none)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_sdiv_valid : Pattern.Valid pattern_sdiv := by
  simp only [pattern_sdiv]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x p v hi
  obtain ⟨hu, rfl⟩ := (sdiv_iff w p x x v).mp hi
  exists (.int w (.val (BitVec.ofNat w 1)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp)
  · cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv,
      LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB,
      isRefinedBy, Id.run, pure] at *
    all_goals grind

def pattern_udiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .udiv) #[x,x] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.applyNative ty (fun ty => match ty.val with
        | .integerType it => some ({ value := .integer { type := it, value := 1 } } : LLVMConstantProperties)
        | _ => none)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_udiv_valid : Pattern.Valid pattern_udiv := by
  simp only [pattern_udiv]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x p v hi
  obtain ⟨hu, rfl⟩ := (udiv_iff w p x x v).mp hi
  exists (.int w (.val (BitVec.ofNat w 1)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp)
  · cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.udiv,
      LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB,
      isRefinedBy, Id.run, pure] at *
    all_goals grind

def pattern_srem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .srem) #[x,x] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_srem_valid : Pattern.Valid pattern_srem := by
  simp only [pattern_srem]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x p v hi
  obtain ⟨hu, rfl⟩ := (srem_iff w p x x v).mp hi
  exists (.int w (.val (BitVec.ofNat w 0)))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.srem,
      LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB,
      isRefinedBy, Id.run, pure] at *
    all_goals grind

def pattern_urem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .urem) #[x,x] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_urem_valid : Pattern.Valid pattern_urem := by
  simp only [pattern_urem]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x p v hi
  obtain ⟨hu, rfl⟩ := (urem_iff w p x x v).mp hi
  exists (.int w (.val (BitVec.ofNat w 0)))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.urem,
      LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB,
      isRefinedBy, Id.run, pure] at *
    all_goals grind
end Veir.InstSimplify.IS1083
