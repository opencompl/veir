import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1057

/-- Scalar LLVM sdiv poison divisor branch, including its modeled UB behavior. -/
def pattern_sdiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .sdiv) #[x,c] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun x => x)

theorem pattern_sdiv_valid : Pattern.Valid pattern_sdiv := by
  simp only [pattern_sdiv, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain ⟨hu, rfl⟩ := (sdiv_iff w p x _ v).mp hi
  simp [LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB] at hu

/-- The matched source executes immediate UB, rather than an unsupported-op failure. -/
theorem sdiv_source_ub {s : IntegerType.Signedness} (w : Nat)
    (p : propertiesOf (.llvm .sdiv : OpCode)) (x : LLVM.Int w) (m : MemoryState) :
    interpretOp' (.llvm .sdiv) p #[IntegerType.mk w s] #[.int w x, .int w (.poison)] #[] m = .ub none := by
  simp [interpretOp', Llvm.interpretOp', LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB]

/-- Scalar LLVM udiv poison divisor branch, including its modeled UB behavior. -/
def pattern_udiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .udiv) #[x,c] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun x => x)

theorem pattern_udiv_valid : Pattern.Valid pattern_udiv := by
  simp only [pattern_udiv, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain ⟨hu, rfl⟩ := (udiv_iff w p x _ v).mp hi
  simp [LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB] at hu

/-- The matched source executes immediate UB, rather than an unsupported-op failure. -/
theorem udiv_source_ub {s : IntegerType.Signedness} (w : Nat)
    (p : propertiesOf (.llvm .udiv : OpCode)) (x : LLVM.Int w) (m : MemoryState) :
    interpretOp' (.llvm .udiv) p #[IntegerType.mk w s] #[.int w x, .int w (.poison)] #[] m = .ub none := by
  simp [interpretOp', Llvm.interpretOp', LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB]

/-- Scalar LLVM srem poison divisor branch, including its modeled UB behavior. -/
def pattern_srem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .srem) #[x,c] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun x => x)

theorem pattern_srem_valid : Pattern.Valid pattern_srem := by
  simp only [pattern_srem, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain ⟨hu, rfl⟩ := (srem_iff w p x _ v).mp hi
  simp [LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB] at hu

/-- The matched source executes immediate UB, rather than an unsupported-op failure. -/
theorem srem_source_ub {s : IntegerType.Signedness} (w : Nat)
    (p : propertiesOf (.llvm .srem : OpCode)) (x : LLVM.Int w) (m : MemoryState) :
    interpretOp' (.llvm .srem) p #[IntegerType.mk w s] #[.int w x, .int w (.poison)] #[] m = .ub none := by
  simp [interpretOp', Llvm.interpretOp', LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB]

/-- Scalar LLVM urem poison divisor branch, including its modeled UB behavior. -/
def pattern_urem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchPoison ty
      let _ ← MatchProg.root (.llvm .urem) #[x,c] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun x => x)

theorem pattern_urem_valid : Pattern.Valid pattern_urem := by
  simp only [pattern_urem, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc
  obtain rfl := (poison_iff _ cp cv).mp hc
  intro p v hi
  obtain ⟨hu, rfl⟩ := (urem_iff w p x _ v).mp hi
  simp [LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB] at hu

/-- The matched source executes immediate UB, rather than an unsupported-op failure. -/
theorem urem_source_ub {s : IntegerType.Signedness} (w : Nat)
    (p : propertiesOf (.llvm .urem : OpCode)) (x : LLVM.Int w) (m : MemoryState) :
    interpretOp' (.llvm .urem) p #[IntegerType.mk w s] #[.int w x, .int w (.poison)] #[] m = .ub none := by
  simp [interpretOp', Llvm.interpretOp', LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB]
end Veir.InstSimplify.IS1057
