import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1063

/-- Scalar LLVM sdiv zero divisor branch, including its modeled UB behavior. -/
def pattern_sdiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .sdiv) #[x,c] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun x => x)

theorem pattern_sdiv_valid : Pattern.Valid pattern_sdiv := by
  simp only [pattern_sdiv, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain ⟨hu, rfl⟩ := (sdiv_iff w p x _ v).mp hi
  simp [LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB] at hu

/-- The matched source executes immediate UB, rather than an unsupported-op failure. -/
theorem sdiv_source_ub {s : IntegerType.Signedness} (w : Nat)
    (p : propertiesOf (.llvm .sdiv : OpCode)) (x : LLVM.Int w) (m : MemoryState) :
    interpretOp' (.llvm .sdiv) p #[IntegerType.mk w s] #[.int w x, .int w (.val (BitVec.ofInt w 0))] #[] m = .ub none := by
  simp [interpretOp', Llvm.interpretOp', LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB]

/-- Scalar LLVM udiv zero divisor branch, including its modeled UB behavior. -/
def pattern_udiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .udiv) #[x,c] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun x => x)

theorem pattern_udiv_valid : Pattern.Valid pattern_udiv := by
  simp only [pattern_udiv, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain ⟨hu, rfl⟩ := (udiv_iff w p x _ v).mp hi
  simp [LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB] at hu

/-- The matched source executes immediate UB, rather than an unsupported-op failure. -/
theorem udiv_source_ub {s : IntegerType.Signedness} (w : Nat)
    (p : propertiesOf (.llvm .udiv : OpCode)) (x : LLVM.Int w) (m : MemoryState) :
    interpretOp' (.llvm .udiv) p #[IntegerType.mk w s] #[.int w x, .int w (.val (BitVec.ofInt w 0))] #[] m = .ub none := by
  simp [interpretOp', Llvm.interpretOp', LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB]

/-- Scalar LLVM srem zero divisor branch, including its modeled UB behavior. -/
def pattern_srem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .srem) #[x,c] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun x => x)

theorem pattern_srem_valid : Pattern.Valid pattern_srem := by
  simp only [pattern_srem, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain ⟨hu, rfl⟩ := (srem_iff w p x _ v).mp hi
  simp [LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB] at hu

/-- The matched source executes immediate UB, rather than an unsupported-op failure. -/
theorem srem_source_ub {s : IntegerType.Signedness} (w : Nat)
    (p : propertiesOf (.llvm .srem : OpCode)) (x : LLVM.Int w) (m : MemoryState) :
    interpretOp' (.llvm .srem) p #[IntegerType.mk w s] #[.int w x, .int w (.val (BitVec.ofInt w 0))] #[] m = .ub none := by
  simp [interpretOp', Llvm.interpretOp', LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB]

/-- Scalar LLVM urem zero divisor branch, including its modeled UB behavior. -/
def pattern_urem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .urem) #[x,c] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun x => x)

theorem pattern_urem_valid : Pattern.Valid pattern_urem := by
  simp only [pattern_urem, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain ⟨hu, rfl⟩ := (urem_iff w p x _ v).mp hi
  simp [LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB] at hu

/-- The matched source executes immediate UB, rather than an unsupported-op failure. -/
theorem urem_source_ub {s : IntegerType.Signedness} (w : Nat)
    (p : propertiesOf (.llvm .urem : OpCode)) (x : LLVM.Int w) (m : MemoryState) :
    interpretOp' (.llvm .urem) p #[IntegerType.mk w s] #[.int w x, .int w (.val (BitVec.ofInt w 0))] #[] m = .ub none := by
  simp [interpretOp', Llvm.interpretOp', LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB]
end Veir.InstSimplify.IS1063
