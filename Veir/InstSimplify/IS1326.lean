import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1326

/-- Constant shift count at least the scalar width produces poison. -/
def pattern_shl (n : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty n
      let _ ← MatchProg.root (.llvm .shl) #[x,c] #[ty]
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => decide (it.bitwidth ≤ (BitVec.ofInt it.bitwidth n).toNat)
        | _ => false)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_shl_valid (n : Int) : Pattern.Valid (pattern_shl n) := by
  simp only [pattern_shl, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz hn
  obtain rfl := matched_bit_constant_eq _ cp n cv hc hz
  obtain rfl := (shl_iff w p x _ v).mp hi
  change decide (w ≤ (BitVec.ofInt w n).toNat) = true at hn
  have hn' : w ≤ (BitVec.ofInt w n).toNat := by simpa using hn
  have h : BitVec.ofNat w w ≤ BitVec.ofInt w n := by
    rw [BitVec.le_def]
    have hm := Nat.mod_le w (2^w)
    simp only [BitVec.toNat_ofNat]
    omega
  exists (.int w .poison)
  constructor
  · exact (poison_iff _ _ _).mpr rfl
  · cases x <;> simp [LLVM.Int.shl, Id.run, pure, h, RuntimeValue.isRefinedBy, isRefinedBy]

/-- Constant shift count at least the scalar width produces poison. -/
def pattern_lshr (n : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty n
      let _ ← MatchProg.root (.llvm .lshr) #[x,c] #[ty]
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => decide (it.bitwidth ≤ (BitVec.ofInt it.bitwidth n).toNat)
        | _ => false)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_lshr_valid (n : Int) : Pattern.Valid (pattern_lshr n) := by
  simp only [pattern_lshr, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz hn
  obtain rfl := matched_bit_constant_eq _ cp n cv hc hz
  obtain rfl := (lshr_iff w p x _ v).mp hi
  change decide (w ≤ (BitVec.ofInt w n).toNat) = true at hn
  have hn' : w ≤ (BitVec.ofInt w n).toNat := by simpa using hn
  have h : BitVec.ofNat w w ≤ BitVec.ofInt w n := by
    rw [BitVec.le_def]
    have hm := Nat.mod_le w (2^w)
    simp only [BitVec.toNat_ofNat]
    omega
  exists (.int w .poison)
  constructor
  · exact (poison_iff _ _ _).mpr rfl
  · cases x <;> simp [LLVM.Int.lshr, Id.run, pure, h, RuntimeValue.isRefinedBy, isRefinedBy]

/-- Constant shift count at least the scalar width produces poison. -/
def pattern_ashr (n : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty n
      let _ ← MatchProg.root (.llvm .ashr) #[x,c] #[ty]
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => decide (it.bitwidth ≤ (BitVec.ofInt it.bitwidth n).toNat)
        | _ => false)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_ashr_valid (n : Int) : Pattern.Valid (pattern_ashr n) := by
  simp only [pattern_ashr, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz hn
  obtain rfl := matched_bit_constant_eq _ cp n cv hc hz
  obtain rfl := (ashr_iff w p x _ v).mp hi
  change decide (w ≤ (BitVec.ofInt w n).toNat) = true at hn
  have hn' : w ≤ (BitVec.ofInt w n).toNat := by simpa using hn
  have h : BitVec.ofNat w w ≤ BitVec.ofInt w n := by
    rw [BitVec.le_def]
    have hm := Nat.mod_le w (2^w)
    simp only [BitVec.toNat_ofNat]
    omega
  exists (.int w .poison)
  constructor
  · exact (poison_iff _ _ _).mpr rfl
  · cases x <;> simp [LLVM.Int.ashr, Id.run, pure, h, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify.IS1326
