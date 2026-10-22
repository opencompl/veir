import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1189
private theorem signed_shift_remainder (x : BitVec w) (n : Nat) (hn : n ≤ w)
    (hs : (x <<< n).sshiftRight n = x) : (x <<< n).srem x = 0 := by
  have hpow : (2^n : Int) ∣ (2^w : Nat) := by
    exact_mod_cast Nat.pow_dvd_pow 2 hn
  have hmod : (2^n : Int) ∣ (x <<< n).toInt := by
    rw [BitVec.toInt_shiftLeft]
    have hd := Int.dvd_trans hpow (Int.dvd_bmod_sub_self (x := (x.toNat <<< n : Nat)) (m := 2^w))
    have hxn : 2^n ∣ x.toNat <<< n := by
      rw [Nat.shiftLeft_eq]
      exact Nat.dvd_mul_left _ _
    have hx : (2^n : Int) ∣ (x.toNat <<< n : Nat) := by
      exact_mod_cast hxn
    have hh := Int.dvd_add hd hx
    simpa only [Int.sub_add_cancel] using hh
  have hq := congrArg BitVec.toInt hs
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow] at hq
  norm_cast at hq
  have hm := Int.ediv_mul_cancel hmod
  norm_cast at hm
  rw [hq] at hm
  apply BitVec.srem_zero_of_dvd
  rw [← hm]
  exact Int.dvd_mul_right _ _
private theorem unsigned_shift_remainder (x : BitVec w) (n : Nat) (hn : n ≤ w)
    (hs : (x <<< n) >>> n = x) : (x <<< n) % x = 0 := by
  have hmod : (x <<< n).toNat % 2^n = 0 := by
    rw [BitVec.toNat_shiftLeft, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn), Nat.shiftLeft_eq]
    simp
  have hq := congrArg BitVec.toNat hs
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hq
  have hm := Nat.mod_add_div (x <<< n).toNat (2^n)
  rw [hmod, Nat.zero_add, hq] at hm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, ← hm]
  simp

private theorem refines_srem (x a : LLVM.Int w) (nu : Bool) :
    RuntimeValue.int w (LLVM.Int.srem (LLVM.Int.shl x a true nu) x) ⊒ .int w (.val 0) := by
  have hw : w % 2^w = w := Nat.mod_eq_of_lt Nat.lt_two_pow_self
  cases x <;> cases a <;> simp [LLVM.Int.shl, LLVM.Int.srem, Id.run, pure, RuntimeValue.isRefinedBy,
    isRefinedBy, BitVec.le_def, BitVec.toNat_ofNat, hw, BitVec.sshiftRight_eq']
  grind [signed_shift_remainder]

def pattern_srem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let a ← MatchProg.value ty
      let sh ← MatchProg.operation (.llvm .shl) #[x,a] #[ty] (fun p => p.nsw)
      let _ ← MatchProg.root (.llvm .srem) #[sh.res[0]!,x] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_srem_valid : Pattern.Valid pattern_srem := by
  simp only [pattern_srem]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x a sp sv hp hs p v hi
  obtain rfl := (shl_iff w sp x a sv).mp hs
  obtain ⟨hu,rfl⟩ := (srem_iff w p _ x v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hp]
    exact refines_srem _ _ _

private theorem refines_urem (x a : LLVM.Int w) (ns : Bool) :
    RuntimeValue.int w (LLVM.Int.urem (LLVM.Int.shl x a ns true) x) ⊒ .int w (.val 0) := by
  have hw : w % 2^w = w := Nat.mod_eq_of_lt Nat.lt_two_pow_self
  cases x <;> cases a <;> simp [LLVM.Int.shl, LLVM.Int.urem, Id.run, pure, RuntimeValue.isRefinedBy,
    isRefinedBy, BitVec.le_def, BitVec.toNat_ofNat, hw, BitVec.sshiftRight_eq']
  grind [unsigned_shift_remainder]

def pattern_urem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let a ← MatchProg.value ty
      let sh ← MatchProg.operation (.llvm .shl) #[x,a] #[ty] (fun p => p.nuw)
      let _ ← MatchProg.root (.llvm .urem) #[sh.res[0]!,x] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_urem_valid : Pattern.Valid pattern_urem := by
  simp only [pattern_urem]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x a sp sv hp hs p v hi
  obtain rfl := (shl_iff w sp x a sv).mp hs
  obtain ⟨hu,rfl⟩ := (urem_iff w p _ x v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hp]
    exact refines_urem _ _ _
end Veir.InstSimplify.IS1189
