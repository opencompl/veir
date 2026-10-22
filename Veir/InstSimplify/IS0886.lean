import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0886
private theorem nat_xor_lowmask (n k : Nat) (h : n < 2^k) : n ^^^ (2^k-1) = 2^k-1-n := by
  have hx := BitVec.toNat_not (x := BitVec.ofNat k n)
  rw [BitVec.not_def] at hx
  simp only [BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at hx
  simpa only [Nat.xor_comm] using hx

private theorem lowmask_cancel (x m : BitVec w) (k : Nat) (hm : m.toNat = 2^k-1)
    (hn : (x ^^^ m).toNat ≤ m.toNat) : m - (x ^^^ m) = x := by
  have hp := Nat.two_pow_pos k
  have hylt : (x ^^^ m).toNat < 2^k := by omega
  have hxdiv := Nat.div_eq_of_lt hylt
  rw [BitVec.toNat_xor, Nat.xor_div_two_pow, hm, Nat.div_eq_of_lt (show 2^k-1<2^k by omega), Nat.xor_zero] at hxdiv
  have hxlt : x.toNat < 2^k := by
    have h := (Nat.div_eq_zero_iff).mp hxdiv
    omega
  have heq : (x ^^^ m).toNat = m.toNat - x.toNat := by
    rw [BitVec.toNat_xor, hm, nat_xor_lowmask _ _ hxlt]
  have hxle : x.toNat ≤ m.toNat := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_not_usubOverflow]
  · omega
  · simp only [BitVec.usubOverflow, decide_eq_true_eq]
    exact Nat.not_lt.mpr hn
private theorem refines (x : LLVM.Int w) (m : BitVec w) (k : Nat)
    (hm : m.toNat = 2^k-1) (ns : Bool) :
    RuntimeValue.int w (LLVM.Int.sub (.val m) (LLVM.Int.xor x (.val m)) ns true) ⊒ .int w x := by
  cases x <;> simp [LLVM.Int.sub, LLVM.Int.xor, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [lowmask_cancel, BitVec.usubOverflow]

/-- sub nuw lowmask,(xor X,lowmask) → X. -/
def pattern (n : Int) (k : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty n
      let xr ← MatchProg.operation (.llvm .xor) #[x,c] #[ty]
      let _ ← MatchProg.root (.llvm .sub) #[c,xr.res[0]!] #[ty] (fun p => p.nuw)
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => decide (0 < k ∧ k ≤ it.bitwidth) &&
            ((BitVec.ofInt it.bitwidth n).toNat == 2^k-1)
        | _ => false)
      return x)
    pure (fun x => x)

theorem valid (n : Int) (k : Nat) : Pattern.Valid (pattern n k) := by
  simp only [pattern, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc xp xv hx p v hp hi hz hg
  obtain rfl := matched_bit_constant_eq _ cp n cv hc hz
  obtain rfl := (xor_iff w xp x _ xv).mp hx
  obtain rfl := (sub_iff w p _ _ v).mp hi
  change (decide (0 < k ∧ k ≤ w) && ((BitVec.ofInt w n).toNat == 2^k-1)) = true at hg
  have hg' : (0 < k ∧ k ≤ w) ∧ (BitVec.ofInt w n).toNat = 2^k-1 := by simpa using hg
  rw [hp]
  exact refines _ _ _ hg'.2 _
end Veir.InstSimplify.IS0886
