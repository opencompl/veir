import Veir.InstSimplify.LogicExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
 theorem lowmask_sub_xor (x m : BitVec w) (k : Nat) (hk : k ≤ w)
    (hm : m = (BitVec.allOnes k).zeroExtend w) (hle : x ≤ m) : (m-x) ^^^ m = x := by
  have hpow : 2^k ≤ 2^w := Nat.pow_le_pow_right (by decide) hk
  have hpos : 0 < 2^k := Nat.two_pow_pos k
  have hmod : 2^k - 1 < 2^w := by omega
  have hmnat : m.toNat = 2^k - 1 := by
    rw [hm]
    simp [BitVec.toNat_setWidth,Nat.mod_eq_of_lt hmod]
  have hle' : x.toNat ≤ m.toNat := hle
  have hxsmall : x.toNat < 2^k := by omega
  let xk : BitVec k := BitVec.ofNat k x.toNat
  have hxk : xk.toNat = x.toNat := by simp [xk,Nat.mod_eq_of_lt hxsmall]
  have hxdef : x = xk.zeroExtend w := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth,hxk,Nat.mod_eq_of_lt x.isLt]
  have hd : m-x = (~~~xk).zeroExtend w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hle]
    simp only [BitVec.toNat_setWidth,BitVec.toNat_not,hxk,hmnat]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hd,hm,← BitVec.setWidth_xor]
  simpa [BitVec.xor_allOnes,BitVec.not_not] using hxdef.symm
end Veir.InstSimplify
