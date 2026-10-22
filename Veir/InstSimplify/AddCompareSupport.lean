import Veir.InstSimplify.LogicExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

theorem logic_add_value_facts (a b r : BitVec w) (nsw nuw : Bool)
    (h : LLVM.Int.add (.val a) (.val b) nsw nuw = .val r) :
    r = a+b ∧ (nsw = true → BitVec.saddOverflow a b = false) ∧
      (nuw = true → BitVec.uaddOverflow a b = false) := by
  simp only [LLVM.Int.add,Id.run,pure] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem logic_toInt_le_nat (a : BitVec w) : a.toInt ≤ (a.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem logic_positive_toNat (a : BitVec w) (h : 0 ≤ a.toInt) : a.toInt = a.toNat := by
  have hh := BitVec.toInt_pos_iff.mp h
  exact BitVec.toInt_eq_toNat_of_lt hh

theorem logic_delta_toNat_bound (c d : BitVec w) (delta : Nat)
    (h : (d-c).toNat = delta) : d.toNat ≤ c.toNat + delta := by
  have hv : d-c = BitVec.ofNat w delta := by
    rw [← h]
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have hd := BitVec.sub_eq_iff_eq_add.mp hv
  rw [hd,BitVec.toNat_add]
  have hmod := Nat.mod_le delta (2^w)
  have hmod' := Nat.mod_le ((BitVec.ofNat w delta).toNat + c.toNat) (2^w)
  simp only [BitVec.toNat_ofNat] at hmod' ⊢
  omega

theorem logic_addcmp_unsigned_signed (a c d : BitVec w) (delta : Nat)
    (hc : 0 < c.toInt) (ha : c.toInt < a.toInt)
    (hd : (d-c).toNat = delta) :
    c.toNat + 2 ≤ (a+c).toNat ∧ d.toNat ≤ c.toNat + delta := by
  have hca := logic_positive_toNat c (by omega)
  have haa := logic_positive_toNat a (by omega)
  have hc2 := BitVec.toInt_pos_iff.mp (show 0 ≤ c.toInt by omega)
  have ha2 := BitVec.toInt_pos_iff.mp (show 0 ≤ a.toInt by omega)
  have hsum : a.toNat + c.toNat < 2^w := by omega
  rw [BitVec.toNat_add,Nat.mod_eq_of_lt hsum]
  constructor
  · omega
  · exact logic_delta_toNat_bound c d delta hd

theorem logic_addcmp_signed (a c d : BitVec w) (delta : Nat)
    (hc : 0 < c.toInt) (ha : c.toInt < a.toInt)
    (hd : (d-c).toNat = delta) (hf : BitVec.saddOverflow a c = false) :
    c.toInt + 2 ≤ (a+c).toInt ∧ d.toInt ≤ c.toInt + delta := by
  have hca := logic_positive_toNat c (by omega)
  have hbound := logic_delta_toNat_bound c d delta hd
  have hdnat := logic_toInt_le_nat d
  have he := BitVec.toInt_add_of_not_saddOverflow (x := a) (y := c) (by simpa using hf)
  rw [he]
  constructor <;> omega

theorem logic_addcmp_unsigned (a c d : BitVec w) (delta : Nat)
    (hc : c ≠ 0) (ha : c.toNat < a.toNat)
    (hd : (d-c).toNat = delta) (hf : BitVec.uaddOverflow a c = false) :
    c.toNat + 2 ≤ (a+c).toNat ∧ d.toNat ≤ c.toNat + delta := by
  have hcn : c.toNat ≠ 0 := by intro h; apply hc; apply BitVec.eq_of_toNat_eq; simpa using h
  have he := BitVec.toNat_add_of_not_uaddOverflow (x := a) (y := c) (by simpa using hf)
  rw [he]
  constructor
  · omega
  · exact logic_delta_toNat_bound c d delta hd
end Veir.InstSimplify
