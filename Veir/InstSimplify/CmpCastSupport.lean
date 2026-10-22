import Veir.InstSimplify.CastLogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

theorem neg_zext_nonpos (x : BitVec w) (hw : w < v) :
    (-(x.zeroExtend v)).toInt ≤ 0 := by
  have hn : x.zeroExtend v ≠ BitVec.intMin v := by
    intro he
    have ht := congrArg BitVec.toInt he
    rw [logic_zext_toInt x hw, BitVec.toInt_intMin_of_pos (by omega)] at ht
    have hp : (0 : Int) < 2 ^ (v-1) := Int.pow_pos (by decide)
    omega
  rw [BitVec.toInt_neg_of_ne_intMin hn, logic_zext_toInt x hw]
  omega

theorem zext_nonroundtrip_lt (x : BitVec w) (c : BitVec v) (hw : w < v)
    (hc : (c.setWidth w).zeroExtend v ≠ c) : (x.zeroExtend v).toNat < c.toNat := by
  have hcge : 2^w ≤ c.toNat := by
    by_cases hlt : c.toNat < 2^w
    · exfalso
      apply hc
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth_of_le (by omega), BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]
    · omega
  rw [BitVec.toNat_setWidth_of_le (by omega)]
  exact Nat.lt_of_lt_of_le x.isLt hcge

theorem sext_nonroundtrip_order (x : BitVec w) (c : BitVec v) (hw : w < v) (hw0 : 0 < w)
    (hc : (c.setWidth w).signExtend v ≠ c) :
    (c.toInt < 0 → c.toInt < (x.signExtend v).toInt) ∧
    (0 ≤ c.toInt → (x.signExtend v).toInt < c.toInt) := by
  have hn : ¬(-2^(w-1) ≤ c.toInt ∧ c.toInt < 2^(w-1)) := by
    rintro ⟨hlo,hhi⟩
    apply hc
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by omega),
      ← BitVec.signExtend_eq_setWidth_of_le c (by omega),
      BitVec.toInt_signExtend_eq_toInt_bmod_of_le c (by omega)]
    have hi := BitVec.toInt_ofInt_eq_self hw0 hlo hhi
    simpa only [BitVec.toInt_ofInt] using hi
  have hxlo := BitVec.le_toInt (x := x)
  have hxhi := BitVec.toInt_lt (x := x)
  have hp : (0 : Int) < 2^(w-1) := Int.pow_pos (by decide)
  rw [BitVec.toInt_signExtend_of_le (by omega)]
  constructor <;> intro h <;> omega

theorem zext_nonroundtrip_order (x : BitVec w) (c : BitVec v) (hw : w < v)
    (hc : (c.setWidth w).zeroExtend v ≠ c) :
    (c.toInt < 0 → c.toInt < (x.zeroExtend v).toInt) ∧
    (0 ≤ c.toInt → (x.zeroExtend v).toInt < c.toInt) := by
  have hlt := zext_nonroundtrip_lt x c hw hc
  rw [logic_zext_toInt x hw]
  rw [BitVec.toNat_setWidth_of_le (by omega)] at hlt
  constructor
  · intro h
    omega
  · intro h
    have hm : c.msb = false := by
      cases hm : c.msb
      · rfl
      · have := BitVec.toInt_neg_of_msb_true hm
        omega
    rw [BitVec.toInt_eq_toNat_of_msb hm]
    omega

inductive CastCompareLiteral where
  | falseValue | trueValue | negative | nonnegative

def CastCompareLiteral.value (kind : CastCompareLiteral) (constant : Int) (width : Nat) : Int :=
  match kind with
  | .falseValue => 0
  | .trueValue => 1
  | .negative => if (BitVec.ofInt width constant).toInt < 0 then 1 else 0
  | .nonnegative => if 0 ≤ (BitVec.ofInt width constant).toInt then 1 else 0

def castNonroundtripGuard (signed : Bool) (constant : Int) (src dst : TypeAttr) : Bool :=
  match src.val, dst.val with
  | .integerType s, .integerType d =>
    let c := BitVec.ofInt d.bitwidth constant
    decide (0 < s.bitwidth) &&
      (match signed with
      | true => (c.setWidth s.bitwidth).signExtend d.bitwidth != c
      | false => (c.setWidth s.bitwidth).zeroExtend d.bitwidth != c)
  | _, _ => false

def unsignedCmpResult (p : LLVM.IntPred) : Bool :=
  match p with | .ne | .ult | .ule => true | _ => false

theorem icmp_unsigned_lt (a c : BitVec v) (h : a.toNat < c.toNat) (p : LLVM.IntPred)
    (hp : p = .eq ∨ p = .ne ∨ p = .ugt ∨ p = .uge ∨ p = .ult ∨ p = .ule) :
    LLVM.Int.icmp (.val a) (.val c) p = .val (BitVec.ofBool (unsignedCmpResult p)) := by
  have hne : a ≠ c := by intro he; have := congrArg BitVec.toNat he; omega
  cases p <;> simp_all [LLVM.Int.icmp, LLVM.IntPred.eval, unsignedCmpResult,
    BitVec.ult, BitVec.ule, bne, Id.run, pure] <;> omega

def signedCmpResult (p : LLVM.IntPred) : Bool :=
  match p with | .ne | .slt | .sle => true | _ => false

theorem icmp_signed_lt (a c : BitVec v) (h : a.toInt < c.toInt) (p : LLVM.IntPred)
    (hp : p = .eq ∨ p = .ne ∨ p = .sgt ∨ p = .sge ∨ p = .slt ∨ p = .sle) :
    LLVM.Int.icmp (.val a) (.val c) p = .val (BitVec.ofBool (signedCmpResult p)) := by
  have hne : a ≠ c := by intro he; have := congrArg BitVec.toInt he; omega
  cases p <;> simp_all [LLVM.Int.icmp, LLVM.IntPred.eval, signedCmpResult,
    BitVec.slt, BitVec.sle, bne, Id.run, pure] <;> omega

def outsideCmpResult (p : LLVM.IntPred) (c : BitVec v) : Bool :=
  match p with
  | .eq => false
  | .ne => true
  | .sgt | .sge => decide (c.toInt < 0)
  | .slt | .sle => decide (0 ≤ c.toInt)
  | _ => false

theorem icmp_signed_outside (a c : BitVec v)
    (h : (c.toInt < 0 → c.toInt < a.toInt) ∧ (0 ≤ c.toInt → a.toInt < c.toInt))
    (p : LLVM.IntPred) (hp : p = .eq ∨ p = .ne ∨ p = .sgt ∨ p = .sge ∨ p = .slt ∨ p = .sle) :
    LLVM.Int.icmp (.val a) (.val c) p = .val (BitVec.ofBool (outsideCmpResult p c)) := by
  by_cases hn : c.toInt < 0
  · have hb := h.1 hn
    have hne : a ≠ c := by intro he; have := congrArg BitVec.toInt he; omega
    cases p <;> simp_all [LLVM.Int.icmp, LLVM.IntPred.eval, outsideCmpResult,
      BitVec.slt, BitVec.sle, bne, Id.run, pure] <;> first | omega | (apply congrArg BitVec.ofBool; simp only [decide_eq_decide]; omega)
  · have hb := h.2 (by omega)
    have hne : a ≠ c := by intro he; have := congrArg BitVec.toInt he; omega
    cases p <;> simp_all [LLVM.Int.icmp, LLVM.IntPred.eval, outsideCmpResult,
      BitVec.slt, BitVec.sle, bne, Id.run, pure] <;> first | omega | (apply congrArg BitVec.ofBool; simp only [decide_eq_decide]; omega)


end Veir.InstSimplify
