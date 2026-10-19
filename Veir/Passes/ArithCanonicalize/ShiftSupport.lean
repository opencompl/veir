import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize

open Veir Veir.Puddle Veir.Data

theorem shli_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .shli : OpCode)) (x y : LLVM.Int w)
    (v : RuntimeValue) :
    InterpretsTo (.arith .shli) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.shl x y props.attr.nsw props.attr.nuw) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem shrui_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .shrui : OpCode)) (x y : LLVM.Int w)
    (v : RuntimeValue) :
    InterpretsTo (.arith .shrui) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.lshr x y props.exact) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem shrsi_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .shrsi : OpCode)) (x y : LLVM.Int w)
    (v : RuntimeValue) :
    InterpretsTo (.arith .shrsi) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.ashr x y props.exact) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem shl_zero_count_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.shl x (.val 0) nsw nuw) ⊒ .int w x := by
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.shl, isRefinedBy, Id.run]
  | val a =>
    by_cases h : BitVec.ofNat w w = 0#w
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.shl, isRefinedBy, Id.run, pure, h]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.shl, isRefinedBy, Id.run, h]

theorem lshr_zero_count_refines (w : Nat) (x : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.lshr x (.val 0) exact) ⊒ .int w x := by
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run]
  | val a =>
    by_cases h : BitVec.ofNat w w = 0#w
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run, pure, h]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run, h]

theorem ashr_zero_count_refines (w : Nat) (x : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.ashr x (.val 0) exact) ⊒ .int w x := by
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run]
  | val a =>
    by_cases h : BitVec.ofNat w w = 0#w
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run, pure, h]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run, h]

theorem shl_zero_value_refines (w : Nat) (y : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.shl (.val 0) y nsw nuw) ⊒ .int w (.val 0) := by
  cases y with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.shl, isRefinedBy, Id.run]
  | val a =>
    by_cases h : BitVec.ofNat w w ≤ a
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.shl, isRefinedBy, Id.run, pure, h]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.shl, isRefinedBy, Id.run, h]

theorem lshr_zero_value_refines (w : Nat) (y : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.lshr (.val 0) y exact) ⊒ .int w (.val 0) := by
  cases y with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run]
  | val a =>
    by_cases h : BitVec.ofNat w w ≤ a
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run, pure, h]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run, h]

theorem ashr_zero_value_refines (w : Nat) (y : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.ashr (.val 0) y exact) ⊒ .int w (.val 0) := by
  cases y with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run]
  | val a =>
    by_cases h : BitVec.ofNat w w ≤ a
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run, pure, h]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run, h]

theorem shift_count_in_range (w : Nat) (b : BitVec w) (hb : b.toNat < w) :
    ¬ BitVec.ofNat w w ≤ b := by
  simp only [BitVec.le_def, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := w))]
  omega

theorem shl_const_refines (w : Nat) (a b : BitVec w) (nsw nuw : Bool)
    (hb : b.toNat < w) :
    RuntimeValue.int w (LLVM.Int.shl (.val a) (.val b) nsw nuw) ⊒
      .int w (.val (a <<< b)) := by
  have hr := shift_count_in_range w b hb
  cases nsw <;> cases nuw <;>
    (by_cases hs : (a <<< b.toNat).sshiftRight b.toNat ≠ a <;>
     by_cases hu : (a <<< b.toNat) >>> b.toNat ≠ a <;>
     simp [RuntimeValue.isRefinedBy, LLVM.Int.shl, isRefinedBy,
       Id.run, pure, hr, hs, hu])

theorem lshr_const_refines (w : Nat) (a b : BitVec w) (exact : Bool)
    (hb : b.toNat < w) :
    RuntimeValue.int w (LLVM.Int.lshr (.val a) (.val b) exact) ⊒
      .int w (.val (a >>> b)) := by
  have hr := shift_count_in_range w b hb
  cases exact
  · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run, hr]
  · by_cases he : (a >>> b.toNat) <<< b.toNat ≠ a
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy,
        Id.run, pure, hr, he]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy,
        Id.run, hr, he]

theorem ashr_const_refines (w : Nat) (a b : BitVec w) (exact : Bool)
    (hb : b.toNat < w) :
    RuntimeValue.int w (LLVM.Int.ashr (.val a) (.val b) exact) ⊒
      .int w (.val (a.sshiftRight' b)) := by
  have hr := shift_count_in_range w b hb
  cases exact
  · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run, hr]
  · by_cases he : (a >>> b.toNat) <<< b.toNat ≠ a
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy,
        Id.run, pure, hr, he]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy,
        Id.run, hr, he]

theorem allones_sshiftRight (w : Nat) (b : BitVec w) :
    (BitVec.ofInt w (-1)).sshiftRight' b = BitVec.ofInt w (-1) := by
  cases w with
  | zero => simp
  | succ n =>
    have hone : BitVec.ofInt (n + 1) (-1) = BitVec.allOnes (n + 1) := by
      simp [BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes]
    rw [hone, BitVec.sshiftRight_eq']
    rw [BitVec.sshiftRight_eq_of_msb_true
      (BitVec.msb_allOnes (Nat.succ_pos n))]
    simp

theorem ashr_allones_refines (w : Nat) (y : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w
      (LLVM.Int.ashr (.val (BitVec.ofInt w (-1))) y exact) ⊒
      .int w (.val (BitVec.ofInt w (-1))) := by
  cases y with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run]
  | val b =>
    by_cases hr : BitVec.ofNat w w ≤ b
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr,
        isRefinedBy, Id.run, pure, hr]
    · cases exact
      · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr,
          isRefinedBy, Id.run, hr, allones_sshiftRight]
        simpa [BitVec.sshiftRight_eq'] using allones_sshiftRight w b
      · by_cases he : ((BitVec.ofInt w (-1) >>> b.toNat) <<< b.toNat) ≠
          BitVec.ofInt w (-1)
        · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr,
            isRefinedBy, Id.run, pure, hr, he]
        · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr,
            isRefinedBy, Id.run, hr, he, allones_sshiftRight]
          simpa [BitVec.sshiftRight_eq'] using allones_sshiftRight w b

theorem lshr_self_refines (w : Nat) (x : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.lshr x x exact) ⊒ .int w (.val 0) := by
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run]
  | val a =>
    by_cases hr : BitVec.ofNat w w ≤ a
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr,
        isRefinedBy, Id.run, pure, hr]
    · cases exact
      · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr,
          isRefinedBy, Id.run, hr, BitVec.ushiftRight_self]
      · by_cases hz : a = 0#w
        · have hn : BitVec.ofNat w w ≠ 0#w := by
            intro he
            exact hr (by simp [he, hz])
          simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr,
            isRefinedBy, Id.run, hr, hz, hn, BitVec.ushiftRight_self]
        · simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr,
            isRefinedBy, Id.run, pure, hr, hz, eq_comm, BitVec.ushiftRight_self]

theorem in_range_msb_false (w : Nat) (a : BitVec w) (ha : a.toNat < w) :
    a.msb = false := by
  cases w with
  | zero => omega
  | succ n =>
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    have hn : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    rw [Nat.pow_succ]
    omega

theorem ashr_self_refines (w : Nat) (x : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.ashr x x exact) ⊒ .int w (.val 0) := by
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run]
  | val a =>
    by_cases hr : BitVec.ofNat w w ≤ a
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr,
        isRefinedBy, Id.run, pure, hr]
    · have hbound : a.toNat < w := by
        have hlt : a < BitVec.ofNat w w := BitVec.not_le.mp hr
        simpa [BitVec.lt_def, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := w))] using hlt
      have hmsb := in_range_msb_false w a hbound
      have hshift : a.sshiftRight' a = 0#w := by
        rw [BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_of_msb_false hmsb]
        exact BitVec.ushiftRight_self a
      cases exact
      · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr,
          isRefinedBy, Id.run, hr, hshift]
        simpa [BitVec.sshiftRight_eq'] using hshift
      · by_cases hz : a = 0#w
        · have hn : BitVec.ofNat w w ≠ 0#w := by
            intro he
            exact hr (by simp [he, hz])
          simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr,
            isRefinedBy, Id.run, hr, hz, hn, hshift]
        · simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr,
            isRefinedBy, Id.run, pure, hr, hz, eq_comm, hshift]

end Veir.ArithCanonicalize
