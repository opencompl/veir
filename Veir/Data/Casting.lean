module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.LLVM.Int.Bitblast
public import Veir.Data.LLVM.Byte.Basic
public import Veir.Data.RISCV.Reg.Basic

import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Data.LLVM.Byte.Basic
meta import Veir.Meta.Tactic.BVDecide

public section

/-!
  This file defines the conversions between different types used in lowering passes.
  These represent the semantics of `builtin.unrealized_conversion_cast` operations.
-/


/--
  Cast `LLVM.Int` to `RISCV.Reg`.
-/
def LLVM.Int.toReg (i : Veir.Data.LLVM.Int w) : Veir.Data.RISCV.Reg :=
  match i with
  | .poison => .mk 0#64
  | .val bv => .mk (bv.zeroExtend 64)

/--
  Cast `RISCV.Reg` to `LLVM.Int`.
-/
@[grind]
def RISCV.Reg.toInt (r : Veir.Data.RISCV.Reg) (w : Nat) : Veir.Data.LLVM.Int w :=
  Veir.Data.LLVM.Int.val (BitVec.zeroExtend w r.val)

@[veir_bv_normalize, grind =]
theorem toInt_eq_val {r : Veir.Data.RISCV.Reg} :
    (RISCV.Reg.toInt r 64).getValue = r.val := by
  simp [RISCV.Reg.toInt, Veir.Data.LLVM.Int.getValue]

@[veir_bv_normalize, grind =]
theorem toInt_isPoison {w : Nat} {r : Veir.Data.RISCV.Reg} :
    (RISCV.Reg.toInt r w).isPoison = false := by
  simp [RISCV.Reg.toInt, Veir.Data.LLVM.Int.isPoison]

@[veir_bv_normalize, grind =]
theorem toInt_getValue {w : Nat} {r : Veir.Data.RISCV.Reg} :
    (RISCV.Reg.toInt r w).getValue = (r.val).zeroExtend w := by
  simp [RISCV.Reg.toInt, Veir.Data.LLVM.Int.getValue]

@[veir_bv_normalize, grind =]
theorem val_toReg {w : Nat} {i : Veir.Data.LLVM.Int w} :
    (LLVM.Int.toReg i).val = if h : i.isPoison = true then 0#64 else i.getValue.zeroExtend 64 := by
  simp only [LLVM.Int.toReg, BitVec.truncate_eq_setWidth]
  split
  · simp [Veir.Data.LLVM.Int.isPoison]
  · simp [veir_bv_normalize]

@[simp, grind =]
theorem toReg_toInt_64 {r : Veir.Data.RISCV.Reg} :
    LLVM.Int.toReg (RISCV.Reg.toInt r 64) = r := by
  simp [LLVM.Int.toReg, RISCV.Reg.toInt]

/--
  An integer of at most 64 bits is refined by its round trip through a register.
-/
@[grind .]
theorem LLVM.Int.isRefinedBy_toInt_toReg {w : Nat} (hw : w ≤ 64) (i : Veir.Data.LLVM.Int w) :
    i ⊒ RISCV.Reg.toInt (LLVM.Int.toReg i) w := by
  grind [BitVec.setWidth_setWidth_of_le _ hw]

/--
  Cast `LLVM.Byte` to `RISCV.Reg`.
-/
def LLVM.Byte.toReg (b : Veir.Data.LLVM.Byte w) : Veir.Data.RISCV.Reg :=
  ⟨b.val.zeroExtend 64⟩

/--
  Cast `RISCV.Reg` to `LLVM.Byte`.
-/
@[grind]
def RISCV.Reg.toByte (r : Veir.Data.RISCV.Reg) (w : Nat) : Veir.Data.LLVM.Byte w :=
  ⟨BitVec.zeroExtend w r.val, 0, by simp⟩

@[veir_bv_normalize, grind =]
theorem toByte_eq_val {r : Veir.Data.RISCV.Reg} :
    (RISCV.Reg.toByte r 64).val = r.val := by
  simp [RISCV.Reg.toByte]

@[veir_bv_normalize, grind =]
theorem toByte_val {w : Nat} {r : Veir.Data.RISCV.Reg} :
    (RISCV.Reg.toByte r w).val = (r.val).zeroExtend w := by
  simp [RISCV.Reg.toByte]

/--
  A byte of at most 64 bits is refined by its round trip through a register.
-/
@[grind .]
theorem LLVM.Byte.isRefinedBy_toByte_toReg {w : Nat} (hw : w ≤ 64) (b : Veir.Data.LLVM.Byte w) :
    b ⊒ RISCV.Reg.toByte (LLVM.Byte.toReg b) w := by
  grind [LLVM.Byte.toReg, BitVec.setWidth_setWidth_of_le _ hw]

/-- The register of an integer that is not poison holds its bits. -/
theorem LLVM.Int.toReg_val {w : Nat} {x : BitVec w} :
    LLVM.Int.toReg (.val x) = ⟨x.zeroExtend 64⟩ := by
  simp [LLVM.Int.toReg]

/-- The register of a byte holds its bits, with its poison bits as zero. -/
theorem LLVM.Byte.toReg_eq {w : Nat} {b : Veir.Data.LLVM.Byte w} :
    LLVM.Byte.toReg b = ⟨b.val.zeroExtend 64⟩ := by
  simp [LLVM.Byte.toReg]

/--
  A byte of at most 64 bits is refined by its round trip through a register,
  whatever bits its poison bits come out as.
-/
theorem LLVM.Byte.isRefinedBy_toByte_of_poison {w : Nat} (hw : w ≤ 64)
    (b : Veir.Data.LLVM.Byte w) (bits : BitVec w) :
    b ⊒ RISCV.Reg.toByte ⟨(b.val ||| (b.poison &&& bits)).zeroExtend 64⟩ w := by
  simp only [Veir.Data.LLVM.Byte.isRefinedBy, RISCV.Reg.toByte,
    BitVec.truncate_eq_setWidth, BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_allOnes, hi, decide_true]
  cases b.poison.getLsbD i <;> simp

/--
  Resolving the poison bits of a byte to the bits of a resolved refinement of it
  gives that resolved refinement: the bits that are not poison already agree.
-/
theorem LLVM.Byte.resolve_of_isRefinedBy {w : Nat} {b b' : Veir.Data.LLVM.Byte w} (h : b ⊒ b')
    (bits : BitVec w) :
    b.val ||| (b.poison &&& (b'.val ||| (b'.poison &&& bits))) =
      b'.val ||| (b'.poison &&& bits) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h' : (b.poison ||| ((b.val ^^^ ~~~b'.val) &&& ~~~b'.poison)) = BitVec.allOnes w := h
  have h₁ := congrArg (·.getLsbD i) h'
  have h₂ := congrArg (·.getLsbD i) b.h
  have h₃ := congrArg (·.getLsbD i) b'.h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_allOnes, decide_eq_true hi] at h₁ h₂ h₃ ⊢
  clear h'
  rcases Bool.eq_false_or_eq_true (b.val.getLsbD i) with h₄ | h₄ <;>
  rcases Bool.eq_false_or_eq_true (b.poison.getLsbD i) with h₅ | h₅ <;>
  rcases Bool.eq_false_or_eq_true (b'.val.getLsbD i) with h₆ | h₆ <;>
  rcases Bool.eq_false_or_eq_true (b'.poison.getLsbD i) with h₇ | h₇ <;>
  rcases Bool.eq_false_or_eq_true (bits.getLsbD i) with h₈ | h₈ <;>
  simp_all

/-- A refinement of a byte is poison only where the byte is. -/
theorem LLVM.Byte.poison_eq_allOnes_of_isRefinedBy {w : Nat} {b b' : Veir.Data.LLVM.Byte w}
    (h : b ⊒ b') (h' : b'.poison = BitVec.allOnes w) : b.poison = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hr : (b.poison ||| ((b.val ^^^ ~~~b'.val) &&& ~~~b'.poison)) = BitVec.allOnes w := h
  have h₁ := congrArg (·.getLsbD i) hr
  have h₂ := congrArg (·.getLsbD i) h'
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_allOnes, decide_eq_true hi] at h₁ h₂ ⊢
  simp_all

/-- A byte without poison is refined only by itself. -/
theorem LLVM.Byte.eq_of_isRefinedBy_of_poison_eq_zero {w : Nat} {b b' : Veir.Data.LLVM.Byte w}
    (h : b ⊒ b') (h₀ : b.poison = 0) : b' = b := by
  have hr : (b.poison ||| ((b.val ^^^ ~~~b'.val) &&& ~~~b'.poison)) = BitVec.allOnes w := h
  have hp : b'.poison = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h₁ := congrArg (·.getLsbD i) hr
    have h₂ := congrArg (·.getLsbD i) h₀
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
      BitVec.getLsbD_allOnes, decide_eq_true hi] at h₁ h₂ ⊢
    simp_all
  have hv : b'.val = b.val := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h₁ := congrArg (·.getLsbD i) hr
    have h₂ := congrArg (·.getLsbD i) h₀
    have h₃ := congrArg (·.getLsbD i) hp
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
      BitVec.getLsbD_allOnes, decide_eq_true hi] at h₁ h₂ h₃ ⊢
    rcases Bool.eq_false_or_eq_true (b.val.getLsbD i) with h₄ | h₄ <;>
    rcases Bool.eq_false_or_eq_true (b'.val.getLsbD i) with h₅ | h₅ <;> simp_all
  rcases b with ⟨v, p, _⟩
  rcases b' with ⟨v', p', _⟩
  simp_all

/--
  Cast `LLVM.Byte` to `LLVM.Int`. The result is poison only if every bit is poison, otherwise
  poison bits become zero.
-/
def LLVM.Byte.toFrozenInt (b : Veir.Data.LLVM.Byte w) : Veir.Data.LLVM.Int w :=
  if b.poison = BitVec.allOnes w then .poison else .val b.val

/--
  A poison integer casts to the wholly poison byte, which `llvm.mlir.poison` of a byte type is.
  This is the correctness of `lowerBytePoison` in `llvm-to-gmir`.
-/
@[simp]
theorem LLVM.Byte.fromInt_poison {w : Nat} :
    Veir.Data.LLVM.Byte.fromInt (Veir.Data.LLVM.Int.poison : Veir.Data.LLVM.Int w) =
      Veir.Data.LLVM.Byte.allPoison := by
  simp [Veir.Data.LLVM.Byte.fromInt, Veir.Data.LLVM.Byte.allPoison,
    Veir.Data.LLVM.Int.isPoison]

/--
  An integer cast to a byte and back is unchanged.
-/
@[simp, grind =]
theorem LLVM.Byte.toFrozenInt_fromInt {w : Nat} (h : 0 < w) (x : Veir.Data.LLVM.Int w) :
    LLVM.Byte.toFrozenInt (Veir.Data.LLVM.Byte.fromInt x) = x := by
  cases x <;> simp [LLVM.Byte.toFrozenInt, Veir.Data.LLVM.Byte.fromInt,
    Veir.Data.LLVM.Int.isPoison] <;> grind
