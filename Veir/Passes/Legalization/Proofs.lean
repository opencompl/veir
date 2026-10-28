module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

import Veir.ForLean
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.GMIR.OpInfo

public section

namespace Veir.Data.LLVM

/--
Prove the correctness of `llvm.add` widening with anyext.
-/
theorem add_widening_32_64 (i i' : LLVM.Int 32) (ext ext' : BitVec 32) (nuw nsw : Bool) :
    LLVM.Int.add i i' nuw nsw ⊒
      LLVM.Int.trunc (LLVM.Int.add
        (LLVM.Int.ext i 64 ext (by grind))
        (LLVM.Int.ext i' 64 ext' (by grind))
        false false
      ) 32 false false (by grind) := by
  veir_bv_decide

/--
Prove the correctness of combining `g_anyext (g_trunc x)` to `x`, at every width and whatever the
`nsw` and `nuw` flags of the `g_trunc`.
-/
theorem anyext_trunc_same (w n : Nat) (h : n < w) (x : LLVM.Int w) (nsw nuw : Bool) :
    ∃ ext : BitVec (w - n), LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw h) w ext h ⊒ x :=
  ⟨x.getValueD.extractLsb' n (w - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_anyext (g_trunc x)` to a narrower `g_trunc x`, at every
width.
-/
theorem anyext_trunc_narrower (w n m : Nat) (hn : n < m) (hm : m < w) (x : LLVM.Int w)
    (nsw nuw : Bool) :
    ∃ ext : BitVec (m - n),
      LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw (by omega)) m ext hn ⊒
        LLVM.Int.trunc x m false false hm :=
  ⟨x.getValueD.extractLsb' n (m - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_anyext (g_trunc x)` to a wider `g_anyext x`, at every width
and whatever the high bits `ext'` of the new `g_anyext` are.
-/
theorem anyext_trunc_wider (w n m : Nat) (hn : n < w) (hw : w < m) (x : LLVM.Int w)
    (ext' : BitVec (m - w)) (nsw nuw : Bool) :
    ∃ ext : BitVec (m - n),
      LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw hn) m ext (by omega) ⊒
        LLVM.Int.ext x m ext' hw :=
  ⟨(ext' ++ x.getValueD.extractLsb' n (w - n)).cast (by omega), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_anyext (g_anyext x)` to `g_anyext x`, at every width.
-/
theorem anyext_anyext (w n m : Nat) (hn : w < n) (hm : n < m) (x : LLVM.Int w)
    (ext : BitVec (m - w)) :
    ∃ ext₁ : BitVec (n - w), ∃ ext₂ : BitVec (m - n),
      LLVM.Int.ext (LLVM.Int.ext x n ext₁ hn) m ext₂ hm ⊒ LLVM.Int.ext x m ext (by omega) :=
  ⟨ext.extractLsb' 0 (n - w), ext.extractLsb' (n - w) (m - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_trunc (g_trunc x)` to `g_trunc x`, at every width and whatever
the flags of both `g_trunc`s.
-/
theorem trunc_trunc (w n m : Nat) (hn : n < m) (hm : m < w) (x : LLVM.Int w)
    (nsw nuw nsw' nuw' : Bool) :
    LLVM.Int.trunc (LLVM.Int.trunc x m nsw nuw hm) n nsw' nuw' hn ⊒
      LLVM.Int.trunc x n false false (by omega) := by
  veir_bv_normalize
  simp [BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hn)]

/-- Bit `i` of the mask `2 ^ n - 1` is set exactly when `i < n`. -/
private theorem getElem_ofInt_two_pow_sub_one {m n i : Nat} (hi : i < m) :
    (BitVec.ofInt m (2 ^ n - 1))[i] = decide (i < n) := by
  rw [show (2 ^ n - 1 : _root_.Int) = ((2 ^ n - 1 : Nat) : _root_.Int) by
    simp [Int.natCast_sub Nat.one_le_two_pow]]
  simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, hi]

/--
Prove the correctness of lowering `g_zext` to a `g_and` of a `g_anyext` with the mask of the source
width, at every width.
-/
theorem zext_and_anyext (n m : Nat) (h : n < m) (x : LLVM.Int n) (nneg : Bool)
    (ext : BitVec (m - n)) :
    LLVM.Int.zext x m nneg h ⊒
      LLVM.Int.and (LLVM.Int.ext x m ext h) (LLVM.Int.constant m (2 ^ n - 1)) := by
  veir_bv_normalize
  simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append, getElem_ofInt_two_pow_sub_one]
  grind

/--
Prove the correctness of lowering `g_uaddo` to a `g_add`, at every width.

The add carries exactly when its sum is less than an operand.
-/
theorem uaddo_lowering {w : Nat} (x y : LLVM.Int w) :
    (LLVM.Int.add x y, LLVM.Int.uaddOverflowFlag x y) =
      let sum := LLVM.Int.add x y
      (sum, LLVM.Int.icmp sum y .ult) := by
  cases x <;> cases y <;>
    simp [LLVM.Int.uaddOverflowFlag, LLVM.Int.add, LLVM.Int.icmp, Id.run, IntPred.eval,
      BitVec.uaddOverflow_eq_ult]

/--
Prove the correctness of lowering `g_uadde`, at every width wider than `i1`.

The lowering adds the operands, then adds the carry-in. It carries if either add carries. The
second add carries only if its sum is zero.
-/
private theorem uadde_lowering {w : Nat} (h : 1 < w) (x y : LLVM.Int w) (c : LLVM.Int 1) :
    uaddWithCarry x y c =
      let tmp := LLVM.Int.add x y
      let carry := LLVM.Int.icmp tmp x .ult
      let sum := LLVM.Int.add tmp (LLVM.Int.zext c w false h)
      let carry2 := LLVM.Int.and (LLVM.Int.icmp sum (LLVM.Int.constant w 0) .eq) c
      (sum, LLVM.Int.or carry carry2) := by
  cases x <;> cases y <;> cases c
  case val.val.val x y c =>
    obtain ⟨b, rfl⟩ := c.exists_eq_ofBool
    -- It carries if either `g_add` carries.
    simp [uaddWithCarry, LLVM.Int.add, LLVM.Int.icmp, LLVM.Int.zext, LLVM.Int.and, LLVM.Int.or,
      LLVM.Int.constant, Id.run, IntPred.eval, BitVec.ofBool_or_ofBool, BitVec.ofBool_and_ofBool,
      BitVec.carry_eq_uaddOverflow_or (by omega : 0 < w), BitVec.uaddOverflow_eq_ult_left x y,
      BitVec.uaddOverflow_setWidth_ofBool (by omega : 0 < w)]
  -- A poison operand makes both sides poison.
  all_goals rfl

/--
Prove the correctness of lowering `g_usubo` to a `g_sub`, at every width.

The sub borrows exactly when the left operand is less than the right one.
-/
theorem usubo_lowering {w : Nat} (x y : LLVM.Int w) :
    (LLVM.Int.sub x y, LLVM.Int.usubOverflowFlag x y) =
      (LLVM.Int.sub x y, LLVM.Int.icmp x y .ult) := by
  cases x <;> cases y <;>
    simp [LLVM.Int.usubOverflowFlag, LLVM.Int.icmp, Id.run, IntPred.eval,
      BitVec.usubOverflow_eq, BitVec.ult_eq_decide, BitVec.lt_def]

/--
Prove the correctness of lowering `g_usube`, at every width wider than `i1`.

The lowering subtracts the operands, then subtracts the borrow-in. It borrows if either sub borrows.
The second sub borrows only if the first difference is zero.
-/
private theorem usube_lowering {w : Nat} (h : 1 < w) (x y : LLVM.Int w) (b : LLVM.Int 1) :
    usubWithBorrow x y b =
      let tmp := LLVM.Int.sub x y
      let borrow := LLVM.Int.icmp tmp x .ugt
      let diff := LLVM.Int.sub tmp (LLVM.Int.zext b w false h)
      let borrow2 := LLVM.Int.and (LLVM.Int.icmp tmp (LLVM.Int.constant w 0) .eq) b
      (diff, LLVM.Int.or borrow borrow2) := by
  cases x <;> cases y <;> cases b
  case val.val.val x y b =>
    obtain ⟨b, rfl⟩ := b.exists_eq_ofBool
    -- It borrows if either `g_sub` borrows.
    simp [usubWithBorrow, LLVM.Int.sub, LLVM.Int.icmp, LLVM.Int.zext, LLVM.Int.and, LLVM.Int.or,
      LLVM.Int.constant, Id.run, IntPred.eval, BitVec.ofBool_or_ofBool, BitVec.ofBool_and_ofBool,
      BitVec.ult_setWidth_add_ofBool (by omega : 0 < w), BitVec.usubOverflow_eq_ult_sub x y,
      BitVec.usubOverflow_setWidth_ofBool (by omega : 0 < w)]
  -- A poison operand makes both sides poison.
  all_goals rfl

end Veir.Data.LLVM

end
