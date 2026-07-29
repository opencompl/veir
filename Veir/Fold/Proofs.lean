module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.LLVM.Byte.Basic
public import Veir.Data.RISCV.Reg.Basic
public import Veir.Data.Refinement
public import Veir.IR.Attribute

import Veir.Meta.BVDecide
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Lemmas

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

public section

/-!
  Standalone correctness proofs for the partial folds in `Veir.Fold`.

  Integer proofs are specialized to i8 so `veir_bv_decide` can check them
  exhaustively. The `arith` and LLVM tables use the same `LLVM.Int` operations,
  so a shared theorem covers corresponding rows in both tables. As in the fold
  implementation, the theorem direction is refinement: replacing a poison
  result by a concrete value is permitted.

  The shared integer theorems cover these paired rows:

  * `arith.addi/subi/muli/andi/ori/xori/shli/shrsi/shrui` and
    `llvm.add/sub/mul/and/or/xor/shl/ashr/lshr`;
  * `arith.divsi/divui/remsi/remui` and `llvm.sdiv/udiv/srem/urem`;
  * `arith.maxsi/minsi/maxui/minui` and the four LLVM min/max intrinsics;
  * `arith.cmpi/select` and `llvm.icmp/select`.
-/

namespace Veir.Fold.Proofs

open Veir.Data

namespace Integer

theorem add_zero (x : LLVM.Int 8) (nsw nuw : Bool) :
    LLVM.Int.add x (LLVM.Int.constant 8 0) nsw nuw ⊒ x := by
  veir_bv_decide

theorem sub_zero (x : LLVM.Int 8) (nsw nuw : Bool) :
    LLVM.Int.sub x (LLVM.Int.constant 8 0) nsw nuw ⊒ x := by
  veir_bv_decide

theorem mul_zero (x : LLVM.Int 8) (nsw nuw : Bool) :
    LLVM.Int.mul x (LLVM.Int.constant 8 0) nsw nuw ⊒ LLVM.Int.constant 8 0 := by
  veir_bv_decide

theorem mul_one (x : LLVM.Int 8) (nsw nuw : Bool) :
    LLVM.Int.mul x (LLVM.Int.constant 8 1) nsw nuw ⊒ x := by
  veir_bv_decide

theorem and_zero (x : LLVM.Int 8) :
    LLVM.Int.and x (LLVM.Int.constant 8 0) ⊒ LLVM.Int.constant 8 0 := by
  veir_bv_decide

theorem and_all_ones (x : LLVM.Int 8) :
    LLVM.Int.and x (LLVM.Int.constant 8 (-1)) ⊒ x := by
  veir_bv_decide

theorem or_zero (x : LLVM.Int 8) (disjoint : Bool) :
    LLVM.Int.or x (LLVM.Int.constant 8 0) disjoint ⊒ x := by
  veir_bv_decide

theorem or_all_ones (x : LLVM.Int 8) (disjoint : Bool) :
    LLVM.Int.or x (LLVM.Int.constant 8 (-1)) disjoint ⊒ LLVM.Int.constant 8 (-1) := by
  veir_bv_decide

theorem xor_zero (x : LLVM.Int 8) :
    LLVM.Int.xor x (LLVM.Int.constant 8 0) ⊒ x := by
  veir_bv_decide

theorem shl_zero (x : LLVM.Int 8) (nsw nuw : Bool) :
    LLVM.Int.shl x (LLVM.Int.constant 8 0) nsw nuw ⊒ x := by
  veir_bv_decide

theorem lshr_zero (x : LLVM.Int 8) (exact : Bool) :
    LLVM.Int.lshr x (LLVM.Int.constant 8 0) exact ⊒ x := by
  veir_bv_decide

theorem ashr_zero (x : LLVM.Int 8) (exact : Bool) :
    LLVM.Int.ashr x (LLVM.Int.constant 8 0) exact ⊒ x := by
  veir_bv_decide

theorem sdiv_zero (x : LLVM.Int 8) (exact : Bool) :
    LLVM.Int.sdiv x (LLVM.Int.constant 8 0) exact ⊒ LLVM.Int.poison := by
  veir_bv_decide

theorem sdiv_one (x : LLVM.Int 8) (exact : Bool) :
    LLVM.Int.sdiv x (LLVM.Int.constant 8 1) exact ⊒ x := by
  veir_bv_decide

theorem udiv_zero (x : LLVM.Int 8) (exact : Bool) :
    LLVM.Int.udiv x (LLVM.Int.constant 8 0) exact ⊒ LLVM.Int.poison := by
  veir_bv_decide

theorem udiv_one (x : LLVM.Int 8) (exact : Bool) :
    LLVM.Int.udiv x (LLVM.Int.constant 8 1) exact ⊒ x := by
  veir_bv_decide

/-- i8 value semantics of `arith.ceildivui`, used only by these standalone proofs. -/
def ceildivui (a b : LLVM.Int 8) : LLVM.Int 8 :=
  let zero := LLVM.Int.constant 8 0
  let one := LLVM.Int.constant 8 1
  let isZero := LLVM.Int.icmp a zero .eq
  let quotient := LLVM.Int.udiv (LLVM.Int.sub a one) b
  LLVM.Int.select isZero zero (LLVM.Int.add quotient one)

theorem ceildivui_one (x : LLVM.Int 8) :
    ceildivui x (LLVM.Int.constant 8 1) ⊒ x := by
  simp only [ceildivui]
  veir_bv_decide

/-- i8 value semantics of `arith.ceildivsi`, used only by these standalone proofs. -/
def ceildivsi (a b : LLVM.Int 8) : LLVM.Int 8 :=
  let zero := LLVM.Int.constant 8 0
  let one := LLVM.Int.constant 8 1
  let z := LLVM.Int.sdiv a b
  let notExact := LLVM.Int.icmp a (LLVM.Int.mul z b) .ne
  let signEqual :=
    LLVM.Int.icmp (LLVM.Int.icmp a zero .slt) (LLVM.Int.icmp b zero .slt) .eq
  let cond := LLVM.Int.and notExact signEqual
  LLVM.Int.select cond (LLVM.Int.add z one) z

theorem ceildivsi_one (x : LLVM.Int 8) :
    ceildivsi x (LLVM.Int.constant 8 1) ⊒ x := by
  simp only [ceildivsi]
  veir_bv_decide

/-- i8 value semantics of `arith.floordivsi`, used only by these standalone proofs. -/
def floordivsi (a b : LLVM.Int 8) : LLVM.Int 8 :=
  let zero := LLVM.Int.constant 8 0
  let negOne := LLVM.Int.constant 8 (-1)
  let z := LLVM.Int.sdiv a b
  let notExact := LLVM.Int.icmp a (LLVM.Int.mul z b) .ne
  let signOpposite :=
    LLVM.Int.icmp (LLVM.Int.icmp a zero .slt) (LLVM.Int.icmp b zero .slt) .ne
  let cond := LLVM.Int.and notExact signOpposite
  LLVM.Int.select cond (LLVM.Int.add z negOne) z

theorem floordivsi_one (x : LLVM.Int 8) :
    floordivsi x (LLVM.Int.constant 8 1) ⊒ x := by
  simp only [floordivsi]
  veir_bv_decide

theorem srem_zero (x : LLVM.Int 8) :
    LLVM.Int.srem x (LLVM.Int.constant 8 0) ⊒ LLVM.Int.poison := by
  veir_bv_decide

theorem srem_one (x : LLVM.Int 8) :
    LLVM.Int.srem x (LLVM.Int.constant 8 1) ⊒ LLVM.Int.constant 8 0 := by
  veir_bv_decide

theorem srem_neg_one (x : LLVM.Int 8) :
    LLVM.Int.srem x (LLVM.Int.constant 8 (-1)) ⊒ LLVM.Int.constant 8 0 := by
  veir_bv_decide

theorem urem_zero (x : LLVM.Int 8) :
    LLVM.Int.urem x (LLVM.Int.constant 8 0) ⊒ LLVM.Int.poison := by
  veir_bv_decide

theorem urem_one (x : LLVM.Int 8) :
    LLVM.Int.urem x (LLVM.Int.constant 8 1) ⊒ LLVM.Int.constant 8 0 := by
  veir_bv_decide

theorem smax_min (x : LLVM.Int 8) :
    LLVM.Int.smax x (.val (BitVec.intMin 8)) ⊒ x := by
  veir_bv_decide

theorem smax_max (x : LLVM.Int 8) :
    LLVM.Int.smax x (.val (BitVec.intMax 8)) ⊒ .val (BitVec.intMax 8) := by
  veir_bv_decide

theorem smin_max (x : LLVM.Int 8) :
    LLVM.Int.smin x (.val (BitVec.intMax 8)) ⊒ x := by
  veir_bv_decide

theorem smin_min (x : LLVM.Int 8) :
    LLVM.Int.smin x (.val (BitVec.intMin 8)) ⊒ .val (BitVec.intMin 8) := by
  veir_bv_decide

theorem umax_zero (x : LLVM.Int 8) :
    LLVM.Int.umax x (LLVM.Int.constant 8 0) ⊒ x := by
  veir_bv_decide

theorem umax_all_ones (x : LLVM.Int 8) :
    LLVM.Int.umax x (LLVM.Int.constant 8 (-1)) ⊒ LLVM.Int.constant 8 (-1) := by
  veir_bv_decide

theorem umin_all_ones (x : LLVM.Int 8) :
    LLVM.Int.umin x (LLVM.Int.constant 8 (-1)) ⊒ x := by
  veir_bv_decide

theorem umin_zero (x : LLVM.Int 8) :
    LLVM.Int.umin x (LLVM.Int.constant 8 0) ⊒ LLVM.Int.constant 8 0 := by
  veir_bv_decide

theorem icmp_ne_zero_i1 (x : LLVM.Int 1) :
    LLVM.Int.icmp x (LLVM.Int.constant 1 0) .ne ⊒ x := by
  veir_bv_decide

theorem icmp_eq_one_i1 (x : LLVM.Int 1) :
    LLVM.Int.icmp x (LLVM.Int.constant 1 1) .eq ⊒ x := by
  veir_bv_decide

theorem select_true (x y : LLVM.Int 8) :
    LLVM.Int.select (LLVM.Int.constant 1 1) x y ⊒ x := by
  veir_bv_decide

theorem select_false (x y : LLVM.Int 8) :
    LLVM.Int.select (LLVM.Int.constant 1 0) x y ⊒ y := by
  veir_bv_decide

theorem select_poison_condition (x y : LLVM.Int 8) :
    LLVM.Int.select LLVM.Int.poison x y ⊒ LLVM.Int.poison := by
  veir_bv_decide

theorem select_poison_true_arm (c : LLVM.Int 1) (y : LLVM.Int 8) :
    LLVM.Int.select c LLVM.Int.poison y ⊒ y := by
  veir_bv_decide

theorem select_poison_false_arm (c : LLVM.Int 1) (x : LLVM.Int 8) :
    LLVM.Int.select c x LLVM.Int.poison ⊒ x := by
  veir_bv_decide

theorem select_true_false (c : LLVM.Int 1) :
    LLVM.Int.select c (LLVM.Int.constant 1 1) (LLVM.Int.constant 1 0) ⊒ c := by
  veir_bv_decide

theorem select_equal (c : LLVM.Int 1) (x : LLVM.Int 8) :
    LLVM.Int.select c x x ⊒ x := by
  veir_bv_decide

end Integer

namespace Byte

/-- The LLVM shift tables also accept a byte-valued left operand. -/
theorem shl_zero (x : LLVM.Byte 8) (nuw : Bool) :
    LLVM.Byte.shl x (LLVM.Int.constant 8 0) nuw = x := by
  cases x
  cases nuw <;> simp [LLVM.Byte.shl, LLVM.Int.constant] <;> congr

theorem lshr_zero (x : LLVM.Byte 8) (exact : Bool) :
    LLVM.Byte.lshr x (LLVM.Int.constant 8 0) exact = x := by
  cases exact <;> simp [LLVM.Byte.lshr, LLVM.Int.constant]

end Byte

namespace GenericSelect

/--
  Type-polymorphic select semantics used for the table cases whose selected
  values are not integers. `none` represents a poison result.
-/
def select (c : LLVM.Int 1) (x y : α) : Option α :=
  match c with
  | .poison => none
  | .val c => some (if c = 1 then x else y)

/-- A poison result may be refined by any concrete selected value. -/
def refines (source : Option α) (target : α) : Prop :=
  source = none ∨ source = some target

theorem select_true (x y : α) :
    refines (select (LLVM.Int.constant 1 1) x y) x := by
  simp [select, refines, LLVM.Int.constant]

theorem select_false (x y : α) :
    refines (select (LLVM.Int.constant 1 0) x y) y := by
  simp [select, refines, LLVM.Int.constant]

theorem select_equal (c : LLVM.Int 1) (x : α) :
    refines (select c x x) x := by
  cases c <;> simp [select, refines]

theorem select_equal_float_bits (c : LLVM.Int 1) (x y : Float)
    (h : x.toBits = y.toBits) :
    refines (select c x y) x := by
  have : x = y := floatEqOfToBitsEq h
  subst y
  exact select_equal c x

end GenericSelect

namespace Riscv

open Data.RISCV

theorem add_zero (x : Reg) :
    Data.RISCV.add (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem sub_zero (x : Reg) :
    Data.RISCV.sub (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem xor_zero (x : Reg) :
    Data.RISCV.xor (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem or_zero (x : Reg) :
    Data.RISCV.or (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem or_all_ones (x : Reg) :
    Data.RISCV.or (Data.RISCV.li (BitVec.allOnes 64)) x =
      Data.RISCV.li (BitVec.allOnes 64) := by
  veir_bv_decide

theorem and_zero (x : Reg) :
    Data.RISCV.and (Data.RISCV.li 0) x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem and_all_ones (x : Reg) :
    Data.RISCV.and (Data.RISCV.li (BitVec.allOnes 64)) x = x := by
  veir_bv_decide

theorem mul_zero (x : Reg) :
    Data.RISCV.mul (Data.RISCV.li 0) x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem mul_one (x : Reg) :
    Data.RISCV.mul (Data.RISCV.li 1) x = x := by
  veir_bv_decide

theorem sll_zero (x : Reg) :
    Data.RISCV.sll (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem srl_zero (x : Reg) :
    Data.RISCV.srl (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem sra_zero (x : Reg) :
    Data.RISCV.sra (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem czeroeqz_zero (x : Reg) :
    Data.RISCV.czeroeqz (Data.RISCV.li 0) x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem czeroeqz_nonzero (x c : Reg) (h : c.val ≠ 0) :
    Data.RISCV.czeroeqz c x = x := by
  veir_bv_decide

theorem czeronez_zero (x : Reg) :
    Data.RISCV.czeronez (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem czeronez_nonzero (x c : Reg) (h : c.val ≠ 0) :
    Data.RISCV.czeronez c x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem addi_zero (x : Reg) :
    Data.RISCV.addi 0 x = x := by
  veir_bv_decide

theorem ori_zero (x : Reg) :
    Data.RISCV.ori 0 x = x := by
  veir_bv_decide

theorem xori_zero (x : Reg) :
    Data.RISCV.xori 0 x = x := by
  veir_bv_decide

theorem andi_zero (x : Reg) :
    Data.RISCV.andi 0 x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem slli_zero (x : Reg) :
    Data.RISCV.slli 0 x = x := by
  veir_bv_decide

theorem srli_zero (x : Reg) :
    Data.RISCV.srli 0 x = x := by
  veir_bv_decide

theorem srai_zero (x : Reg) :
    Data.RISCV.srai 0 x = x := by
  veir_bv_decide

end Riscv

namespace ModArith

/--
  The interpreter's i8 modular multiplication semantics. The modulus remains
  general because the fold accepts every positive modulus that fits the
  storage type.
-/
def mulMod (modulus : Nat) (x y : LLVM.Int 8) : LLVM.Int 8 :=
  match x.toNat?, y.toNat? with
  | some x, some y => LLVM.Int.constant 8 ((x * y) % modulus)
  | _, _ => LLVM.Int.poison

theorem mul_zero_residue_rhs (modulus : Nat)
    (x : LLVM.Int 8) (c : BitVec 8) (h : c.toNat % modulus = 0) :
    mulMod modulus x (.val c) ⊒ LLVM.Int.constant 8 0 := by
  cases x with
  | poison => simp [mulMod, LLVM.Int.toNat?, isRefinedBy]
  | val x =>
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    simp [mulMod, LLVM.Int.toNat?, LLVM.Int.constant, isRefinedBy, hk]
    rw [Int.mul_emod]
    simp

theorem mul_zero_residue_lhs (modulus : Nat)
    (c : BitVec 8) (x : LLVM.Int 8) (h : c.toNat % modulus = 0) :
    mulMod modulus (.val c) x ⊒ LLVM.Int.constant 8 0 := by
  cases x with
  | poison => simp [mulMod, LLVM.Int.toNat?, isRefinedBy]
  | val x =>
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    simp [mulMod, LLVM.Int.toNat?, LLVM.Int.constant, isRefinedBy, hk]
    rw [Int.mul_emod]
    simp

end ModArith

end Veir.Fold.Proofs
