module

public import Veir.Fold.Basic
public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Refinement

import Veir.Meta.BVDecide
import Veir.IR.Attribute
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Bitblast

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

public section

/-!
  Standalone correctness proofs for the dialect-independent partial folds.

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

  `GenericSelect` covers the type-independent rows of `Fold.selectFoldsTo`,
  which backs both `arith.select` and `llvm.select`.

  Proofs that are specific to one dialect live beside that dialect's fold
  table, in `Veir/Dialects/*/Fold/Lemmas.lean`.
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

theorem ceildivui_one (x : LLVM.Int 8) :
    (let zero := LLVM.Int.constant 8 0
     let one := LLVM.Int.constant 8 1
     let isZero := LLVM.Int.icmp x zero .eq
     let quotient := LLVM.Int.udiv (LLVM.Int.sub x one) one
     LLVM.Int.select isZero zero (LLVM.Int.add quotient one)) ⊒ x := by
  veir_bv_decide

theorem ceildivsi_one (x : LLVM.Int 8) :
    (let zero := LLVM.Int.constant 8 0
     let one := LLVM.Int.constant 8 1
     let z := LLVM.Int.sdiv x one
     let notExact := LLVM.Int.icmp x (LLVM.Int.mul z one) .ne
     let signEqual :=
       LLVM.Int.icmp (LLVM.Int.icmp x zero .slt) (LLVM.Int.icmp one zero .slt) .eq
     let cond := LLVM.Int.and notExact signEqual
     LLVM.Int.select cond (LLVM.Int.add z one) z) ⊒ x := by
  veir_bv_decide

theorem floordivsi_one (x : LLVM.Int 8) :
    (let zero := LLVM.Int.constant 8 0
     let one := LLVM.Int.constant 8 1
     let negOne := LLVM.Int.constant 8 (-1)
     let z := LLVM.Int.sdiv x one
     let notExact := LLVM.Int.icmp x (LLVM.Int.mul z one) .ne
     let signOpposite :=
       LLVM.Int.icmp (LLVM.Int.icmp x zero .slt) (LLVM.Int.icmp one zero .slt) .ne
     let cond := LLVM.Int.and notExact signOpposite
     LLVM.Int.select cond (LLVM.Int.add z negOne) z) ⊒ x := by
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

namespace GenericSelect

theorem select_true (x y : α) :
    (let source :=
       match LLVM.Int.constant 1 1 with
       | .poison => none
       | .val c => some (if c = 1 then x else y)
     source = none ∨ source = some x) := by
  simp [LLVM.Int.constant]

theorem select_false (x y : α) :
    (let source :=
       match LLVM.Int.constant 1 0 with
       | .poison => none
       | .val c => some (if c = 1 then x else y)
     source = none ∨ source = some y) := by
  simp [LLVM.Int.constant]

theorem select_equal (c : LLVM.Int 1) (x : α) :
    (let source :=
       match c with
       | .poison => none
       | .val c => some (if c = 1 then x else x)
     source = none ∨ source = some x) := by
  cases c <;> simp

theorem select_equal_float_bits (c : LLVM.Int 1) (x y : Float)
    (h : x.toBits = y.toBits) :
    (let source :=
       match c with
       | .poison => none
       | .val c => some (if c = 1 then x else y)
     source = none ∨ source = some x) := by
  have : x = y := floatEqOfToBitsEq h
  subst y
  exact select_equal c x

end GenericSelect

end Veir.Fold.Proofs
