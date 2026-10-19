import Veir.Passes.ArithCanonicalize.SelectSupport

set_option linter.unusedSimpArgs false

namespace Veir.ArithCanonicalize.SelectMinMaxSupport
open Veir Veir.Data

theorem select_slt_smin (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .slt) a b) ⊒
      .int w (LLVM.Int.smin a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toInt ≠ y.toInt := by
          intro hh
          exact heq ((BitVec.toInt_inj).mp hh)
        by_cases hle : x.toInt ≤ y.toInt
        · have hlt : x.toInt < y.toInt := by omega
          have hnotgt : ¬ y.toInt < x.toInt := by omega
          have hnotge : ¬ y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toInt < x.toInt := by omega
          have hnotlt : ¬ x.toInt < y.toInt := by omega
          have hge : y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hgt, hle, hnotlt, hge]

theorem select_sle_smin (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .sle) a b) ⊒
      .int w (LLVM.Int.smin a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toInt ≠ y.toInt := by
          intro hh
          exact heq ((BitVec.toInt_inj).mp hh)
        by_cases hle : x.toInt ≤ y.toInt
        · have hlt : x.toInt < y.toInt := by omega
          have hnotgt : ¬ y.toInt < x.toInt := by omega
          have hnotge : ¬ y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toInt < x.toInt := by omega
          have hnotlt : ¬ x.toInt < y.toInt := by omega
          have hge : y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hgt, hle, hnotlt, hge]

theorem select_sgt_smax (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .sgt) a b) ⊒
      .int w (LLVM.Int.smax a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toInt ≠ y.toInt := by
          intro hh
          exact heq ((BitVec.toInt_inj).mp hh)
        by_cases hle : x.toInt ≤ y.toInt
        · have hlt : x.toInt < y.toInt := by omega
          have hnotgt : ¬ y.toInt < x.toInt := by omega
          have hnotge : ¬ y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toInt < x.toInt := by omega
          have hnotlt : ¬ x.toInt < y.toInt := by omega
          have hge : y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hgt, hle, hnotlt, hge]

theorem select_sge_smax (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .sge) a b) ⊒
      .int w (LLVM.Int.smax a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toInt ≠ y.toInt := by
          intro hh
          exact heq ((BitVec.toInt_inj).mp hh)
        by_cases hle : x.toInt ≤ y.toInt
        · have hlt : x.toInt < y.toInt := by omega
          have hnotgt : ¬ y.toInt < x.toInt := by omega
          have hnotge : ¬ y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toInt < x.toInt := by omega
          have hnotlt : ¬ x.toInt < y.toInt := by omega
          have hge : y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hgt, hle, hnotlt, hge]

theorem select_ult_umin (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .ult) a b) ⊒
      .int w (LLVM.Int.umin a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toNat ≠ y.toNat := by
          intro hh
          exact heq ((BitVec.toNat_inj).mp hh)
        by_cases hle : x.toNat ≤ y.toNat
        · have hlt : x.toNat < y.toNat := by omega
          have hnotgt : ¬ y.toNat < x.toNat := by omega
          have hnotge : ¬ y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toNat < x.toNat := by omega
          have hnotlt : ¬ x.toNat < y.toNat := by omega
          have hge : y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hgt, hle, hnotlt, hge]

theorem select_ule_umin (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .ule) a b) ⊒
      .int w (LLVM.Int.umin a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toNat ≠ y.toNat := by
          intro hh
          exact heq ((BitVec.toNat_inj).mp hh)
        by_cases hle : x.toNat ≤ y.toNat
        · have hlt : x.toNat < y.toNat := by omega
          have hnotgt : ¬ y.toNat < x.toNat := by omega
          have hnotge : ¬ y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toNat < x.toNat := by omega
          have hnotlt : ¬ x.toNat < y.toNat := by omega
          have hge : y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hgt, hle, hnotlt, hge]

theorem select_ugt_umax (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .ugt) a b) ⊒
      .int w (LLVM.Int.umax a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toNat ≠ y.toNat := by
          intro hh
          exact heq ((BitVec.toNat_inj).mp hh)
        by_cases hle : x.toNat ≤ y.toNat
        · have hlt : x.toNat < y.toNat := by omega
          have hnotgt : ¬ y.toNat < x.toNat := by omega
          have hnotge : ¬ y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toNat < x.toNat := by omega
          have hnotlt : ¬ x.toNat < y.toNat := by omega
          have hge : y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hgt, hle, hnotlt, hge]

theorem select_uge_umax (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .uge) a b) ⊒
      .int w (LLVM.Int.umax a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toNat ≠ y.toNat := by
          intro hh
          exact heq ((BitVec.toNat_inj).mp hh)
        by_cases hle : x.toNat ≤ y.toNat
        · have hlt : x.toNat < y.toNat := by omega
          have hnotgt : ¬ y.toNat < x.toNat := by omega
          have hnotge : ¬ y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toNat < x.toNat := by omega
          have hnotlt : ¬ x.toNat < y.toNat := by omega
          have hge : y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hgt, hle, hnotlt, hge]

theorem select_slt_smax_inverse (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .slt) b a) ⊒
      .int w (LLVM.Int.smax a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toInt ≠ y.toInt := by
          intro hh
          exact heq ((BitVec.toInt_inj).mp hh)
        by_cases hle : x.toInt ≤ y.toInt
        · have hlt : x.toInt < y.toInt := by omega
          have hnotgt : ¬ y.toInt < x.toInt := by omega
          have hnotge : ¬ y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toInt < x.toInt := by omega
          have hnotlt : ¬ x.toInt < y.toInt := by omega
          have hge : y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hgt, hle, hnotlt, hge]

theorem select_sle_smax_inverse (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .sle) b a) ⊒
      .int w (LLVM.Int.smax a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toInt ≠ y.toInt := by
          intro hh
          exact heq ((BitVec.toInt_inj).mp hh)
        by_cases hle : x.toInt ≤ y.toInt
        · have hlt : x.toInt < y.toInt := by omega
          have hnotgt : ¬ y.toInt < x.toInt := by omega
          have hnotge : ¬ y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toInt < x.toInt := by omega
          have hnotlt : ¬ x.toInt < y.toInt := by omega
          have hge : y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hgt, hle, hnotlt, hge]

theorem select_sgt_smin_inverse (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .sgt) b a) ⊒
      .int w (LLVM.Int.smin a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toInt ≠ y.toInt := by
          intro hh
          exact heq ((BitVec.toInt_inj).mp hh)
        by_cases hle : x.toInt ≤ y.toInt
        · have hlt : x.toInt < y.toInt := by omega
          have hnotgt : ¬ y.toInt < x.toInt := by omega
          have hnotge : ¬ y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toInt < x.toInt := by omega
          have hnotlt : ¬ x.toInt < y.toInt := by omega
          have hge : y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hgt, hle, hnotlt, hge]

theorem select_sge_smin_inverse (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .sge) b a) ⊒
      .int w (LLVM.Int.smin a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toInt ≠ y.toInt := by
          intro hh
          exact heq ((BitVec.toInt_inj).mp hh)
        by_cases hle : x.toInt ≤ y.toInt
        · have hlt : x.toInt < y.toInt := by omega
          have hnotgt : ¬ y.toInt < x.toInt := by omega
          have hnotge : ¬ y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toInt < x.toInt := by omega
          have hnotlt : ¬ x.toInt < y.toInt := by omega
          have hge : y.toInt ≤ x.toInt := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.smin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.slt, BitVec.sle,
            hgt, hle, hnotlt, hge]

theorem select_ult_umax_inverse (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .ult) b a) ⊒
      .int w (LLVM.Int.umax a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toNat ≠ y.toNat := by
          intro hh
          exact heq ((BitVec.toNat_inj).mp hh)
        by_cases hle : x.toNat ≤ y.toNat
        · have hlt : x.toNat < y.toNat := by omega
          have hnotgt : ¬ y.toNat < x.toNat := by omega
          have hnotge : ¬ y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toNat < x.toNat := by omega
          have hnotlt : ¬ x.toNat < y.toNat := by omega
          have hge : y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hgt, hle, hnotlt, hge]

theorem select_ule_umax_inverse (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .ule) b a) ⊒
      .int w (LLVM.Int.umax a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toNat ≠ y.toNat := by
          intro hh
          exact heq ((BitVec.toNat_inj).mp hh)
        by_cases hle : x.toNat ≤ y.toNat
        · have hlt : x.toNat < y.toNat := by omega
          have hnotgt : ¬ y.toNat < x.toNat := by omega
          have hnotge : ¬ y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toNat < x.toNat := by omega
          have hnotlt : ¬ x.toNat < y.toNat := by omega
          have hge : y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umax, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hgt, hle, hnotlt, hge]

theorem select_ugt_umin_inverse (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .ugt) b a) ⊒
      .int w (LLVM.Int.umin a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toNat ≠ y.toNat := by
          intro hh
          exact heq ((BitVec.toNat_inj).mp hh)
        by_cases hle : x.toNat ≤ y.toNat
        · have hlt : x.toNat < y.toNat := by omega
          have hnotgt : ¬ y.toNat < x.toNat := by omega
          have hnotge : ¬ y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toNat < x.toNat := by omega
          have hnotlt : ¬ x.toNat < y.toNat := by omega
          have hge : y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hgt, hle, hnotlt, hge]

theorem select_uge_umin_inverse (a b : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp a b .uge) b a) ⊒
      .int w (LLVM.Int.umin a b) := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val y =>
      by_cases heq : x = y
      · subst y
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hneq : x.toNat ≠ y.toNat := by
          intro hh
          exact heq ((BitVec.toNat_inj).mp hh)
        by_cases hle : x.toNat ≤ y.toNat
        · have hlt : x.toNat < y.toNat := by omega
          have hnotgt : ¬ y.toNat < x.toNat := by omega
          have hnotge : ¬ y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hlt, hle, hnotgt, hnotge]
        · have hgt : y.toNat < x.toNat := by omega
          have hnotlt : ¬ x.toNat < y.toNat := by omega
          have hge : y.toNat ≤ x.toNat := by omega
          simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.umin, LLVM.IntPred.eval,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, BitVec.ult, BitVec.ule,
            hgt, hle, hnotlt, hge]

end Veir.ArithCanonicalize.SelectMinMaxSupport
