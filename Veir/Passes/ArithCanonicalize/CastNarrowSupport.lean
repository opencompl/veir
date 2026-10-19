import Veir.Passes.ArithCanonicalize.CastIntermediateSupport

namespace Veir.ArithCanonicalize.CastNarrowSupport
open Veir Veir.Data

theorem truncate_signExtend_narrow (v : BitVec a) (hba : b < a) (hac : a < c) :
    (v.signExtend c).truncate b = v.truncate b := by
  ext i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth]
  rw [BitVec.getLsbD_signExtend]
  simp [show i < a by omega, show i < c by omega,
    BitVec.getLsbD_eq_getElem]

theorem truncate_zeroExtend_narrow (v : BitVec a) (hba : b < a) (hac : a < c) :
    (v.zeroExtend c).truncate b = v.truncate b := by
  simp only [BitVec.truncate_eq_setWidth]
  rw [BitVec.setWidth_setWidth_of_le]
  omega

theorem truncate_signExtend_recover (v : BitVec a) (hac : a < c) :
    (v.signExtend c).truncate a = v := by
  ext i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth]
  rw [BitVec.getLsbD_signExtend]
  simp [hi, show i < c by omega, BitVec.getLsbD_eq_getElem]

theorem truncate_zeroExtend_recover (v : BitVec a) (hac : a < c) :
    (v.zeroExtend c).truncate a = v := by
  simp only [BitVec.truncate_eq_setWidth]
  rw [BitVec.setWidth_setWidth_of_le]
  · simp
  · omega


theorem trunci_extsi_narrow (x : LLVM.Int a) (hba : b < a) (hac : a < c)
    (nsw nuw : Bool) :
    RuntimeValue.int b (LLVM.Int.trunc (LLVM.Int.sext x c hac) b nsw nuw (by omega)) ⊒
      .int b (LLVM.Int.trunc x b nsw nuw (by omega)) := by
  cases x with
  | poison => simp [LLVM.Int.sext, LLVM.Int.trunc, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val v =>
    let q := v.truncate b
    have hLow : (v.signExtend c).truncate b = q :=
      truncate_signExtend_narrow v hba hac
    have hs : q.signExtend c = v.signExtend c → q.signExtend a = v := by
      intro h
      have hh := congrArg (fun z : BitVec c => z.truncate a) h
      simpa only [CastIntermediateSupport.truncate_signExtend q hba hac,
        truncate_signExtend_recover v hac] using hh
    have hu : q.zeroExtend c = v.signExtend c → q.zeroExtend a = v := by
      intro h
      have hh := congrArg (fun z : BitVec c => z.truncate a) h
      simpa only [CastIntermediateSupport.truncate_zeroExtend q hba hac,
        truncate_signExtend_recover v hac] using hh
    by_cases hS : q.signExtend c = v.signExtend c <;>
      by_cases hU : q.zeroExtend c = v.signExtend c <;>
      cases nsw <;> cases nuw
    all_goals
      try have hSd := hs hS
      try have hUd := hu hU
      simp_all [LLVM.Int.sext, LLVM.Int.trunc, q, BitVec.truncate_eq_setWidth, RuntimeValue.isRefinedBy,
        isRefinedBy, Id.run, pure]


theorem trunci_extui_narrow (x : LLVM.Int a) (hba : b < a) (hac : a < c)
    (nneg nsw nuw : Bool) :
    RuntimeValue.int b (LLVM.Int.trunc (LLVM.Int.zext x c nneg hac) b nsw nuw (by omega)) ⊒
      .int b (LLVM.Int.trunc x b nsw nuw (by omega)) := by
  cases x with
  | poison => simp [LLVM.Int.zext, LLVM.Int.trunc, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val v =>
    let q := v.truncate b
    have hLow : (v.zeroExtend c).truncate b = q :=
      truncate_zeroExtend_narrow v hba hac
    have hs : q.signExtend c = v.zeroExtend c → q.signExtend a = v := by
      intro h
      have hh := congrArg (fun z : BitVec c => z.truncate a) h
      simpa only [CastIntermediateSupport.truncate_signExtend q hba hac,
        truncate_zeroExtend_recover v hac] using hh
    have hu : q.zeroExtend c = v.zeroExtend c → q.zeroExtend a = v := by
      intro h
      have hh := congrArg (fun z : BitVec c => z.truncate a) h
      simpa only [CastIntermediateSupport.truncate_zeroExtend q hba hac,
        truncate_zeroExtend_recover v hac] using hh
    by_cases hNeg : v.msb = true <;>
      by_cases hS : q.signExtend c = v.zeroExtend c <;>
      by_cases hU : q.zeroExtend c = v.zeroExtend c <;>
      cases nneg <;> cases nsw <;> cases nuw
    all_goals
      try have hSd := hs hS
      try have hUd := hu hU
      simp_all [LLVM.Int.zext, LLVM.Int.trunc, q, BitVec.truncate_eq_setWidth,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

end Veir.ArithCanonicalize.CastNarrowSupport
