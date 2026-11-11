module

import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.CombinerHelper
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Init.Data.Array.Basic
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide

/-! CTree validity of the lowerings of `lower?` and the narrowings of `narrowScalar?`.

`lowerSext` passes the source width as a 64-bit `g_sext_inreg` size, so it is wrong from width
`2^64`; `lowerFunnelShift` computes `urem` by the width, which is undefined at width 0. -/

namespace Veir.Legalization.CTreeProofs

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp'

attribute [local simp] GMIR.isTerminator GMIR.getEffects GMIR_RISCV.base

attribute [local implicit_reducible] TypeAttr Veir._propertiesOf GMIR.propertiesOf

/-- A count whose zero input is poison refines the count that is defined at zero. -/
private theorem ctlz_zero_poison {v w : Nat} (x : Data.LLVM.Int v) :
    resizeCount w (x.ctlz true) ⊒ resizeCount w (x.ctlz false) := by
  cases x with
  | poison => simp [resizeCount, Data.LLVM.Int.ctlz, Id.run]
  | val x => by_cases h : x = 0#v <;> simp [resizeCount, Data.LLVM.Int.ctlz, Id.run, h, isRefinedBy_eq, pure]

private theorem cttz_zero_poison {v w : Nat} (x : Data.LLVM.Int v) :
    resizeCount w (x.cttz true) ⊒ resizeCount w (x.cttz false) := by
  cases x with
  | poison => simp [resizeCount, Data.LLVM.Int.cttz, Id.run]
  | val x => by_cases h : x = 0#v <;> simp [resizeCount, Data.LLVM.Int.cttz, Id.run, h, isRefinedBy_eq, pure]

/-- Copied from `Veir.Passes.Legalization.Proofs`, where it is private. -/
private theorem uadde_lowering {w : Nat} (h : 1 < w) (x y : Data.LLVM.Int w) (c : Data.LLVM.Int 1) :
    uaddWithCarry x y c =
      let tmp := Data.LLVM.Int.add x y
      let carry := Data.LLVM.Int.icmp tmp x Data.LLVM.IntPred.ult
      let sum := Data.LLVM.Int.add tmp (Data.LLVM.Int.zext c w false h)
      let carry2 := Data.LLVM.Int.and (Data.LLVM.Int.icmp sum (Data.LLVM.Int.constant w 0) Data.LLVM.IntPred.eq) c
      (sum, Data.LLVM.Int.or carry carry2) := by
  cases x <;> cases y <;> cases c
  case val.val.val x y c =>
    obtain ⟨b, rfl⟩ := c.exists_eq_ofBool
    -- It carries if either `g_add` carries.
    simp [uaddWithCarry, Data.LLVM.Int.add, Data.LLVM.Int.icmp, Data.LLVM.Int.zext, Data.LLVM.Int.and, Data.LLVM.Int.or,
      Data.LLVM.Int.constant, Id.run, Data.LLVM.IntPred.eval, BitVec.ofBool_or_ofBool, BitVec.ofBool_and_ofBool,
      BitVec.carry_eq_uaddOverflow_or (by omega : 0 < w), BitVec.uaddOverflow_eq_ult_left x y,
      BitVec.uaddOverflow_setWidth_ofBool (by omega : 0 < w)]
  -- The other seven cases have a poison operand, so both sides reduce to poison.
  all_goals rfl

/-- Copied from `Veir.Passes.Legalization.Proofs`, where it is private. -/
private theorem usube_lowering {w : Nat} (h : 1 < w) (x y : Data.LLVM.Int w) (b : Data.LLVM.Int 1) :
    usubWithBorrow x y b =
      let tmp := Data.LLVM.Int.sub x y
      let borrow := Data.LLVM.Int.icmp tmp x Data.LLVM.IntPred.ugt
      let diff := Data.LLVM.Int.sub tmp (Data.LLVM.Int.zext b w false h)
      let borrow2 := Data.LLVM.Int.and (Data.LLVM.Int.icmp tmp (Data.LLVM.Int.constant w 0) Data.LLVM.IntPred.eq) b
      (diff, Data.LLVM.Int.or borrow borrow2) := by
  cases x <;> cases y <;> cases b
  case val.val.val x y b =>
    obtain ⟨b, rfl⟩ := b.exists_eq_ofBool
    -- It borrows if either `g_sub` borrows.
    simp [usubWithBorrow, Data.LLVM.Int.sub, Data.LLVM.Int.icmp, Data.LLVM.Int.zext, Data.LLVM.Int.and, Data.LLVM.Int.or,
      Data.LLVM.Int.constant, Id.run, Data.LLVM.IntPred.eval, BitVec.ofBool_or_ofBool, BitVec.ofBool_and_ofBool,
      BitVec.ult_setWidth_add_ofBool (by omega : 0 < w), BitVec.usubOverflow_eq_ult_sub x y,
      BitVec.usubOverflow_setWidth_ofBool (by omega : 0 < w)]
  -- The other seven cases have a poison operand, so both sides reduce to poison.
  all_goals rfl

/-- The zero constant of an integer attribute. -/
private theorem IntegerAttr.ofInt_zero_value (t : IntegerType) : (IntegerAttr.ofInt 0 t).value = 0 := by
  simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]

theorem lower_ctlz_zero_poison_valid :
    Puddle.CTree.Pattern.Valid (lowerZeroPoisonCount .g_ctlz_zero_poison .g_ctlz) := by
  proveLegalValid using ctlz_zero_poison

theorem lower_cttz_zero_poison_valid :
    Puddle.CTree.Pattern.Valid (lowerZeroPoisonCount .g_cttz_zero_poison .g_cttz) := by
  proveLegalValid using cttz_zero_poison

theorem lower_uadde_valid : Puddle.CTree.Pattern.Valid (lowerAddSubE true) := by
  proveLegalValid with simp_all [uadde_lowering, Data.LLVM.Int.constant, IntegerAttr.ofInt_zero_value]

theorem lower_usube_valid : Puddle.CTree.Pattern.Valid (lowerAddSubE false) := by
  proveLegalValid with simp_all [usube_lowering, Data.LLVM.Int.constant, IntegerAttr.ofInt_zero_value]

/-! ## Status of every lowering and narrowing -/

@[legalization_status]
theorem lower_sext_status :
    Status Unproven (lowerSext) :=
  .unproven .widthDependent

@[legalization_status]
theorem lower_zext_status :
    Status Unproven (lowerZext) :=
  .unproven .notYetProven

@[legalization_status]
theorem lower_fshl_status :
    Status Unproven (lowerFunnelShift true) :=
  .unproven .widthDependent

@[legalization_status]
theorem lower_fshr_status :
    Status Unproven (lowerFunnelShift false) :=
  .unproven .widthDependent

@[legalization_status]
theorem lower_ctlz_zero_poison_status :
    Status Unproven (lowerZeroPoisonCount .g_ctlz_zero_poison .g_ctlz) :=
  .proven lower_ctlz_zero_poison_valid

@[legalization_status]
theorem lower_cttz_zero_poison_status :
    Status Unproven (lowerZeroPoisonCount .g_cttz_zero_poison .g_cttz) :=
  .proven lower_cttz_zero_poison_valid

@[legalization_status]
theorem lower_uaddsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_uaddsat false true) :=
  .unproven .notYetProven

@[legalization_status]
theorem lower_usubsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_usubsat false false) :=
  .unproven .notYetProven

@[legalization_status]
theorem lower_saddsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_saddsat true true) :=
  .unproven .notYetProven

@[legalization_status]
theorem lower_ssubsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_ssubsat true false) :=
  .unproven .notYetProven

@[legalization_status]
theorem lower_sshlsat_status :
    Status Unproven (lowerShlSat true) :=
  .unproven .notYetProven

@[legalization_status]
theorem lower_ushlsat_status :
    Status Unproven (lowerShlSat false) :=
  .unproven .notYetProven

@[legalization_status]
theorem lower_uaddo_status :
    Status Unproven (lowerUAddSubO true) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem lower_usubo_status :
    Status Unproven (lowerUAddSubO false) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem lower_saddo_status :
    Status Unproven (lowerSAddSubO true) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem lower_ssubo_status :
    Status Unproven (lowerSAddSubO false) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem lower_uadde_status :
    Status Unproven (lowerAddSubE true) :=
  .proven lower_uadde_valid

@[legalization_status]
theorem lower_usube_status :
    Status Unproven (lowerAddSubE false) :=
  .proven lower_usube_valid

@[legalization_status]
theorem narrow_add_status (W : Nat) :
    Status Unproven (narrowAddSub true W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem narrow_sub_status (W : Nat) :
    Status Unproven (narrowAddSub false W) :=
  .unproven .needsTypedMatch

end Veir.Legalization.CTreeProofs
