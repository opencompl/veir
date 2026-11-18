module

public import Veir.Interpreter.ResultsConformLemmas

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.Basic
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Verifier
import all Veir.Verifier.Basic
import Veir.ForLean

public section

/-!
# The results of the `gmir_riscv` operations conform to their types

A `gmir_riscv` operation returns one 64-bit integer, and the verifier gives it one result, of type
`i64`.
-/

namespace Veir

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

private theorem verifyPlainOpCounts_ok {o r : Nat}
    (h : op.verifyPlainOpCounts ctx opIn o r = .ok ()) : op.getNumResults! ctx.raw = r := by
  simp only [OperationPtr.verifyPlainOpCounts, OperationPtr.verifyOpCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · exact verifyNonOperandCounts_ok h

/-- A type that `verifyI64` accepts is a 64-bit integer type. -/
private theorem verifyI64_ok {ty : TypeAttr} {msg : String} (h : ty.verifyI64 msg = .ok ()) :
    ∃ it : IntegerType, ty.val = .integerType it ∧ it.bitwidth = 64 := by
  simp only [TypeAttr.verifyI64] at h
  split at h
  · exact ⟨_, ‹_›, rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A verified `gmir_riscv` operation has one result, of type `i64`. -/
private theorem gmirRiscv_verify {gOp : GMIR_RISCV}
    (h : GMIR_RISCV.verifyLocalInvariants gOp op ctx opIn = .ok ()) :
    op.getNumResults! ctx.raw = 1 ∧
      ∃ it : IntegerType, ((op.getResult 0).getType! ctx.raw).val = .integerType it ∧
        it.bitwidth = 64 := by
  simp only [GMIR_RISCV.verifyLocalInvariants] at h
  cases gOp <;> simp only at h
  all_goals first
    | (have h₁ := Except.ok_left_of_bind_ok h
       simp only [OperationPtr.verifyIntegerBinop] at h₁
       exact ⟨verifyPlainOpCounts_ok (bind_ok_left h₁), verifyI64_ok (Except.ok_of_bind_ok h)⟩)
    | (obtain ⟨_, h₁, h₂⟩ := Except_bind_ok_iff.mp h
       simp only [OperationPtr.verifyIntegerUnop] at h₁
       exact ⟨verifyPlainOpCounts_ok (bind_ok_left h₁), verifyI64_ok h₂⟩)

/-- The results of a CTree run of every `gmir_riscv` opcode conform to their types. -/
theorem OpCode.resultsConform_gmir_riscv (gOp : GMIR_RISCV) :
    OpCode.ResultsConform (.gmir_riscv gOp) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType opVerif operands mem conforms vals mem' act h => ?_
  have hType! : op.getOpType! ctx.raw = .gmir_riscv gOp := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  rw [OperationPtr.interpretCTree_def!, hType!] at h
  simp only [CTree.interpretOp', CTree.MayReturn.monadLift_iff, interpretOp'] at h
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, hType!] at opVerif
  obtain ⟨hN, it, hT, hw⟩ := gmirRiscv_verify opVerif
  have h0 : 0 < op.getNumResults ctx.raw opIn := by
    rw [← OperationPtr.getNumResults!_eq_getNumResults opIn, hN]; omega
  rw [resultType_eq h0] at hT
  obtain ⟨x, rfl⟩ : ∃ x, vals = #[.int 64 x] := by
    simp only [GMIR_RISCV.interpretOp'] at h
    repeat' (first
      | (obtain ⟨_, -, h⟩ := Interp.exists_of_bind_eq_ok h)
      | split at h)
    all_goals first
      | (simp at h; done)
      | (simp only [Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq] at h; exact ⟨_, h.1.symm⟩)
  refine ⟨by rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hN]; rfl, fun i hi => ?_⟩
  obtain rfl : i = 0 := by simpa using hi
  simpa using int_conforms_of_val (x := x) hT hw

instance (gOp : GMIR_RISCV) : ResultsConform (.gmir_riscv gOp) :=
  ⟨OpCode.resultsConform_gmir_riscv gOp⟩

end Veir

end
