module

public import Veir.Interpreter.ResultsConformLemmas

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.Basic
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV_Stack.OpInfo
import all Veir.Verifier
import all Veir.Verifier.Basic
import Veir.ForLean

public section

/-!
# The results of the `riscv_stack` operations conform to their types

`riscv_stack.alloca` returns one register, and the verifier gives it one result, of a register
type.
-/

namespace Veir

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

private theorem verifyPlainOpCounts_ok {o r : Nat}
    (h : op.verifyPlainOpCounts ctx opIn o r = .ok ()) : op.getNumResults! ctx.raw = r := by
  simp only [OperationPtr.verifyPlainOpCounts, OperationPtr.verifyOpCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · exact verifyNonOperandCounts_ok h

/-- Every result of an operation that `verifyRISCVRegisterTypes` accepts is a register. -/
private theorem verifyRISCVRegisterTypes_ok (h : op.verifyRISCVRegisterTypes ctx opIn = .ok ()) :
    ∀ i < op.getNumResults ctx.raw opIn,
      ∃ rt, ((op.getResult i).getType! ctx.raw).val = .registerType rt := by
  simp only [OperationPtr.verifyRISCVRegisterTypes] at h
  refine Except.forIn_range_ok _ (fun a s hs => ?_) (bind_ok_left (Except.ok_of_bind_ok h))
  split at hs
  · next _ hT =>
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    exact ⟨hs.symm, _, hT⟩
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs

/-- A register conforms to a register type. -/
private theorem reg_conforms_of_val {r : Data.RISCV.Reg} {ty : TypeAttr} {rt : RegisterType}
    (h : ty.val = .registerType rt) : (RuntimeValue.reg r).Conforms ty := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; trivial

/-- The results of a CTree run of every `riscv_stack` opcode conform to their types. -/
theorem OpCode.resultsConform_riscv_stack (stackOp : Riscv_Stack) :
    OpCode.ResultsConform (.riscv_stack stackOp) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType opVerif operands mem conforms vals mem' act h => ?_
  have hType! : op.getOpType! ctx.raw = .riscv_stack stackOp := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  rw [OperationPtr.interpretCTree_def!, hType!] at h
  simp only [CTree.interpretOp', CTree.MayReturn.monadLift_iff, interpretOp'] at h
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, hType!] at opVerif
  cases stackOp
  simp only [Riscv_Stack.verifyLocalInvariants] at opVerif
  have hN := verifyPlainOpCounts_ok (bind_ok_left opVerif)
  have h0 : 0 < op.getNumResults ctx.raw opIn := by
    rw [← OperationPtr.getNumResults!_eq_getNumResults opIn, hN]; omega
  obtain ⟨rt, hrt⟩ :=
    verifyRISCVRegisterTypes_ok (bind_ok_left (Except.ok_of_bind_ok opVerif)) 0 h0
  rw [resultType_eq h0] at hrt
  obtain ⟨r, rfl⟩ : ∃ r, vals = #[.reg r] := by
    simp only [Riscv_Stack.interpretOp'] at h
    obtain ⟨⟨m, a⟩, -, h⟩ := Interp.exists_of_bind_eq_ok h
    simp only [Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq] at h
    exact ⟨_, h.1.symm⟩
  refine ⟨by rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hN]; rfl, fun i hi => ?_⟩
  obtain rfl : i = 0 := by simpa using hi
  simpa using reg_conforms_of_val (r := r) hrt

instance (stackOp : Riscv_Stack) : ResultsConform (.riscv_stack stackOp) :=
  ⟨OpCode.resultsConform_riscv_stack stackOp⟩

end Veir

end
