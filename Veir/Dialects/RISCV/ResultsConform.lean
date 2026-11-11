module

public import Veir.Interpreter.Lemmas
public import Veir.Dialects.RISCV.Monotonicity
public import Veir.Verifier
import all Veir.Verifier.Basic
import all Veir.Verifier.Lemmas
import all Veir.Verifier
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Interpreter.Basic
import all Veir.IR.Basic
import all Veir.IR.OpCode
import all Veir.IR.Attribute
import Veir.ForLean

public section

namespace Veir

/-- RISC-V execution checks result conformance, including the value constraint on x0. -/
theorem OpCode.resultsConform_riscv (opT : Riscv) : OpCode.resultsConform (.riscv opT) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType _ operands vals mem mem' act _ h => ?_
  have hType! : op.getOpType! ctx.raw = .riscv opT := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  simp only [OperationPtr.interpret] at h
  rw [hType!] at h
  simp only [Veir.interpretOp', checkResultTypes_ok_iff] at h
  exact h.2

/--
info: 'Veir.OpCode.resultsConform_riscv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OpCode.resultsConform_riscv

instance (op : Riscv) : ResultsConform (.riscv op) :=
  ⟨OpCode.resultsConform_riscv op⟩

end Veir

end
