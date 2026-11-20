module

public import Veir.Interpreter.Lemmas
public import Veir.Interpreter.ResultsConformLemmas
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

/-!
# The results of RISC-V operations conform to their types

A verified RISC-V operation returns, if its interpretation succeeds, results that conform to its
result types (`OpCode.resultsConform`). Every result of a RISC-V operation is a register, the
verifier makes every result type `!riscv.reg`, and a store has no result where every other opcode
has one.
-/

namespace Veir

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

/--
The RISC-V opcodes that load from memory. It is reducible, so that instance resolution decides it
for a concrete opcode.
-/
@[reducible]
def Riscv.isLoad : Riscv → Bool
  | .ld | .lw | .lwu | .lh | .lhu | .lb | .lbu => true
  | _ => false

/-- Unfold `Riscv.isLoad`, whose body modules importing this one do not see. -/
theorem Riscv.isLoad_eq (opT : Riscv) :
    opT.isLoad = match opT with
      | .ld | .lw | .lwu | .lh | .lhu | .lb | .lbu => true
      | _ => false := by
  cases opT <;> rfl

/-- The number of results of a RISC-V opcode: none for a store, one otherwise. -/
def Riscv.numResults : Riscv → Nat
  | .sd | .sw | .sh | .sb => 0
  | _ => 1

/-- A RISC-V load has a single result. -/
theorem Riscv.numResults_of_isLoad {opT : Riscv} (h : opT.isLoad = true) :
    opT.numResults = 1 := by
  cases opT <;> first | rfl | simp at h

/-- A register conforms to a register type. -/
private theorem reg_conforms_of_val {r : Data.RISCV.Reg} {ty : TypeAttr}
    (h : ∃ rt, ty.val = .registerType rt) : (RuntimeValue.reg r).Conforms ty := by
  obtain ⟨a, _⟩ := ty; obtain ⟨rt, h⟩ := h; simp only at h; subst h; trivial

/-! ## Interpretation -/

/--
A RISC-V operation that interprets successfully produces register results and no
control flow action.
-/
private theorem Riscv.interpretOp'_ok_results {opType : Riscv} {properties : propertiesOf opType}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {blockOperands : Array BlockPtr}
    {mem mem' : MemoryState} {vals : Array RuntimeValue} {act : Option ControlFlowAction}
    (h : Riscv.interpretOp' opType properties resultTypes operands blockOperands mem
      = .ok (vals, mem', act)) :
    ((∃ r, vals = #[.reg r]) ∨ vals = #[]) ∧ act = none := by
  cases opType <;> simp only [Riscv.interpretOp'] at h <;> grind

/-- A RISC-V operation returns as many registers as its opcode has results. -/
private theorem Riscv.interpretOp'_ok_vals {opT : Riscv} {properties : propertiesOf opT}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {bs : Array BlockPtr}
    {mem mem' : MemoryState} {vals : Array RuntimeValue} {act : Option ControlFlowAction}
    (h : Riscv.interpretOp' opT properties resultTypes operands bs mem = .ok (vals, mem', act)) :
    vals.size = opT.numResults ∧ ∀ v ∈ vals, ∃ r, v = .reg r := by
  refine ⟨?_, ?_⟩
  · cases opT <;> simp only [Riscv.interpretOp'] at h <;> grind [Riscv.numResults]
  · rcases (Riscv.interpretOp'_ok_results h).1 with ⟨r, rfl⟩ | rfl <;> simp

/-! ## Verifier -/

private theorem riscvVerified {opT : Riscv} (hType : op.getOpType! ctx.raw = .riscv opT)
    (hV : op.Verified ctx opIn) : Riscv.verifyLocalInvariants opT op ctx opIn = .ok () := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, hType] at hV
  exact hV

private theorem verifyPlainOpCounts_ok {o r : Nat}
    (h : op.verifyPlainOpCounts ctx opIn o r = .ok ()) : op.getNumResults! ctx.raw = r := by
  simp only [OperationPtr.verifyPlainOpCounts, OperationPtr.verifyOpCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · exact verifyNonOperandCounts_ok h

/-- A verified RISC-V operation has as many results as its opcode. -/
theorem riscv_verify_numResults {opT : Riscv}
    (h : Riscv.verifyLocalInvariants opT op ctx opIn = .ok ()) :
    op.getNumResults! ctx.raw = opT.numResults := by
  unfold Riscv.verifyLocalInvariants at h
  have h' := Except.ok_of_bind_ok h
  cases opT <;>
    simp only [OperationPtr.verifyRISCVimm12, OperationPtr.verifyRISCVuimm5,
      OperationPtr.verifyRISCVuimm6, OperationPtr.verifyRISCVneg] at h' <;>
    first
      | exact verifyPlainOpCounts_ok (bind_ok_left h')
      | exact verifyPlainOpCounts_ok (bind_ok_left (bind_ok_left h'))

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

/-! ## The opcodes -/

/--
Results that are registers, and as many as the opcode has, conform to the result types of a
verified RISC-V operation: the verifier requires every result type to be a register type.

The CTree of a RISC-V load chooses the bits of its result that memory marks poison, so this is
what carries conformance over to each value it may choose.
-/
theorem Riscv.regs_results_conform (opT : Riscv)
    (hType : op.getOpType! ctx.raw = .riscv opT) (hV : op.Verified ctx opIn)
    (hs : vals.size = opT.numResults) (hr : ∀ v ∈ vals, ∃ r, v = .reg r) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  have hVL := riscvVerified hType hV
  have hN := riscv_verify_numResults hVL
  have hRegs := verifyRISCVRegisterTypes_ok (bind_ok_left hVL)
  have hsN : vals.size = op.getNumResults ctx.raw opIn := by
    rw [← OperationPtr.getNumResults!_eq_getNumResults opIn, hN, hs]
  refine ⟨by rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hN, hs], fun i hi => ?_⟩
  obtain ⟨r, hv⟩ := hr _ (Array.getElem_mem hi)
  have hT := hRegs i (hsN ▸ hi)
  rw [resultType_eq (hsN ▸ hi)] at hT
  rw [getElem!_pos vals i hi, hv]
  exact reg_conforms_of_val hT

/--
A verified RISC-V operation returns, if its `Interp` interpretation succeeds, results that
conform to its result types.
-/
theorem Riscv.interpretOp'_results_conform (opT : Riscv)
    (hType : op.getOpType! ctx.raw = .riscv opT) (hV : op.Verified ctx opIn)
    (h : Riscv.interpretOp' opT (op.getProperties! ctx.raw (OpCode.riscv opT))
      (op.getResultTypes! ctx.raw) operands bs mem = .ok (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) :=
  have ⟨hs, hr⟩ := Riscv.interpretOp'_ok_vals h
  Riscv.regs_results_conform opT hType hV hs hr

end Veir

end
