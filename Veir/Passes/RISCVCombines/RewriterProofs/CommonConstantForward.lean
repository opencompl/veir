import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Rewriter.WfRewriter
import Veir.Data.LLVM.Int.Lemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret

namespace Veir

/-! ## Shared forward lemma for a freshly-created `llvm.mlir.constant`

Used by the MIR-combine correctness proofs that emit a single `llvm.mlir.constant` (e.g. the
`same_val_zero_*` combines). It is the `llvm.mlir.constant` analogue of `interpretOp_riscv_li_forward`
(`LowerConst.lean`). -/

/-- Nullary `llvm.mlir.constant` specialization of `interpretOp_forward`: an `llvm.mlir.constant`
op with no operands, a single `i{bw}` result type, and integer value attribute `intAttr` binds
that result to `.int bw (LLVM.Int.constant bw intAttr.value)`, leaving memory and every other
value unchanged. Mirrors `interpretOp_riscv_li_forward` (`LowerConst.lean`). -/
theorem interpretOp_llvm_constant_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {intType : IntegerType} {hIsTy}
    {intAttr : IntegerAttr}
    (hType : theOp.getOpType! ctx.raw = .llvm .mlir__constant)
    (hProps : (theOp.getProperties! ctx.raw (.llvm .mlir__constant)).value = .integer intAttr)
    (hOperands : theOp.getOperands! ctx.raw = #[])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.integerType intType, hIsTy⟩]) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.int intType.bitwidth
            (Data.LLVM.Int.constant intType.bitwidth intAttr.value)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[])
      (results := #[.int intType.bitwidth (Data.LLVM.Int.constant intType.bitwidth intAttr.value)])
      (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp only [interpretOp', Llvm.interpretOp', hProps, hResTypes, Interp]
          rfl)
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  have hNRes : 0 < theOp.getNumResults! ctx.raw := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hResTypes]; simp
  grind

end Veir
