import Veir.IR.WellFormed
import Veir.Rewriter.WfRewriter
import Veir.Dominance
import Veir.Passes.Matching
import Veir.Verifier
import Veir.Passes.InstructionSelection.Common
import Veir.Interpreter

/-!
# Forward interpretation lemmas for instruction-selection rewrite proofs

This file collects `interpretOp_forward` specializations tailored to the operations that show up in
RISC-V instruction-selection lowerings. Each lemma fixes the shape of a specific op (cast-to-register,
cast-back, and unary register-to-register `riscv` ops) and reduces its one-step interpretation to a
concrete result binding, so the surrounding rewrite proofs can reason about semantics without
unfolding the interpreter by hand.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {rawCtx rawCtx' : IRContext OpInfo} {ctx ctx' : WfIRContext OpInfo}

/-- Cast-to-register specialization of `interpretOp_forward`: `castOp` is a
`builtin.unrealized_conversion_cast` with single operand `v` (holding an `i{bw}` value `x`) and a
single `!riscv.reg` result. Interpreting it always succeeds, leaves memory untouched, binds the
result to `.reg (LLVM.Int.toReg x)`, and leaves every non-result value unchanged. -/
theorem interpretOp_castToReg_forward
    {ctx : WfIRContext OpCode} {castOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : castOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {bw : Nat} {x : Data.LLVM.Int bw}
    (hType : castOp.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hOperands : castOp.getOperands! ctx.raw = #[v])
    (hResTypes : castOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.int bw x)) :
    ∃ state', interpretOp castOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (.reg (LLVM.Int.toReg x)) ∧
      (∀ v', v' ∉ castOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVar⟩ :=
    interpretOp_forward (op := castOp) (state := state) (inBounds := inBounds)
      (vals := #[.int bw x]) (results := #[.reg (LLVM.Int.toReg x)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [hResTypes, interpretOp', pure, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Cast-back specialization of `interpretOp_forward`, symmetric to
`interpretOp_castToReg_forward`: `castOp` is a `builtin.unrealized_conversion_cast` with single
operand `v` (holding a register value `r`) and a single `i{bw}` result. Interpreting it always
succeeds, leaves memory untouched, binds the result to `.int bw (RISCV.Reg.toInt r bw)`, and
leaves every non-result value unchanged. -/
theorem interpretOp_castBack_forward
    {ctx : WfIRContext OpCode} {castOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : castOp.InBounds ctx.raw} {v : ValuePtr} {intTy : IntegerType} {hIsTy}
    {r : Data.RISCV.Reg}
    (hType : castOp.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hOperands : castOp.getOperands! ctx.raw = #[v])
    (hResTypes : castOp.getResultTypes! ctx.raw = #[⟨.integerType intTy, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp castOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (.int intTy.bitwidth (RISCV.Reg.toInt r intTy.bitwidth)) ∧
      (∀ v', v' ∉ castOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVar⟩ :=
    interpretOp_forward (op := castOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r])
      (results := #[.int intTy.bitwidth (RISCV.Reg.toInt r intTy.bitwidth)])
      (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [hResTypes, interpretOp', pure, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Unary register-to-register `riscv` op specialization of `interpretOp_forward`: `theOp` is any
`riscv` op `rop` whose interpretation maps a single register operand `r` to `f r` (hypothesis
`hSem`, discharged by `rfl` at each concrete opcode), with a single `!riscv.reg` result.
Interpreting it always succeeds, leaves memory untouched, binds the result to `.reg (f r)`, and
leaves every non-result value unchanged. This covers `riscv.clz`/`clzw`/`ctz`/`ctzw`/`cpop`/
`cpopw` and any future unary Zbb op. -/
theorem interpretOp_riscv_unaryReg_forward
    {ctx : WfIRContext OpCode} {rop : Riscv} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {r : Data.RISCV.Reg} {f : Data.RISCV.Reg → Data.RISCV.Reg}
    (hSem : ∀ (props : HasDialectOpInfo.propertiesOf rop) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' rop props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (f r)], mem, none)))
    (hType : theOp.getOpType! ctx.raw = .riscv rop)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (f r)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.reg (f r)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [interpretOp', hSem, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind
