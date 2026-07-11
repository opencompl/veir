import Veir.Interpreter.EquationLemma
import Veir.Fold.Semantics

/-!
  # Bridging `foldEvaluate` to `interpretOp`

  Layer B of the folding soundness proofs (see `Veir.Fold.Semantics`).
  `FoldDecision.Refines` is stated against `foldEvaluate` — interpretation with
  a dummy memory and no successors — while the interpreter runs operations with
  `interpretOp` on a real state. This file closes that gap.

  The central notion is `OpCode.FoldEligibleSemantics`: interpreting the opcode
  with *any* memory and successors equals `foldEvaluate` with the memory
  threaded through unchanged and no control-flow action. This single equation
  packages the three facts a fold needs about the operation it replaces:

  * memory-independence (the fold may ignore the heap);
  * successor-irrelevance (the fold may ignore block operands); and
  * control-flow-freeness (replacing the op by a value drops no control flow).

  It is proved for every opcode `OpCode.isFoldEvaluable` accepts, and every
  opcode the fold tables answer for is fold-evaluable, so every non-`noFold`
  decision is covered.
-/

namespace Veir

/--
  Interpreting the opcode with any memory and successors equals `foldEvaluate`
  with the memory threaded through unchanged and no control-flow action.
-/
def OpCode.FoldEligibleSemantics (opCode : OpCode) : Prop :=
  ∀ (props : HasOpInfo.propertiesOf opCode) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr) (mem : MemoryState),
    interpretOp' opCode props resultTypes operands successors mem =
      Interp.map (fun results => (results, mem, none))
        (foldEvaluate opCode props resultTypes operands)

set_option linter.unusedSimpArgs false in
/-- Every `arith` opcode has fold-eligible semantics. -/
theorem OpCode.foldEligibleSemantics_arith (aop : Arith) :
    OpCode.FoldEligibleSemantics (.arith aop) := by
  intro props resultTypes operands successors mem
  cases aop <;>
  · simp only [interpretOp', foldEvaluate, Arith.interpretOp']
    repeat' split
    all_goals
      simp_all [Interp.map, Interp.ub, Option.map, UBOr.map, bind, pure]

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- Every fold-evaluable `llvm` opcode has fold-eligible semantics. -/
theorem OpCode.foldEligibleSemantics_llvm (lop : Llvm)
    (hElig : OpCode.isFoldEvaluable (.llvm lop)) :
    OpCode.FoldEligibleSemantics (.llvm lop) := by
  intro props resultTypes operands successors mem
  cases lop <;> first
    | exact absurd hElig (by decide)
    | (simp only [interpretOp', foldEvaluate, Llvm.interpretOp']
       repeat' split
       all_goals
         simp_all [Interp.map, Interp.ub, Option.map, UBOr.map, bind, pure]
       done)

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- Every fold-evaluable `riscv` opcode has fold-eligible semantics. -/
theorem OpCode.foldEligibleSemantics_riscv (rop : Riscv)
    (hElig : OpCode.isFoldEvaluable (.riscv rop)) :
    OpCode.FoldEligibleSemantics (.riscv rop) := by
  intro props resultTypes operands successors mem
  cases rop <;> first
    | exact absurd hElig (by decide)
    | (simp only [interpretOp', foldEvaluate, Riscv.interpretOp']
       repeat' split
       all_goals
         simp_all [Interp.map, Interp.ub, Option.map, UBOr.map, bind, pure]
       done)

/-- Every fold-evaluable opcode has fold-eligible semantics. -/
theorem OpCode.foldEligibleSemantics_of_isFoldEvaluable {opCode : OpCode}
    (hElig : opCode.isFoldEvaluable) : opCode.FoldEligibleSemantics := by
  cases opCode with
  | arith aop => exact OpCode.foldEligibleSemantics_arith aop
  | llvm lop => exact OpCode.foldEligibleSemantics_llvm lop hElig
  | riscv rop => exact OpCode.foldEligibleSemantics_riscv rop hElig
  | _ => simp [OpCode.isFoldEvaluable] at hElig

/-! ## Every fold decision concerns a fold-evaluable opcode -/

/-- The fold tables and the all-constant evaluation branch only answer for
    fold-evaluable opcodes. -/
theorem OpCode.foldsTo_isFoldEvaluable {opCode : OpCode}
    {props : HasOpInfo.propertiesOf opCode}
    {knownOperands : Array (Option RuntimeValue)} {outcome : FoldOutcome}
    (hFold : OpCode.foldsTo opCode props knownOperands = some outcome) :
    opCode.isFoldEvaluable := by
  unfold OpCode.foldsTo at hFold
  split at hFold
  · grind
  · cases opCode with
    | arith aop => rfl
    | llvm lop => cases lop <;> simp_all [Llvm.foldsTo, OpCode.isFoldEvaluable]
    | riscv rop => cases rop <;> simp_all [Riscv.foldsTo, OpCode.isFoldEvaluable]
    | _ => simp at hFold

/-- Every non-`noFold` decision concerns a fold-evaluable opcode. -/
theorem foldDecision_isFoldEvaluable {opCode : OpCode}
    {props : HasOpInfo.propertiesOf opCode} {resultTypes : Array TypeAttr}
    {knownOperands : Array (Option RuntimeValue)}
    (hDecision : foldDecision opCode props resultTypes knownOperands ≠ .noFold) :
    opCode.isFoldEvaluable := by
  unfold foldDecision at hDecision
  split at hDecision
  · exact absurd rfl hDecision
  · split at hDecision
    · exact absurd rfl hDecision
    · split at hDecision
      case h_1 hFold => exact absurd rfl hDecision
      case h_2 j hFold => exact OpCode.foldsTo_isFoldEvaluable hFold
      case h_3 rv hFold => exact OpCode.foldsTo_isFoldEvaluable hFold
      case h_4 hFold => exact OpCode.foldsTo_isFoldEvaluable hFold

/-! ## The `interpretOp`-level bridges -/

/-- A fold-evaluable operation is pure. -/
theorem OperationPtr.Pure.of_isFoldEvaluable {op : OperationPtr} {ctx : IRContext OpCode}
    (hElig : (op.getOpType! ctx).isFoldEvaluable) : op.Pure ctx := by
  have hSem := OpCode.foldEligibleSemantics_of_isFoldEvaluable hElig
  unfold OperationPtr.Pure
  intro operands memory₁ memory₂
  rw [hSem, hSem]
  cases foldEvaluate (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operands with
  | none => rfl
  | some result => cases result <;> rfl

/--
  Successful interpretation of a fold-evaluable operation: the operands were fetched from
  the state, `foldEvaluate` on them succeeds with the operation's result values, no control
  flow is produced, and memory is unchanged. This upgrades `FoldDecision.Refines` (stated
  against `foldEvaluate`) to a statement about what actually runs.
-/
theorem interpretOp_ok_foldEvaluate {ctx : WfIRContext OpCode}
    {op : OperationPtr} {inBounds : op.InBounds ctx.raw}
    {state newState : InterpreterState ctx} {cf}
    (hElig : (op.getOpType! ctx.raw).isFoldEvaluable)
    (hinterp : interpretOp op state inBounds = some (.ok (newState, cf))) :
    ∃ actualOperands resValues,
      state.variables.getOperandValues op = some actualOperands ∧
      foldEvaluate (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) actualOperands = some (.ok resValues) ∧
      cf = none ∧
      newState.memory = state.memory ∧
      state.variables.setResultValues? op resValues = some newState.variables := by
  have hSem := OpCode.foldEligibleSemantics_of_isFoldEvaluable hElig
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues, resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  refine ⟨operandValues, resValues, hOV, ?_⟩
  simp only [OperationPtr.interpret] at hInterp'
  rw [hSem] at hInterp'
  cases hFe : foldEvaluate (op.getOpType! ctx.raw)
      (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
      (op.getResultTypes! ctx.raw) operandValues with
  | none =>
    rw [hFe] at hInterp'
    simp only [Interp.map, Option.map] at hInterp'
    exact nomatch hInterp'
  | some result =>
    cases result with
    | ub =>
      rw [hFe] at hInterp'
      simp only [Interp.map, Option.map, UBOr.map] at hInterp'
      exact nomatch hInterp'
    | ok results =>
      rw [hFe] at hInterp'
      simp only [Interp.map, Option.map, UBOr.map] at hInterp'
      obtain ⟨rfl, rfl, rfl⟩ :
          results = resValues ∧ mem' = state.memory ∧ cf = none := by grind
      subst hNew
      exact ⟨rfl, rfl, rfl, hSet⟩

/--
  A fold-evaluable operation triggers UB exactly when `foldEvaluate` reports UB on its
  fetched operand values.
-/
theorem interpretOp_ub_foldEvaluate {ctx : WfIRContext OpCode}
    {op : OperationPtr} {inBounds : op.InBounds ctx.raw}
    {state : InterpreterState ctx}
    (hElig : (op.getOpType! ctx.raw).isFoldEvaluable)
    (hinterp : interpretOp op state inBounds = some .ub) :
    ∃ actualOperands,
      state.variables.getOperandValues op = some actualOperands ∧
      foldEvaluate (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) actualOperands = some .ub := by
  have hSem := OpCode.foldEligibleSemantics_of_isFoldEvaluable hElig
  rw [interpretOp_ub_iff] at hinterp
  obtain ⟨operandValues, hOV, hInterp'⟩ := hinterp
  refine ⟨operandValues, hOV, ?_⟩
  simp only [OperationPtr.interpret] at hInterp'
  rw [hSem] at hInterp'
  cases hFe : foldEvaluate (op.getOpType! ctx.raw)
      (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
      (op.getResultTypes! ctx.raw) operandValues with
  | none =>
    rw [hFe] at hInterp'
    simp only [Interp.map, Option.map] at hInterp'
    exact nomatch hInterp'
  | some result =>
    cases result with
    | ub => rfl
    | ok results =>
      rw [hFe] at hInterp'
      simp only [Interp.map, Option.map, UBOr.map] at hInterp'
      exact nomatch hInterp'

end Veir
