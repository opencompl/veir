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

/-- `mod_arith` is uninterpreted (`interpretOp'` and `foldEvaluate` are both `none`),
    so it has fold-eligible semantics vacuously. The semantic anchor for `mod_arith`
    folds is the `mod-arith-to-arith` lowering. -/
theorem OpCode.foldEligibleSemantics_mod_arith (mop : Mod_Arith) :
    OpCode.FoldEligibleSemantics (.mod_arith mop) := by
  intro props resultTypes operands successors mem
  cases mop <;> rfl

/-! ## Every fold decision concerns an opcode with fold-eligible semantics -/

/-- The fold tables and the all-constant evaluation branch only answer for
    opcodes with fold-eligible semantics. -/
theorem OpCode.foldsTo_foldEligibleSemantics {opCode : OpCode}
    {props : HasOpInfo.propertiesOf opCode} {resultTypes : Array TypeAttr}
    {knownOperands : Array (Option RuntimeValue)} {outcome : FoldOutcome}
    (hFold : OpCode.foldsTo opCode props resultTypes knownOperands = some outcome) :
    opCode.FoldEligibleSemantics := by
  unfold OpCode.foldsTo at hFold
  split at hFold
  · exact OpCode.foldEligibleSemantics_of_isFoldEvaluable (by grind)
  · cases opCode with
    | arith aop => exact OpCode.foldEligibleSemantics_arith aop
    | llvm lop =>
      exact OpCode.foldEligibleSemantics_llvm lop
        (by cases lop <;> simp_all [Llvm.foldsTo, OpCode.isFoldEvaluable])
    | riscv rop =>
      exact OpCode.foldEligibleSemantics_riscv rop
        (by cases rop <;> simp_all [Riscv.foldsTo, OpCode.isFoldEvaluable])
    | mod_arith mop => exact OpCode.foldEligibleSemantics_mod_arith mop
    | _ => simp at hFold

/-- Every non-`noFold` decision concerns an opcode with fold-eligible semantics. -/
theorem foldDecision_foldEligibleSemantics {opCode : OpCode}
    {props : HasOpInfo.propertiesOf opCode} {resultTypes : Array TypeAttr}
    {knownOperands : Array (Option RuntimeValue)}
    (hDecision : foldDecision opCode props resultTypes knownOperands ≠ .noFold) :
    opCode.FoldEligibleSemantics := by
  unfold foldDecision at hDecision
  split at hDecision
  · exact absurd rfl hDecision
  · split at hDecision
    · exact absurd rfl hDecision
    · split at hDecision
      case h_1 hFold => exact absurd rfl hDecision
      case h_2 j hFold => exact OpCode.foldsTo_foldEligibleSemantics hFold
      case h_3 rv hFold => exact OpCode.foldsTo_foldEligibleSemantics hFold
      case h_4 hFold => exact OpCode.foldsTo_foldEligibleSemantics hFold

/-! ## The `interpretOp`-level bridges -/

/-- An operation with fold-eligible semantics is pure. -/
theorem OperationPtr.Pure.of_foldEligibleSemantics {op : OperationPtr} {ctx : IRContext OpCode}
    (hSem : (op.getOpType! ctx).FoldEligibleSemantics) : op.Pure ctx := by
  unfold OperationPtr.Pure
  intro operands memory₁ memory₂
  rw [hSem, hSem]
  cases foldEvaluate (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operands with
  | none => rfl
  | some result => cases result <;> rfl

/--
  Successful interpretation of an operation with fold-eligible semantics: the operands were fetched from
  the state, `foldEvaluate` on them succeeds with the operation's result values, no control
  flow is produced, and memory is unchanged. This upgrades `FoldDecision.Refines` (stated
  against `foldEvaluate`) to a statement about what actually runs.
-/
theorem interpretOp_ok_foldEvaluate {ctx : WfIRContext OpCode}
    {op : OperationPtr} {inBounds : op.InBounds ctx.raw}
    {state newState : InterpreterState ctx} {cf}
    (hSem : (op.getOpType! ctx.raw).FoldEligibleSemantics)
    (hinterp : interpretOp op state inBounds = some (.ok (newState, cf))) :
    ∃ actualOperands resValues,
      state.variables.getOperandValues op = some actualOperands ∧
      foldEvaluate (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) actualOperands = some (.ok resValues) ∧
      cf = none ∧
      newState.memory = state.memory ∧
      state.variables.setResultValues? op resValues = some newState.variables := by
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
  An operation with fold-eligible semantics triggers UB exactly when `foldEvaluate` reports UB on its
  fetched operand values.
-/
theorem interpretOp_ub_foldEvaluate {ctx : WfIRContext OpCode}
    {op : OperationPtr} {inBounds : op.InBounds ctx.raw}
    {state : InterpreterState ctx}
    (hSem : (op.getOpType! ctx.raw).FoldEligibleSemantics)
    (hinterp : interpretOp op state inBounds = some .ub) :
    ∃ actualOperands,
      state.variables.getOperandValues op = some actualOperands ∧
      foldEvaluate (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) actualOperands = some .ub := by
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
