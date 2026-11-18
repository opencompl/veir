module

public import Veir.Interpreter.Basic
public import Veir.Verifier

import all Veir.Dialects.GMIR.OpInfo
import all Veir.Verifier
import all Veir.Verifier.Basic
import Veir.Data.LLVM.Int.Lemmas

public section

namespace Veir

/-- `g_br` succeeds exactly when it has one successor, which it branches to with its operands. -/
theorem interpretOp'_gmir_g_br_eq_ok_iff {properties : propertiesOf (OpCode.gmir .g_br)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem mem' : MemoryState} {layout : DataLayout} {results : Array RuntimeValue}
    {action : Option ControlFlowAction} :
    interpretOp' (.gmir .g_br) properties resultTypes operands successors mem layout =
        .ok (results, mem', action) ↔
      ∃ dest, successors = #[dest] ∧ results = #[] ∧ mem' = mem ∧
        action = some (.branch operands dest) := by
  grind [interpretOp', GMIR.interpretOp', List.eq_toArray_iff]

/--
  `g_brcond` succeeds exactly when it has two successors, a condition that is an
  integer and not poison, and a count of the operands of its first successor. It
  then branches to the first successor with those operands when the condition is
  not zero, and to the second with the rest otherwise.
-/
theorem interpretOp'_gmir_g_brcond_eq_ok_iff {properties : propertiesOf (OpCode.gmir .g_brcond)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem mem' : MemoryState} {layout : DataLayout} {results : Array RuntimeValue}
    {action : Option ControlFlowAction} :
    interpretOp' (.gmir .g_brcond) properties resultTypes operands successors mem layout =
        .ok (results, mem', action) ↔
      ∃ destTrue destFalse w, ∃ cond : BitVec w, ∃ n, successors = #[destTrue, destFalse] ∧
        operands[0]? = some (.int w (.val cond)) ∧
        properties.operandSegmentSizes.values[1]? = some n ∧
        results = #[] ∧ mem' = mem ∧
        action = some (if cond ≠ 0 then .branch (operands.extract 1 (n.toNat + 1)) destTrue
          else .branch (operands.extract (n.toNat + 1) operands.size) destFalse) := by
  simp only [interpretOp', GMIR.interpretOp']
  repeat' split
  all_goals grind [List.eq_toArray_iff]

/--
  `g_icmp` compares two integers of the same width. A result that is not poison
  comes from operands that are not poison, and is not zero exactly when the
  predicate holds.
-/
theorem interpretOp'_gmir_g_icmp_eq_ok {properties : propertiesOf (OpCode.gmir .g_icmp)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem mem' : MemoryState} {layout : DataLayout} {results : Array RuntimeValue}
    {action : Option ControlFlowAction}
    (h : interpretOp' (.gmir .g_icmp) properties resultTypes operands successors mem layout =
      .ok (results, mem', action)) :
    ∃ bw, ∃ x y : Data.LLVM.Int bw, ∃ w, ∃ c : Data.LLVM.Int w,
      operands = #[.int bw x, .int bw y] ∧ results = #[.int w c] ∧ mem' = mem ∧ action = none ∧
      ∀ v, c = .val v → ∃ x' y', x = .val x' ∧ y = .val y' ∧
        (v ≠ 0 ↔ Data.LLVM.IntPred.eval properties.predicate x' y' = true) := by
  simp only [interpretOp', GMIR.interpretOp'] at h
  repeat' split at h
  all_goals (try simp at h)
  all_goals
    rename_i bw x bw' y hOps hBw _ _ _ _ _ _ hLt
    obtain rfl : bw' = bw := by simpa using hBw
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨_, x, y, _, _, by simpa using congrArg List.toArray hOps, rfl, rfl, rfl, fun v hv => ?_⟩
    cases x <;> cases y <;> simp at hv ⊢
    subst hv
    cases Data.LLVM.IntPred.eval _ _ _ <;> simp
    all_goals
      intro hEq
      have := congrArg (·.getLsbD 0) hEq
      simp at this
      omega

/-- A `g_constant` of an integer result type gives the integer that its value attribute holds. -/
theorem interpretOp'_gmir_g_constant_eq_ok {properties : propertiesOf (OpCode.gmir .g_constant)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem mem' : MemoryState} {layout : DataLayout} {results : Array RuntimeValue}
    {action : Option ControlFlowAction} {type : TypeAttr} {t : IntegerType}
    (hType : resultTypes[0]? = some type) (hVal : type.val = .integerType t)
    (h : interpretOp' (.gmir .g_constant) properties resultTypes operands successors mem layout =
      .ok (results, mem', action)) :
    results = #[.int t.bitwidth (.val (BitVec.ofInt t.bitwidth properties.value.value))] ∧
      mem' = mem ∧ action = none := by
  simp only [interpretOp', GMIR.interpretOp', hType, hVal] at h
  simp at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- A `g_load` does not branch or return. -/
theorem gmir_g_load_action {properties : propertiesOf (OpCode.gmir .g_load)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue}
    {blockOperands : Array BlockPtr} {mem : MemoryState} {results : Array RuntimeValue}
    {mem' : MemoryState} {action : Option ControlFlowAction}
    (h : GMIR.interpretOp' .g_load properties resultTypes operands blockOperands mem =
      .ok (results, mem', action)) : action = none := by
  simp only [GMIR.interpretOp', bind, pure] at h
  repeat' split at h
  all_goals grind

/-- A terminator that passes its count check has no results and no regions. -/
theorem OperationPtr.verifyTerminatorCounts_ok {OpInfo : Type} [HasOpInfo OpInfo]
    {ctx : WfIRContext OpInfo} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} {n : Nat}
    (h : op.verifyTerminatorCounts ctx opIn n = .ok ()) :
    op.getNumResults! ctx.raw = 0 ∧ op.getNumRegions! ctx.raw = 0 := by
  simp only [verifyTerminatorCounts, verifyNonOperandCounts, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure] at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i h1 h2
  rw [← OperationPtr.getNumRegions!_eq_getNumRegions opIn] at h2
  rw [OperationPtr.getNumResults!_eq_getNumResults opIn]
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- A verified `g_br` or `g_brcond` has no results and no regions. -/
theorem OperationPtr.Verified.gmir_branch {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}
    (opVerify : op.Verified ctx opIn)
    (hBranch : op.getOpType! ctx.raw = .gmir .g_br ∨ op.getOpType! ctx.raw = .gmir .g_brcond) :
    op.getNumResults! ctx.raw = 0 ∧ op.getNumRegions! ctx.raw = 0 := by
  rw [Verified, OperationPtr.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType opIn] at opVerify
  rcases hBranch with hB | hB <;> rw [hB] at opVerify <;>
    simp only [OpCode.verifyLocalInvariants, HasOpInfo.verifyLocalInvariants] at opVerify <;>
    unfold GMIR.verifyLocalInvariants at opVerify <;>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at opVerify <;>
    obtain ⟨_, -, opVerify⟩ := Except.bind_eq_ok.mp opVerify <;>
    obtain ⟨_, -, opVerify⟩ := Except.bind_eq_ok.mp opVerify
  · simp only [OperationPtr.verifyUnconditionalBranch] at opVerify
    obtain ⟨v, hT, -⟩ := Except.bind_eq_ok.mp opVerify
    cases v; exact OperationPtr.verifyTerminatorCounts_ok hT
  · obtain ⟨v, hT, -⟩ := Except.bind_eq_ok.mp opVerify
    cases v; exact OperationPtr.verifyTerminatorCounts_ok hT

end Veir
