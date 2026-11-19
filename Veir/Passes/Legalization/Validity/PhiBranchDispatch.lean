module

public import Veir.Passes.Legalization.Validity.PhiBranches
public import Veir.Passes.Legalization.Validity.PhiSegmentDispatch
public import Veir.Interpreter.CTreeRefinement.Lifted
public import Veir.Interpreter.Lemmas
import Veir.Dialects.Cf.Monotonicity
import Veir.Dialects.GMIR.Monotonicity
import Veir.Dialects.LLVM.Monotonicity
import Veir.Dialects.RISCV_Cf.Monotonicity
import all Veir.Dialects.Cir.OpInfo
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Interpreter.Basic
import all Veir.GlobalOpInfo
import all Veir.Passes.Legalization.Validity.PhiBranches
import all Veir.Passes.Legalization.Validity.PhiSegmentDispatch
import all Veir.Passes.Legalization.Validity.PhiSegments
import all Veir.Verifier.Basic
import all Veir.IR.Basic
import all Veir.IR.OpCode
import all Veir.Interfaces.ControlFlowInterfaces

public section

namespace Veir.Legalization.CTreeProofs

private theorem terminatorSuccessors {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} {n : Nat} (ok : op.verifyTerminatorCounts ctx opIn n = .ok ()) :
    (op.getSuccessors! ctx.raw).size = n := by
  simp only [OperationPtr.verifyTerminatorCounts, OperationPtr.verifyNonOperandCounts,
    bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok <;> try contradiction
  rw [OperationPtr.getSuccessors!.size_eq_getNumSuccessors!, OperationPtr.getNumSuccessors!_eq_getNumSuccessors opIn]
  grind

private theorem conditionalSuccessors {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} (ok : op.verifyTerminatorCounts ctx opIn 2 = .ok ()) :
    ∃ yes no, op.getSuccessors! ctx.raw = #[yes, no] := by
  have h := terminatorSuccessors ok
  let xs := op.getSuccessors! ctx.raw
  change xs.size = 2 at h
  refine ⟨xs[0]'(by omega), xs[1]'(by omega), ?_⟩
  change xs = _
  ext i valid left
  · simpa using h
  · have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> rfl

private theorem verifiedUnconditional {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} {code : OpCode}
    (kind : code = .cf .br ∨ code = .llvm .br ∨ code = .gmir .g_br ∨ code = .riscv_cf .branch)
    (ok : op.verifyUnconditionalBranch ctx opIn = .ok ())
    (props : propertiesOf code) :
    ForwardsBranchSegment code props (op.getSuccessors! ctx.raw) 0 (op.getOperands! ctx.raw) := by
  obtain ⟨d, eq⟩ := Array.size_eq_one_iff.mp (terminatorSuccessors (bind_ok_left ok))
  rw [eq]
  exact forwards_unconditional kind props d _

set_option maxHeartbeats 1600000 in
/-- Branch opcodes lift an operand-monotone interpreter. -/
theorem branchLiftAndMonotone (code : OpCode) (active : code.branchOpInterface?.isSome) :
    code.isLifted ∧ InterpretOp'Monotone code := by
  cases code <;> first | (change false = true at active; cases active) | skip
  all_goals rename_i code
  all_goals cases code <;> first | (change false = true at active; cases active) | skip
  all_goals refine ⟨rfl, ?_⟩
  all_goals first
    | exact cf_monotone _
    | exact riscv_cf_monotone _
    | exact llvm_monotone_br
    | exact llvm_monotone_cond_br
    | exact llvm_monotone_switch
    | exact gmir_monotone_g_br
    | exact gmir_monotone_g_brcond
    | constructor; intros; trivial

/-- Looking up a forwarded segment identifies an operation with the branch interface. -/
theorem branchInterface_of_segment {ctx : WfIRContext OpCode} {op : OperationPtr} {edge seg}
    (found : BranchOpInterface.getSuccessorOperands? op edge ctx.raw = some seg) :
    (op.getOpType! ctx.raw).branchOpInterface?.isSome := by
  unfold BranchOpInterface.getSuccessorOperands? at found
  dsimp only at found
  have eq : HasOpInfo.branchOpInterface? (op.getOpType! ctx.raw) =
    OpCode.branchOpInterface? (op.getOpType! ctx.raw) := rfl
  rw [eq] at found
  cases h : (op.getOpType! ctx.raw).branchOpInterface? <;> simp_all

set_option maxHeartbeats 1800000 in
/-- A verified branch reads precisely the forwarded arguments of its chosen successor.
Its lifted interpreter is monotone when the input state is refined. -/
theorem verifiedPhiBranchSemantics {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} (valid : op.Verified ctx opIn)
    (active : (op.getOpType! ctx.raw).branchOpInterface?.isSome) :
    ForwardsBranchSegment (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getSuccessors! ctx.raw) (phiBranchFixedOperands (op.getOpType! ctx.raw)) (op.getOperands! ctx.raw) ∧
      (op.getOpType! ctx.raw).isLifted ∧ InterpretOp'Monotone (op.getOpType! ctx.raw) := by
  refine ⟨?_, branchLiftAndMonotone _ active⟩
  have facts := verifiedPhiBranchFacts valid
  generalize hcode : op.getOpType! ctx.raw = code at facts active ⊢
  cases code <;> first | (change false = true at active; cases active) | skip
  all_goals rename_i code
  all_goals cases code <;> first | (change false = true at active; cases active) | skip
  case llvm.switch =>
    change Llvm.verifyLocalInvariants Llvm.switch op ctx opIn = .ok () at facts
    unfold Llvm.verifyLocalInvariants at facts
    replace facts := Except.ok_of_bind_ok facts
    dsimp only at facts
    exact forwards_llvm_switch _ _ (terminatorSuccessors (bind_ok_left facts)) _
  all_goals first
    | exact forwards_cir (.inl rfl) _ _ _ _
    | exact forwards_cir (.inr rfl) _ _ _ _
    | exact verifiedUnconditional (.inl rfl) facts _
    | exact verifiedUnconditional (.inr (.inl rfl)) facts _
    | exact verifiedUnconditional (.inr (.inr (.inl rfl))) facts _
    | exact verifiedUnconditional (.inr (.inr (.inr rfl))) facts _
    | skip
  all_goals
    obtain ⟨counts, segments⟩ := facts
    obtain ⟨yes, no, eq⟩ := conditionalSuccessors counts
    rw [eq]
    first
      | obtain ⟨yesCount, noCount, shape, size⟩ := conditionalSegmentCounts (.inl rfl) segments
      | obtain ⟨yesCount, noCount, shape, size⟩ := conditionalSegmentCounts (.inr rfl) segments
    first
      | exact forwards_gmir_brcond _ shape yes no _ size
      | exact forwards_i1_brcond (.inl rfl) _ _ _ shape yes no _ size
      | exact forwards_i1_brcond (.inr rfl) _ _ _ shape yes no _ size
      | exact forwards_riscv_conditional _ _ yes no _ size (congrArg (fun a => some (_, a)) shape)

end Veir.Legalization.CTreeProofs
