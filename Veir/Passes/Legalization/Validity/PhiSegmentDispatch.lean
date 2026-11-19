module

public import Veir.Passes.Legalization.Validity.PhiSegments
import all Veir.Passes.Legalization.Validity.PhiSegments
import all Veir.GlobalOpInfo
import all Veir.IR.Basic
import all Veir.IR.OpInfo
import all Veir.IR.OpCode
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.Cir.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Interfaces.ControlFlowInterfaces
import all Veir.Verifier

public section
namespace Veir.Legalization.CTreeProofs

/-- The verified operand segments of a branch are complete and pairwise disjoint. -/
structure VerifiedPhiSegments (ctx : WfIRContext OpCode) (branch : OperationPtr)
    (lookup : Nat → Option SuccessorOperands) : Prop where
  segment : ∀ {edge s}, lookup edge = some s →
    VerifiedPhiSegment ctx branch (branch.getSuccessor! ctx.raw edge) s
  fixedLe : ∀ {edge s}, lookup edge = some s →
    phiBranchFixedOperands (branch.getOpType! ctx.raw) ≤ s.beginOperandIndex
  disjoint : ∀ {i j a b s t}, i < j → lookup i = some s → lookup j = some t →
    a < s.forwardedOperands.size → s.getOperandIndex a < t.getOperandIndex b

/-- The operand segments needed by phi widening for the branches of a context. -/
abbrev PhiSegmentFacts (ctx : WfIRContext OpCode) : Prop :=
  ∀ (op : OperationPtr), op.InBounds ctx.raw → VerifiedPhiSegments ctx op
    (fun edge => BranchOpInterface.getSuccessorOperands? op edge ctx.raw)

private def wholeSegment (operands : Array ValuePtr) (edge : Nat) : Option SuccessorOperands := do
  guard (edge = 0)
  some {forwardedOperands := operands}

private theorem VerifiedPhiSegments.none {ctx : WfIRContext OpCode} {branch : OperationPtr} :
    VerifiedPhiSegments ctx branch (fun _ => none) := by
  constructor <;> intros <;> contradiction

private theorem VerifiedPhiSegments.whole {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} (fixed : phiBranchFixedOperands (branch.getOpType! ctx.raw) = 0)
    (checked : branch.verifyUnconditionalBranch ctx bp = .ok ()) :
    VerifiedPhiSegments ctx branch (wholeSegment (branch.getOperands! ctx.raw)) := by
  refine ⟨fun {i s} hi => ?_, fun _ => by rw [fixed]; omega, fun {i j _ _ s t} order hi hj _ => ?_⟩
  · by_cases e : i = 0
    · subst i; cases hi; exact VerifiedPhiSegment.unconditional checked
    · simp [wholeSegment, guard, e] at hi
      cases hi
  · have : j ≠ 0 := by omega
    simp [wholeSegment, guard, this] at hj
    cases hj

private theorem VerifiedPhiSegments.segmented {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {fixed : Nat} {sizes : Array Int}
    (fixedEq : phiBranchFixedOperands (branch.getOpType! ctx.raw) = fixed)
    (cert : ∀ {edge s}, BranchOpInterface.getSegmentedSuccessorOperands? fixed sizes
      (branch.getOperands! ctx.raw) edge = some s →
      VerifiedPhiSegment ctx branch (branch.getSuccessor! ctx.raw edge) s) :
    VerifiedPhiSegments ctx branch
      (BranchOpInterface.getSegmentedSuccessorOperands? fixed sizes (branch.getOperands! ctx.raw)) :=
  ⟨cert, fun h => by
    obtain ⟨_, _, start, _⟩ := segmentedSuccessorOperands_spec h
    rw [fixedEq, start, successorSegmentStart]
    omega, fun order hs ht hi => segmentedSuccessorOperands_disjoint order hs ht hi⟩

private theorem VerifiedPhiSegments.conditional {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} {fixed : Nat} {sizes : DenseArrayAttr}
    (fixedEq : phiBranchFixedOperands (branch.getOpType! ctx.raw) = fixed)
    (arity : fixed = 1 ∨ fixed = 2)
    (valid : branch.verifyCondBranchOperandSegmentSizes ctx bp sizes fixed = .ok ()) :
    VerifiedPhiSegments ctx branch
      (BranchOpInterface.getSegmentedSuccessorOperands? fixed sizes.values (branch.getOperands! ctx.raw)) :=
  .segmented fixedEq (fun r => VerifiedPhiSegment.conditional arity valid r)

private theorem VerifiedPhiSegments.switch {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} (fixedEq : phiBranchFixedOperands (branch.getOpType! ctx.raw) = 1)
    (valid : Llvm.verifyLocalInvariants Llvm.switch branch ctx bp = .ok ()) :
    VerifiedPhiSegments ctx branch (Llvm.getSwitchSuccessorOperands?
      (branch.getProperties! ctx.raw Llvm.switch) (branch.getOperands! ctx.raw)) := by
  unfold Llvm.getSwitchSuccessorOperands?
  cases eq : (branch.getProperties! ctx.raw Llvm.switch).operandSegmentSizes.values[1]? with
  | none => exact VerifiedPhiSegments.none
  | some count => exact .segmented fixedEq (fun h => VerifiedPhiSegment.llvmSwitch valid eq h)

/-- The part of each supported branch verifier that checks the successor layout. -/
def PhiBranchFacts (ctx : WfIRContext OpCode) (branch : OperationPtr) (bp : branch.InBounds ctx.raw)
    (code : OpCode) : Prop :=
  let conditional (n : Nat) (sizes : DenseArrayAttr) :=
    branch.verifyTerminatorCounts ctx bp 2 = .ok () ∧
    branch.verifyCondBranchOperandSegmentSizes ctx bp sizes n = .ok ()
  match code with
  | .llvm .br | .cf .br | .cir .br | .gmir .g_br | .riscv_cf .branch =>
    branch.verifyUnconditionalBranch ctx bp = .ok ()
  | .llvm .switch => Llvm.verifyLocalInvariants Llvm.switch branch ctx bp = .ok ()
  | .llvm .cond_br => conditional 1 (branch.getProperties! ctx.raw (OpCode.llvm .cond_br)).operandSegmentSizes
  | .cir .brcond => conditional 1 (branch.getProperties! ctx.raw (OpCode.cir .brcond)).operandSegmentSizes
  | .cf .cond_br => conditional 1 (branch.getProperties! ctx.raw (OpCode.cf .cond_br)).operandSegmentSizes
  | .gmir .g_brcond => conditional 1 (branch.getProperties! ctx.raw (OpCode.gmir .g_brcond)).operandSegmentSizes
  | .riscv_cf .beqz => conditional 1 (branch.getProperties! ctx.raw (OpCode.riscv_cf .beqz)).operandSegmentSizes
  | .riscv_cf .bnez => conditional 1 (branch.getProperties! ctx.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes
  | .riscv_cf .beq => conditional 2 (branch.getProperties! ctx.raw (OpCode.riscv_cf .beq)).operandSegmentSizes
  | .riscv_cf .bne => conditional 2 (branch.getProperties! ctx.raw (OpCode.riscv_cf .bne)).operandSegmentSizes
  | .riscv_cf .blt => conditional 2 (branch.getProperties! ctx.raw (OpCode.riscv_cf .blt)).operandSegmentSizes
  | .riscv_cf .bge => conditional 2 (branch.getProperties! ctx.raw (OpCode.riscv_cf .bge)).operandSegmentSizes
  | .riscv_cf .bltu => conditional 2 (branch.getProperties! ctx.raw (OpCode.riscv_cf .bltu)).operandSegmentSizes
  | .riscv_cf .bgeu => conditional 2 (branch.getProperties! ctx.raw (OpCode.riscv_cf .bgeu)).operandSegmentSizes
  | _ => True

set_option maxHeartbeats 800000 in
theorem verifiedPhiBranchFacts {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} (valid : branch.Verified ctx bp) :
    PhiBranchFacts ctx branch bp (branch.getOpType! ctx.raw) := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants, HasOpInfo.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType] at valid
  generalize eq : branch.getOpType! ctx.raw = code at valid ⊢
  cases code <;> first | exact True.intro | skip
  all_goals rename_i code; cases code <;> first | exact True.intro | skip
  all_goals simp only [OpCode.verifyLocalInvariants] at valid
  case llvm.switch => exact valid
  all_goals try unfold GMIR.verifyLocalInvariants at valid
  all_goals try simp only [Cf.verifyLocalInvariants, Cir.verifyLocalInvariants, OperationPtr.verifyCirBrCondOp,
    Riscv_Cf.verifyLocalInvariants, Llvm.verifyLocalInvariants] at valid
  all_goals try dsimp only at valid
  all_goals simp only [PhiBranchFacts]
  case llvm.br => exact Except.ok_of_bind_ok valid
  case riscv_cf.branch => exact bind_ok_left valid
  case cf.br => exact valid
  case cir.br => exact valid
  case cf.cond_br =>
    refine ⟨bind_ok_left valid, ?_⟩
    replace valid := Except.ok_of_bind_ok valid
    split at valid <;> first | contradiction | exact valid
  case llvm.cond_br =>
    replace valid := Except.ok_of_bind_ok valid
    refine ⟨bind_ok_left valid, ?_⟩
    replace valid := Except.ok_of_bind_ok valid
    split at valid <;> try contradiction
    split at valid <;> try contradiction
    split at valid <;> first | contradiction | exact valid
  case gmir.g_br =>
    split at valid <;> try contradiction
    exact Except.ok_of_bind_ok (Except.ok_of_bind_ok valid)
  case gmir.g_brcond =>
    split at valid <;> try contradiction
    replace valid := Except.ok_of_bind_ok (Except.ok_of_bind_ok valid)
    refine ⟨bind_ok_left valid, ?_⟩
    replace valid := Except.ok_of_bind_ok valid
    split at valid <;> try contradiction
    exact Except.ok_of_bind_ok valid
  all_goals exact ⟨bind_ok_left valid, bind_ok_left (Except.ok_of_bind_ok valid)⟩

set_option maxHeartbeats 2000000 in
/-- The branch operand interface of every locally verified operation has checked types and
in-bounds, nonoverlapping segments. An operation without the interface has no segments. -/
theorem verifiedPhiSegments {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} (valid : branch.Verified ctx bp) :
    VerifiedPhiSegments ctx branch (fun edge =>
      BranchOpInterface.getSuccessorOperands? branch edge ctx.raw) := by
  unfold BranchOpInterface.getSuccessorOperands?
  have facts := verifiedPhiBranchFacts valid
  generalize hcode : branch.getOpType! ctx.raw = code at facts ⊢
  cases code <;>
    first | exact VerifiedPhiSegments.none | skip
  all_goals rename_i code
  all_goals cases code <;>
    first | exact VerifiedPhiSegments.none | skip
  all_goals simp only [PhiBranchFacts] at facts
  all_goals first
    | exact VerifiedPhiSegments.whole (by rw [hcode]; rfl) facts
    | exact VerifiedPhiSegments.switch (by rw [hcode]; rfl) facts
    | exact VerifiedPhiSegments.conditional (by rw [hcode]; rfl) (.inl rfl) facts.2
    | exact VerifiedPhiSegments.conditional (by rw [hcode]; rfl) (.inr rfl) facts.2

theorem PhiSegmentFacts.of_verified {ctx : WfIRContext OpCode} {root : OperationPtr}
    (verified : ctx.Verified root) : PhiSegmentFacts ctx :=
  fun _ opIn => verifiedPhiSegments (OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants
    verified opIn)

end Veir.Legalization.CTreeProofs
