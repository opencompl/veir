module

public import Veir.Passes.Legalization.Validity.PhiBranchDispatch
import all Veir.Passes.Legalization.Validity.PhiBranchDispatch
import all Veir.Passes.Legalization.Validity.PhiSegmentDispatch
import all Veir.Passes.Legalization.Validity.PhiSegments
import all Veir.Passes.Legalization.Validity.PhiBranches
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
import all Veir.Verifier.Basic

public section
namespace Veir.Legalization.CTreeProofs

/-- Reading a segment from the branch metadata and an arbitrary array of SSA operands. -/
def phiBranchLookup (code : OpCode) (props : propertiesOf code) (values : Array ValuePtr) (e : Nat) :=
  (OpCode.branchOpInterface? code).bind fun iface => iface.getSuccessorOperandsImpl? props values e

private def StableLookup (lookup : Array ValuePtr → Nat → Option SuccessorOperands) : Prop :=
  ∀ {xs ys : Array ValuePtr} {e s}, xs.size = ys.size → lookup xs e = some s →
    ∃ t, lookup ys e = some t ∧ t.beginOperandIndex = s.beginOperandIndex ∧
      t.forwardedOperands.size = s.forwardedOperands.size ∧
      ∀ last, s.forwardedOperands = xs.extract s.beginOperandIndex last →
        t.forwardedOperands = ys.extract s.beginOperandIndex last

private theorem sameSlice {xs ys : Array ValuePtr} {a b c : Nat}
    (len : xs.size = ys.size) (eq : xs.extract a b = xs.extract a c) :
    ys.extract a b = ys.extract a c := by
  have size := congrArg Array.size eq
  apply Array.ext
  · simpa only [Array.size_extract, ← len] using size
  · intro i hi hj
    simp only [Array.getElem_extract]

private theorem stableNone : StableLookup (fun _ _ => none) := by
  intro xs ys e s len h
  contradiction

private theorem stableWhole : StableLookup (fun xs e => wholeSegment xs e) := by
  intro xs ys e s len h
  by_cases eq : e = 0
  · subst e; cases h
    refine ⟨_, rfl, rfl, len.symm, fun last old => ?_⟩
    change ys = ys.extract 0 last
    change xs = xs.extract 0 last at old
    simpa only [len, Array.extract_size] using
      (sameSlice (ys := ys) (a := 0) (c := last) (b := xs.size) len (by simpa only [Array.extract_size] using old))
  · simp [wholeSegment, guard, eq] at h
    cases h

private theorem stableSegments (fixed : Nat) (counts : Array Int) :
    StableLookup (BranchOpInterface.getSegmentedSuccessorOperands? fixed counts) := by
  intro xs ys e s len h
  unfold BranchOpInterface.getSegmentedSuccessorOperands? at h ⊢
  simp only [bind, Option.bind] at h ⊢
  split at h <;> try contradiction
  rename_i n hn
  simp only [hn]
  cases h
  exact ⟨_, rfl, rfl, by simp only [Array.size_extract, len], fun _ => sameSlice len⟩

private theorem stableSwitch (props : LLVMSwitchProperties) :
    StableLookup (Llvm.getSwitchSuccessorOperands? props) := by
  unfold Llvm.getSwitchSuccessorOperands?
  cases eq : props.operandSegmentSizes.values[1]? with
  | none => exact @stableNone
  | some n => exact @stableSegments _ _

set_option maxHeartbeats 1500000 in
/-- A branch interface selects its offset and length independently of the operand identities. -/
theorem phiBranchLookup_transport (code : OpCode) (props : propertiesOf code)
    {xs ys : Array ValuePtr} {e s} (len : xs.size = ys.size)
    (read : phiBranchLookup code props xs e = some s) :
    ∃ t, phiBranchLookup code props ys e = some t ∧ t.beginOperandIndex = s.beginOperandIndex ∧
      t.forwardedOperands.size = s.forwardedOperands.size ∧
      ∀ last, s.forwardedOperands = xs.extract s.beginOperandIndex last →
        t.forwardedOperands = ys.extract s.beginOperandIndex last := by
  suffices StableLookup (phiBranchLookup code props) from this len read
  clear read len xs ys e s
  cases code <;> first | exact @stableNone | skip
  all_goals rename_i code; cases code <;> first | exact @stableNone | exact @stableWhole | exact @stableSegments _ _ | exact @stableSwitch _

private theorem wholeEdge {xs : Array ValuePtr} {e s} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {opIn : op.InBounds ctx.raw} (valid : op.verifyUnconditionalBranch ctx opIn = .ok ())
    (read : wholeSegment xs e = some s) : e < (op.getSuccessors! ctx.raw).size := by
  rw [terminatorSuccessors (bind_ok_left valid)]
  by_cases eq : e = 0
  · omega
  · simp [wholeSegment, guard, eq] at read; cases read

private theorem conditionalEdge {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} {fixed : Nat} {sizes : DenseArrayAttr}
    (arity : fixed = 1 ∨ fixed = 2) (valid : op.verifyTerminatorCounts ctx opIn 2 = .ok () ∧
      op.verifyCondBranchOperandSegmentSizes ctx opIn sizes fixed = .ok ())
    {xs : Array ValuePtr} {e s} (read : BranchOpInterface.getSegmentedSuccessorOperands?
      fixed sizes.values xs e = some s) : e < (op.getSuccessors! ctx.raw).size := by
  obtain ⟨n, h, _⟩ := segmentedSuccessorOperands_spec read
  have bound := (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨_, _, shape, _⟩ := conditionalSegmentCounts arity valid.2
  simp only [shape, Array.size_append, Array.size_replicate, List.size_toArray,
    List.length_cons, List.length_nil] at bound
  rw [terminatorSuccessors valid.1]
  omega

private theorem switchEdge {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} (valid : Llvm.verifyLocalInvariants Llvm.switch op ctx opIn = .ok ())
    {e s} (read : Llvm.getSwitchSuccessorOperands? (op.getProperties! ctx.raw Llvm.switch)
      (op.getOperands! ctx.raw) e = some s) : e < (op.getSuccessors! ctx.raw).size := by
  unfold Llvm.verifyLocalInvariants at valid
  replace valid := Except.ok_of_bind_ok valid
  dsimp only at valid
  rw [terminatorSuccessors (bind_ok_left valid)]
  unfold Llvm.getSwitchSuccessorOperands? at read
  simp only [bind, Option.bind] at read
  split at read <;> try contradiction
  obtain ⟨n, h, _⟩ := segmentedSuccessorOperands_spec read
  have bound := (Array.getElem?_eq_some_iff.mp h).1
  simp at bound
  omega

set_option maxHeartbeats 2000000 in
private theorem verifiedEdge {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} (valid : op.Verified ctx opIn)
    {e s} (read : BranchOpInterface.getSuccessorOperands? op e ctx.raw = some s) :
    e < (op.getSuccessors! ctx.raw).size := by
  have facts := verifiedPhiBranchFacts valid
  unfold BranchOpInterface.getSuccessorOperands? at read
  generalize hcode : op.getOpType! ctx.raw = code at facts read
  cases code <;> first | (change none = some _ at read; cases read) | skip
  all_goals rename_i code; cases code <;> first | (change none = some _ at read; cases read) | skip
  all_goals first | exact wholeEdge facts read | exact conditionalEdge (.inl rfl) facts read |
    exact conditionalEdge (.inr rfl) facts read | exact switchEdge facts read

/-- The verified branch behavior and the domain of its successor interface. -/
structure PhiForwarding (ctx : WfIRContext OpCode) : Prop where
  semantics : ∀ (op : OperationPtr), op.InBounds ctx.raw → (op.getOpType! ctx.raw).branchOpInterface?.isSome →
    ForwardsBranchSegment (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
      (op.getSuccessors! ctx.raw) (phiBranchFixedOperands (op.getOpType! ctx.raw)) (op.getOperands! ctx.raw) ∧
      (op.getOpType! ctx.raw).isLifted ∧ InterpretOp'Monotone (op.getOpType! ctx.raw)
  edgeIn : ∀ (op : OperationPtr), op.InBounds ctx.raw → ∀ {e s},
    BranchOpInterface.getSuccessorOperands? op e ctx.raw = some s → e < (op.getSuccessors! ctx.raw).size

theorem PhiForwarding.of_verified {ctx : WfIRContext OpCode} {root : OperationPtr}
    (verified : ctx.Verified root) : PhiForwarding ctx :=
  ⟨fun _ hi => verifiedPhiBranchSemantics (OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants verified hi),
   fun _ hi => verifiedEdge (OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants verified hi)⟩

/-- Substituting SSA operand pointers preserves every successful branch and its chosen slice. -/
theorem ForwardsBranchSegment.changeOperands {code : OpCode} {props : propertiesOf code}
    {succs : Array BlockPtr} {fixed : Nat} {xs ys : Array ValuePtr} (len : xs.size = ys.size)
    (forward : ForwardsBranchSegment code props succs fixed xs) :
    ForwardsBranchSegment code props succs fixed ys := by
  intro values size mem types results mem' action run
  obtain ⟨e, first, last, dest, found, read, rest⟩ := forward values (len.trans size) mem types results mem' action run
  obtain ⟨⟨arr, start⟩, newRead, offset, _, range⟩ := phiBranchLookup_transport code props len read
  change start = first at offset
  subst start
  have slice : arr = ys.extract first last := range last rfl
  subst arr
  exact ⟨e, first, last, dest, found, newRead, rest⟩

end Veir.Legalization.CTreeProofs
