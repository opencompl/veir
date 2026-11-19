module

public import Veir.Passes.Legalization.Validity.PhiBranchContext
public import Veir.Passes.Legalization.Validity.PhiCFGFrame
public import Veir.Passes.Legalization.Validity.PhiVerifiedRequests
import all Veir.Passes.Legalization.Validity.PhiBranchContext
import all Veir.Passes.Legalization.Validity.PhiSegments
import all Veir.Passes.Legalization.Validity.PhiEdges
import all Veir.Passes.Legalization.Validity.PhiFrame
import all Veir.Passes.Legalization.Validity.PhiExtSimulation
import all Veir.Passes.Legalization.Validity.PhiWidening
import all Veir.IR.OpInfo
import all Veir.IR.Basic
import all Veir.IR.InBounds
import all Veir.Interfaces.ControlFlowInterfaces
import all Veir.GlobalOpInfo

public section
namespace Veir.Legalization.CTreeProofs.PhiWidening
variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
    (W : PhiWidening src dst block args)
include W

private theorem operandSize {op : OperationPtr} (hi : op.InBounds src.raw) :
    (op.getOperands! dst.raw).size = (op.getOperands! src.raw).size := by
  have same := W.truncations.ops op hi
  rw [OperationPtr.getOperands!.size_eq_getNumOperands!, W.extensions.numOperands same.inBounds,
    ← OperationPtr.getOperands!.size_eq_getNumOperands!, same.operands, Array.size_map]

omit W in
private theorem getSegment_eq_lookup (ctx : WfIRContext OpCode) (op : OperationPtr) (edge : Nat) :
    BranchOpInterface.getSuccessorOperands? op edge ctx.raw =
      phiBranchLookup (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getOperands! ctx.raw) edge := by
  unfold BranchOpInterface.getSuccessorOperands? phiBranchLookup
  dsimp only
  have eq : HasOpInfo.branchOpInterface? (op.getOpType! ctx.raw) =
    OpCode.branchOpInterface? (op.getOpType! ctx.raw) := rfl
  rw [eq]
  cases (op.getOpType! ctx.raw).branchOpInterface? <;> rfl

/-- Recover the same segment in the source from a destination interface lookup. -/
private theorem oldSegment {op : OperationPtr} (hi : op.InBounds src.raw) {edge s}
    (read : BranchOpInterface.getSuccessorOperands? op edge dst.raw = some s) :
    ∃ old, BranchOpInterface.getSuccessorOperands? op edge src.raw = some old ∧
      old.beginOperandIndex = s.beginOperandIndex ∧ old.forwardedOperands.size = s.forwardedOperands.size := by
  have header := W.opHeader hi
  rw [getSegment_eq_lookup] at read
  simp only [getSegment_eq_lookup]
  rw [header.code, header.properties] at read
  obtain ⟨old, found, offset, len, _⟩ := phiBranchLookup_transport _ _ (W.operandSize hi) read
  exact ⟨old, found, offset, len⟩

private theorem transportForwarding (forward : PhiForwarding src) : PhiForwarding dst := by
  constructor
  · intro op hi branch
    have old := W.originalBranch hi branch
    have header := W.opHeader old
    rw [header.code] at branch
    obtain ⟨dyn, lifted, mono⟩ := forward.semantics _ old branch
    rw [header.code, header.properties, header.successors]
    exact ⟨dyn.changeOperands (W.operandSize old).symm, lifted, mono⟩
  · intro op hi e s read
    have old := W.originalBranch hi (branchInterface_of_segment read)
    obtain ⟨_, found, _⟩ := W.oldSegment old read
    rw [(W.opHeader old).successors]
    exact forward.edgeIn op old found

private theorem transportedSlotType (facts : PhiSegmentFacts src)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (distinct : (args.map Prod.fst).Nodup)
    {op : OperationPtr} (opIn : op.InBounds src.raw) {edge old i : _} {t : IntegerType}
    (read : BranchOpInterface.getSuccessorOperands? op edge src.raw = some old)
    (destRead : (op.getSuccessors! src.raw)[edge]? = some (op.getSuccessor! src.raw edge))
    (destIn : (op.getSuccessor! src.raw edge).InBounds src.raw)
    (argIn : i < (op.getSuccessor! src.raw edge).getNumArguments! src.raw)
    (typeEq : ((op.getSuccessor! src.raw edge).getArgument i).getType! dst.raw = (t : TypeAttr)) :
    (op.getOperand! dst.raw (old.getOperandIndex i)).getType! dst.raw = (t : TypeAttr) := by
  let dest := op.getSuccessor! src.raw edge
  let slot : OpOperandPtr := ⟨op, old.getOperandIndex i⟩
  have cert := (facts op opIn).segment read
  have valid : i < old.forwardedOperands.size := cert.count ▸ argIn
  have placement := W.placement facts run opIn (fixed := 0) (by intros; omega)
  rcases placement.slots edge old dest destRead read i valid with ⟨u, hu, eq, _⟩ | ⟨untouched, notSelected⟩
  · obtain ⟨target, _, selected⟩ := W.originAtSlot facts run opIn read valid hu eq
    obtain ⟨_, extIn, _, extTypes, _, rewritten⟩ := W.extensions.extension
      (fun u hu => W.slotInTruncated (W.slotsInBounds facts run u hu)) (W.uniqueSlots facts run distinct) u hu
    obtain ⟨argOld, wide, _⟩ := W.truncations.args i u.width (List.mem_reverse.mpr selected)
    rw [eq] at rewritten
    change op.getOperand! dst.raw (old.getOperandIndex i) = _ at rewritten
    rw [rewritten, ValuePtr.getType!_opResult, ← OperationPtr.getResultTypes!.getElem!_eq (by
      have := congrArg Array.size extTypes; grind), extTypes]
    rw [target] at typeEq
    have finalType := W.extensions.valueTypes (.blockArgument (block.getArgument i))
      (W.truncations.bounds _ (by simpa [BlockPtr.getArgument_def] using argOld))
    exact (wide.symm.trans finalType.symm).trans typeEq
  · have argOld := dest.getArgument_inBounds destIn i (by
      simpa [dest, ← BlockPtr.getNumArguments!_eq_getNumArguments destIn] using argIn)
    have argOld' : (ValuePtr.blockArgument (dest.getArgument i)).InBounds src.raw := by simpa using argOld
    have preserved := (W.extensions.valueTypes _ (W.truncations.bounds _ argOld')).trans
      (W.truncations.otherTypes _ argOld' (fun a mem eq => notSelected (ValuePtr.blockArgument.inj eq ▸ mem)))
    have tin := cert.integerType argIn (preserved.symm.trans typeEq)
    have slotIn : slot.InBounds src.raw := by
      refine OpOperandPtr.inBounds_def.mpr ⟨opIn, ?_⟩
      change old.beginOperandIndex + i < op.getNumOperands src.raw opIn
      rw [← OperationPtr.getNumOperands!_eq_getNumOperands opIn]
      have lim := cert.limit
      omega
    have keeps := W.extensions.untouchedOperand (W.slotInTruncated slotIn)
      (fun u hu => Ne.symm (untouched u hu))
    change (slot.op.getOperand! dst.raw slot.index).getType! dst.raw = _
    rw [keeps, W.slotValueTruncated slotIn, W.mappedType (slotValueIn slotIn)]
    exact tin

private theorem transportSegments (facts : PhiSegmentFacts src) (forward : PhiForwarding src)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (distinct : (args.map Prod.fst).Nodup) : PhiSegmentFacts dst := by
  intro op newIn
  constructor
  · intro edge s read
    have hi := W.originalBranch newIn (branchInterface_of_segment read)
    obtain ⟨old, found, offset, length⟩ := W.oldSegment hi read
    have header := W.opHeader hi
    have edgeIn := forward.edgeIn op hi found
    have destRead : (op.getSuccessors! src.raw)[edge]? = some (op.getSuccessor! src.raw edge) :=
      Array.getElem?_eq_some_iff.mpr ⟨edgeIn, OperationPtr.getSuccessors!.getElem_eq_getSuccessor!⟩
    have destIn := OperationPtr.getSuccessors!_inBounds hi (Array.mem_of_getElem? destRead)
    have sameEdge : op.getSuccessor! dst.raw edge = op.getSuccessor! src.raw edge := by
      have newRead : (op.getSuccessors! dst.raw)[edge]? = some (op.getSuccessor! src.raw edge) :=
        header.successors ▸ destRead
      obtain ⟨bound, eq⟩ := Array.getElem?_eq_some_iff.mp newRead
      simpa only [OperationPtr.getSuccessors!.getElem_eq_getSuccessor!] using eq
    have cert := (facts op hi).segment found
    have counts := W.ctxSame.numArguments destIn
    have opCount := W.operandSize hi
    simp only [OperationPtr.getOperands!.size_eq_getNumOperands!] at opCount
    rw [sameEdge]
    refine ⟨length ▸ counts ▸ cert.count, ?_, ?_⟩
    · rw [← offset, counts, opCount]
      exact cert.limit
    · intro i t bound typeEq
      simpa only [SuccessorOperands.getOperandIndex, offset] using
        W.transportedSlotType facts run distinct hi found destRead destIn (counts ▸ bound) typeEq
  · intro edge s read
    have hi := W.originalBranch newIn (branchInterface_of_segment read)
    obtain ⟨old, found, offset, _⟩ := W.oldSegment hi read
    rw [(W.opHeader hi).code, ← offset]
    exact (facts op hi).fixedLe found
  · intro i j a b s t order si sj bound
    have hi := W.originalBranch newIn (branchInterface_of_segment si)
    obtain ⟨oldS, hs, os, ls⟩ := W.oldSegment hi si
    obtain ⟨oldT, ht, ot, _⟩ := W.oldSegment hi sj
    simpa only [SuccessorOperands.getOperandIndex, os, ot] using
      (facts op hi).disjoint (b := b) order hs ht (ls ▸ bound)

/-- Widening preserves the branch facts used to widen subsequent phi blocks. -/
theorem transportBranchFacts (facts : PhiSegmentFacts src) (forward : PhiForwarding src)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (distinct : (args.map Prod.fst).Nodup) : PhiSegmentFacts dst ∧ PhiForwarding dst :=
  ⟨W.transportSegments facts forward run distinct, W.transportForwarding forward⟩

end Veir.Legalization.CTreeProofs.PhiWidening
