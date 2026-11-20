module

public import Veir.Passes.Legalization.Validity.PhiPlacement
public import Veir.Passes.Legalization.Validity.PhiRequests
public import Veir.Passes.Legalization.Validity.PhiSegmentDispatch
public import Veir.Passes.Legalization.Validity.PhiExtSimulation
import all Veir.Passes.Legalization.Validity.PhiFrame
import all Veir.Passes.Legalization.Validity.PhiRequests
import all Veir.Passes.Legalization.Validity.PhiExtSimulation
import all Veir.IR.OpInfo
import all Veir.IR.Basic
import all Veir.IR.InBounds
import all Veir.Passes.Legalization.Validity.PhiEdges
import all Veir.Interfaces.ControlFlowInterfaces

public section
namespace Veir.Legalization.CTreeProofs
variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}

private theorem verifiedUse {uses : Array BlockOperandPtr} (chain : block.DefUse src.raw uses)
    (facts : PhiSegmentFacts src) {edge : BlockOperandPtr} (hm : edge ∈ uses) {seg : SuccessorOperands}
    (read : BranchOpInterface.getSuccessorOperands? edge.op edge.index src.raw = some seg) :
    VerifiedPhiSegment src edge.op block seg := by
  have hi := (BlockOperandPtr.inBounds_def.mp (chain.arrayInBounds hm)).1
  have dest := chain.useValue edge hm
  change edge.op.getSuccessor! src.raw edge.index = block at dest
  exact dest ▸ (facts _ hi).segment read

theorem phiRequestedSlots (facts : PhiSegmentFacts src)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (uses : Array BlockOperandPtr) (edges : List (OperationPtr × SuccessorOperands))
    (chain : block.DefUse src.raw uses) (segments : uses.toList.mapM (fun e => do
        return (e.op, ← BranchOpInterface.getSuccessorOperands? e.op e.index src.raw)) = some edges) :
    ∀ x ∈ edges.flatMap (fun e => branchOperandRequests e.1 e.2 args), x.1.InBounds src.raw := by
  intro x hx
  obtain ⟨⟨op, seg⟩, mem, ⟨i,w⟩, sel, rfl⟩ :=
    List.mem_flatMap.mp hx |>.imp fun e => And.imp_right List.mem_map.mp
  obtain ⟨edge, edgeIn, rfl, read⟩ := (describesPhiEdges segments).exists_left_of_mem_right mem
  have useIn := chain.arrayInBounds (by simpa using edgeIn)
  have opIn := (BlockOperandPtr.inBounds_def.mp useIn).1
  have within := (widenBlockArgumentsChecked_argumentType run sel).1
  have limit := (verifiedUse chain facts (by simpa using edgeIn) read).limit
  dsimp only at limit
  apply OpOperandPtr.inBounds_def.mpr
  refine ⟨opIn, ?_⟩
  change seg.beginOperandIndex + i < edge.op.getNumOperands src.raw opIn
  rw [← OperationPtr.getNumOperands!_eq_getNumOperands opIn]
  omega

/-- Two positions of a branch's forwarded operands agree only if they belong to the
same successor and have the same offset within its segment. -/
theorem phiSlot_unique {op : OperationPtr} {i j x y : Nat} {s t : SuccessorOperands}
    (cert : VerifiedPhiSegments src op (fun e => BranchOpInterface.getSuccessorOperands? op e src.raw))
    (si : BranchOpInterface.getSuccessorOperands? op i src.raw = some s)
    (sj : BranchOpInterface.getSuccessorOperands? op j src.raw = some t)
    (hx : x < s.forwardedOperands.size) (hy : y < t.forwardedOperands.size)
    (slot : s.getOperandIndex x = t.getOperandIndex y) : i = j ∧ x = y := by
  have ij : i = j := by
    by_cases lt : i < j
    · have := cert.disjoint (b := y) lt si sj hx; omega
    by_cases gt : j < i
    · have := cert.disjoint (b := x) gt sj si hy; omega
    omega
  subst j
  obtain rfl := Option.some.inj (si.symm.trans sj)
  exact ⟨rfl, Nat.add_left_cancel slot⟩

private theorem uniqueRequests (facts : PhiSegmentFacts src)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    {uses : Array BlockOperandPtr} (chain : block.DefUse src.raw uses)
    (distinct : (args.map Prod.fst).Nodup)
    {us : List BlockOperandPtr} {es : List (OperationPtr × SuccessorOperands)}
    (descriptions : PhiEdgeList src.raw us es)
    (members : ∀ e ∈ us, e ∈ uses) (noDup : us.Nodup) :
    (es.flatMap (fun e => branchOperandRequests e.1 e.2 args)).Pairwise
      (fun x y => x.1 ≠ y.1) := by
  induction descriptions with
  | nil => exact .nil
  | @cons edge e us es d tail ih =>
    obtain ⟨op, s⟩ := e
    obtain ⟨rfl, si⟩ := d
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨?_, ih (fun a ha => members a (.tail _ ha)) (List.nodup_cons.mp noDup).2, ?_⟩
    · unfold branchOperandRequests
      apply List.pairwise_map.mpr
      apply (List.pairwise_map.mp (show (args.map Prod.fst).Pairwise (· ≠ ·) from distinct)).imp
      intro a b ne same
      exact ne (Nat.add_left_cancel (congrArg OpOperandPtr.index same))
    · intro x hx y hy same
      obtain ⟨⟨i, _⟩, hi, rfl⟩ := List.mem_map.mp hx
      obtain ⟨⟨op, t⟩, et, ⟨j, _⟩, hj, rfl⟩ :=
        List.mem_flatMap.mp hy |>.imp fun e => And.imp_right List.mem_map.mp
      obtain ⟨other, hother, opEq, sj⟩ := tail.exists_left_of_mem_right et
      have owners := congrArg OpOperandPtr.op same
      change edge.op = op at owners
      change op = other.op at opEq
      have slots := congrArg OpOperandPtr.index same
      change s.getOperandIndex i = t.getOperandIndex j at slots
      have h₁ := members edge (.head _)
      have h₂ := members other (.tail _ hother)
      have v₁ := verifiedUse chain facts h₁ si
      have v₂ := verifiedUse chain facts h₂ sj
      have opIn := (BlockOperandPtr.inBounds_def.mp (chain.arrayInBounds h₁)).1
      have ver := facts _ opIn
      have ix := phiSlot_unique ver si ((owners.trans opEq).symm ▸ sj)
        (v₁.count ▸ (widenBlockArgumentsChecked_argumentType run hi).1)
        (v₂.count ▸ (widenBlockArgumentsChecked_argumentType run hj).1) slots
      have sameUse : edge = other := by cases edge; cases other; simp_all
      exact (List.nodup_cons.mp noDup).1 (sameUse ▸ hother)

namespace PhiWidening
variable (W : PhiWidening src dst block args)

theorem slotsInBounds (facts : PhiSegmentFacts src)
    (run : widenBlockArgumentsChecked block args src = .ok dst) (u) (hu : u ∈ W.updates) :
    u.operand.InBounds src.raw := by
  have req := List.mem_map_of_mem (f := fun u : BranchOperandExtension => (u.operand, u.width)) hu
  rw [W.requests] at req
  exact phiRequestedSlots facts run W.uses W.edges W.chain W.segments _ req

theorem uniqueSlots (facts : PhiSegmentFacts src) (run : widenBlockArgumentsChecked block args src = .ok dst)
    (distinct : (args.map Prod.fst).Nodup) : (W.updates.map BranchOperandExtension.operand).Nodup := by
  have req := uniqueRequests facts run W.chain distinct (describesPhiEdges W.segments)
    (fun _ h => by simpa using h) (BlockPtr.DefUse_array_toList_Nodup W.chain)
  rw [← W.requests, List.pairwise_map] at req
  exact List.pairwise_map.mpr req

/-- The use and forwarded argument that caused an extension to be inserted. -/
def UpdateOrigin (u : BranchOperandExtension) (i : Nat) : Prop :=
  ∃ edge ∈ W.uses, ∃ seg,
    BranchOpInterface.getSuccessorOperands? edge.op edge.index src.raw = some seg ∧
    (i, u.width) ∈ args ∧ u.operand = ⟨edge.op, seg.getOperandIndex i⟩

theorem exists_origin {u : BranchOperandExtension} (hu : u ∈ W.updates) :
    ∃ i, W.UpdateOrigin u i := by
  obtain ⟨e, he, seg, i, read, sel, slot⟩ := W.update_iff.mp ⟨u, hu, rfl, rfl⟩
  exact ⟨i, e, he, seg, read, sel, slot⟩

noncomputable def argumentIndex (u : BranchOperandExtension) : Nat := open Classical in
  if h : ∃ i, W.UpdateOrigin u i then h.choose else 0

theorem origin {u : BranchOperandExtension} (hu : u ∈ W.updates) :
    W.UpdateOrigin u (W.argumentIndex u) := by
  rw [argumentIndex, dite_eq_left (W.exists_origin hu)]
  exact (W.exists_origin hu).choose_spec

theorem linked (facts : PhiSegmentFacts src)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (u : BranchOperandExtension) (hu : u ∈ W.updates) :
    LinkedExtension (src := src) (block := block) (args := args) u (W.argumentIndex u) := by
  obtain ⟨e, he, seg, read, sel, slot⟩ := W.origin hu
  obtain ⟨bound, bits, ht, _⟩ := widenBlockArgumentsChecked_argumentType run sel
  refine ⟨sel, ?_⟩
  rw [slot, ht]
  exact (verifiedUse W.chain facts he read).integerType bound ht

/-- Identify the destination argument of a rewritten slot on any outgoing edge of this branch. -/
theorem originAtSlot (facts : PhiSegmentFacts src)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    {op : OperationPtr} (opIn : op.InBounds src.raw) {edge i : Nat} {seg : SuccessorOperands}
    (read : BranchOpInterface.getSuccessorOperands? op edge src.raw = some seg)
    (valid : i < seg.forwardedOperands.size)
    {u : BranchOperandExtension} (hu : u ∈ W.updates)
    (slot : u.operand = ⟨op, seg.getOperandIndex i⟩) :
    op.getSuccessor! src.raw edge = block ∧ W.argumentIndex u = i ∧ (i, u.width) ∈ args := by
  obtain ⟨e, he, s, originRead, sel, originSlot⟩ := W.origin hu
  have eq := originSlot.symm.trans slot
  have ops := congrArg OpOperandPtr.op eq
  have slots := congrArg OpOperandPtr.index eq
  change e.op = op at ops
  change s.getOperandIndex (W.argumentIndex u) = seg.getOperandIndex i at slots
  have cert := verifiedUse W.chain facts he originRead
  have edgeEq := phiSlot_unique (facts _ opIn)
    (ops ▸ originRead) read (cert.count ▸ (widenBlockArgumentsChecked_argumentType run sel).1) valid slots
  have dest := W.chain.useValue e he
  change e.op.getSuccessor! src.raw e.index = block at dest
  exact ⟨ops ▸ edgeEq.1 ▸ dest, edgeEq.2, edgeEq.2 ▸ sel⟩

theorem placement (facts : PhiSegmentFacts src) (run : widenBlockArgumentsChecked block args src = .ok dst)
    {op : OperationPtr} (opIn : op.InBounds src.raw) {fixed : Nat}
    (prefixBound : ∀ edge seg, BranchOpInterface.getSuccessorOperands? op edge src.raw = some seg →
      fixed ≤ seg.beginOperandIndex) : W.BranchSlotPlacement op fixed W.argumentIndex := by
  constructor
  · intro u hu owner
    obtain ⟨e, he, seg, read, sel, slot⟩ := W.origin hu
    have owner' : e.op = op := (congrArg OpOperandPtr.op slot).symm.trans owner
    have h := prefixBound _ _ (owner' ▸ read)
    rw [slot]
    change fixed ≤ seg.beginOperandIndex + W.argumentIndex u
    omega
  · intro edge seg dest dstRead read i valid
    obtain ⟨inRange, destEq⟩ := Array.getElem?_eq_some_iff.mp dstRead
    rw [OperationPtr.getSuccessors!.getElem_eq_getSuccessor!] at destEq
    rw [OperationPtr.getSuccessors!.size_eq_getNumSuccessors!] at inRange
    by_cases changed : ∃ u ∈ W.updates, u.operand = ⟨op, seg.getOperandIndex i⟩
    · obtain ⟨u, hu, slot⟩ := changed
      obtain ⟨target, argIndex, _⟩ := W.originAtSlot facts run opIn read valid hu slot
      exact Or.inl ⟨u, hu, slot, by rw [argIndex, ← target, destEq]⟩
    · refine Or.inr ⟨fun u hu slot => changed ⟨u, hu, slot⟩, ?_⟩
      intro selected
      obtain ⟨⟨j, width⟩, mem, heq⟩ := List.mem_map.mp selected
      have targets : block = dest := congrArg BlockArgumentPtr.block heq
      have sameIndex : j = i := congrArg BlockArgumentPtr.index heq
      subst j
      have useIn := W.edge_mem opIn inRange (destEq.trans targets.symm)
      obtain ⟨u, hu, eq, _⟩ := (W.update_iff (width := width)).mpr
        ⟨_, useIn, seg, i, read, List.mem_reverse.mp mem, rfl⟩
      exact changed ⟨u, hu, eq⟩

end PhiWidening
end Veir.Legalization.CTreeProofs
