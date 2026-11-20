module

public import Veir.Passes.Legalization.Validity.PhiWidening
import all Veir.Passes.Legalization.Validity.PhiEdges
import all Veir.IR.Basic
import all Veir.IR.InBounds
import all Veir.Interfaces.ControlFlowInterfaces

public section
namespace Veir.Legalization.CTreeProofs

/-- The branch interface describes the edge identified by this particular successor use. -/
def DescribesPhiEdge (ctx : IRContext OpCode) (u : BlockOperandPtr)
    (e : OperationPtr × SuccessorOperands) : Prop :=
  e.1 = u.op ∧ BranchOpInterface.getSuccessorOperands? u.op u.index ctx = some e.2

inductive PhiEdgeList (ctx : IRContext OpCode) : List BlockOperandPtr →
    List (OperationPtr × SuccessorOperands) → Prop
  | nil : PhiEdgeList ctx [] []
  | cons : DescribesPhiEdge ctx u e → PhiEdgeList ctx us es → PhiEdgeList ctx (u :: us) (e :: es)

theorem PhiEdgeList.exists_left_of_mem_right (d : PhiEdgeList ctx us es) (h : e ∈ es) :
    ∃ u ∈ us, DescribesPhiEdge ctx u e := by
  induction d with
  | nil => simp at h
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, .head _, head⟩
    · obtain ⟨_, m, v⟩ := ih h; exact ⟨_, .tail _ m, v⟩

theorem PhiEdgeList.exists_right_of_mem_left (d : PhiEdgeList ctx us es) (h : u ∈ us) :
    ∃ e ∈ es, DescribesPhiEdge ctx u e := by
  induction d with
  | nil => simp at h
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, .head _, head⟩
    · obtain ⟨_, m, v⟩ := ih h; exact ⟨_, .tail _ m, v⟩

theorem describesPhiEdges {ctx : IRContext OpCode} {uses : List BlockOperandPtr}
    {edges : List (OperationPtr × SuccessorOperands)}
    (segments : uses.mapM (fun u => do
      return (u.op, ← BranchOpInterface.getSuccessorOperands? u.op u.index ctx)) = some edges) :
    PhiEdgeList ctx uses edges := by
  induction uses generalizing edges with
  | nil => cases segments; exact .nil
  | cons u us ih =>
    rw [List.mapM_cons] at segments
    cases read : BranchOpInterface.getSuccessorOperands? u.op u.index ctx with
    | none => simp [read, bind, Option.bind] at segments
    | some seg =>
      simp [read, bind, Option.bind, pure] at segments
      split at segments <;> try contradiction
      cases segments
      exact .cons ⟨rfl, read⟩ (ih (by assumption))

namespace PhiWidening

variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
    (W : PhiWidening src dst block args)

theorem update_iff {p : OpOperandPtr} {width : Nat} :
    (∃ u ∈ W.updates, u.operand = p ∧ u.width = width) ↔
    ∃ edge ∈ W.uses, ∃ seg i,
      BranchOpInterface.getSuccessorOperands? edge.op edge.index src.raw = some seg ∧
      (i, width) ∈ args ∧ p = ⟨edge.op, seg.getOperandIndex i⟩ := by
  have descriptions := describesPhiEdges W.segments
  constructor
  · rintro ⟨u, member, rfl, rfl⟩
    have requested := List.mem_map_of_mem (f := fun u : BranchOperandExtension => (u.operand, u.width)) member
    rw [W.requests] at requested
    obtain ⟨⟨op, seg⟩, edgeMem, ⟨i, w⟩, selected, same⟩ :=
      List.mem_flatMap.mp requested |>.imp fun e => And.imp_right List.mem_map.mp
    obtain ⟨edge, edgeIn, srcOp, read⟩ := descriptions.exists_left_of_mem_right edgeMem
    have slotEq := congrArg Prod.fst same
    have widthEq := congrArg Prod.snd same
    change w = u.width at widthEq
    change op = edge.op at srcOp
    change (⟨op, seg.getOperandIndex i⟩ : OpOperandPtr) = u.operand at slotEq
    exact ⟨edge, by simpa using edgeIn, seg, i, read, widthEq ▸ selected, srcOp ▸ slotEq.symm⟩
  · rintro ⟨edge, member, seg, i, read, selected, rfl⟩
    obtain ⟨⟨op, seg'⟩, edgeMem, rfl, read'⟩ := descriptions.exists_right_of_mem_left
      (show edge ∈ W.uses.toList by simpa using member)
    obtain rfl := Option.some.inj (read.symm.trans read')
    have req : ((⟨edge.op, seg.getOperandIndex i⟩ : OpOperandPtr), width) ∈
        W.edges.flatMap (fun e => branchOperandRequests e.1 e.2 args) :=
      List.mem_flatMap.mpr ⟨_, edgeMem, List.mem_map.mpr ⟨_, selected, rfl⟩⟩
    rw [← W.requests] at req
    obtain ⟨u, hu, eq⟩ := List.mem_map.mp req
    exact ⟨u, hu, congrArg Prod.fst eq, congrArg Prod.snd eq⟩

theorem edge_mem {op : OperationPtr} (opIn : op.InBounds src.raw) {edge : Nat}
    (within : edge < op.getNumSuccessors! src.raw) (dest : op.getSuccessor! src.raw edge = block) :
    op.getBlockOperand edge ∈ W.uses := by
  have useIn : (op.getBlockOperand edge).InBounds src.raw := by
    grind [BlockOperandPtr.InBounds, OperationPtr.getNumSuccessors!]
  have hUse : (op.getBlockOperand edge).getValue! src.raw = block := by
    grind [OperationPtr.getSuccessor!_def, OperationPtr.getBlockOperand]
  exact (W.chain.allUsesInChain _ useIn hUse).mpr (by simp)

theorem noUpdates_to_block {op : OperationPtr} (opIn : op.InBounds src.raw)
    (untouched : ∀ u ∈ W.updates, u.operand.op ≠ op)
    (succ : block ∈ op.getSuccessors! src.raw) : args = [] := by
  obtain ⟨edge, within, dest⟩ := OperationPtr.getSuccessors!.mem_iff_exists_index.mp succ
  have hin := W.edge_mem opIn within dest
  obtain ⟨⟨_, seg⟩, _, _, read⟩ := (describesPhiEdges W.segments).exists_right_of_mem_left
    (show op.getBlockOperand edge ∈ W.uses.toList by simpa using hin)
  cases h : args with
  | nil => rfl
  | cons x xs =>
    obtain ⟨u, hu, operand, _⟩ := (W.update_iff (width := x.2)).mpr
      ⟨_, hin, seg, x.1, read, by simp [h], rfl⟩
    exact False.elim (untouched u hu (congrArg OpOperandPtr.op operand))

end PhiWidening
end Veir.Legalization.CTreeProofs
