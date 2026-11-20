module

public import Veir.Passes.InstructionSelection.Branches.Frame
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.IR.Basic

public section
namespace Veir.Legalization.CTreeProofs

/-- The only newly allocated operations satisfy `added`. No blocks or regions are allocated. -/
structure PhiAllocation (src dst : WfIRContext OpCode) (added : OperationPtr → Prop) : Prop where
  block : ∀ {b : BlockPtr}, b.InBounds dst.raw → b.InBounds src.raw
  region : ∀ {r : RegionPtr}, r.InBounds dst.raw → r.InBounds src.raw
  operation : ∀ {op : OperationPtr}, op.InBounds dst.raw → op.InBounds src.raw ∨ added op

abbrev PhiCastAllocation (src dst : WfIRContext OpCode) :=
  PhiAllocation src dst fun op =>
    (op.getOpType! dst.raw = .gmir .g_trunc ∨ op.getOpType! dst.raw = .gmir .g_anyext) ∧
      op.getSuccessors! dst.raw = #[]

namespace PhiAllocation

theorem refl (src : WfIRContext OpCode) {added} : PhiAllocation src src added :=
  ⟨id, id, Or.inl⟩

theorem castStep {src dst : WfIRContext OpCode} {cast : OperationPtr}
    (alloc : PhiAllocation src dst (· = cast))
    (code : cast.getOpType! dst.raw = .gmir .g_trunc ∨ cast.getOpType! dst.raw = .gmir .g_anyext)
    (successors : cast.getSuccessors! dst.raw = #[]) : PhiCastAllocation src dst := by
  refine ⟨alloc.block, alloc.region, fun hin => ?_⟩
  obtain h | rfl := alloc.operation hin
  · exact .inl h
  · exact .inr ⟨code, successors⟩

theorem transCasts {src middle dst : WfIRContext OpCode}
    (first : PhiCastAllocation src middle) (last : PhiCastAllocation middle dst)
    (headers : ∀ op : OperationPtr, op.InBounds middle.raw →
      op.getOpType! dst.raw = op.getOpType! middle.raw ∧
      op.getSuccessors! dst.raw = op.getSuccessors! middle.raw) : PhiCastAllocation src dst := by
  refine ⟨fun h => first.block (last.block h), fun h => first.region (last.region h), fun h => ?_⟩
  rcases last.operation h with mid | fresh
  · rcases first.operation mid with old | fresh
    · exact .inl old
    · exact .inr (by rwa [(headers _ mid).1, (headers _ mid).2])
  · exact .inr fresh

theorem create {D : Type} [HasOpInfo D] [HasDialect OpCode D]
    {ctx dst : WfIRContext OpCode} {opcode : D} {props : propertiesOf opcode}
    {results : Array TypeAttr} {operands : Array ValuePtr} {succ : Array BlockPtr}
    {ip : InsertPoint} {created : OperationPtr} {h₁ h₂ h₃ h₄}
    (h : WfRewriter.createOp ctx opcode results operands succ #[] props (some ip)
      h₁ h₂ h₃ h₄ = some (dst, created)) : PhiAllocation ctx dst (· = created) := by
  unfold WfRewriter.createOp at h
  split at h <;> try contradiction
  rename_i raw allocated hraw
  cases h
  constructor
  · intro b hb
    simpa using (Rewriter.createOp_inBounds (.block b) hraw).mp hb
  · intro r hr
    simpa using (Rewriter.createOp_inBounds (.region r) hraw).mp hr
  · intro op ho
    simpa using (Rewriter.createOp_inBounds (.operation op) hraw).mp ho

end PhiAllocation
end Veir.Legalization.CTreeProofs
