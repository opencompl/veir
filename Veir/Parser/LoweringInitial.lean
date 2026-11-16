module

public import Veir.Parser.LoweringTotal
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.Rewriter.Basic

/-! The initial module exists and satisfies the allocation invariant. -/

public section
namespace Veir.LLVMLowering

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem createModule_raw_total :
    ∃ raw root, IRContext.create OpCode = some (raw, root) ∧ AllocationSafe raw := by
  obtain ⟨raw₁, r, hr, hs₁⟩ := AllocationSafe.empty.allocateRegion
  have hx : (IRContext.empty OpCode).FieldsInBounds := IRContext.empty_wellFormed.inBounds
  obtain ⟨raw₂, root, ho, hs₂⟩ := hs₁.createOp_total (ts := #[]) (vs := #[]) (rs := #[r]) (block := default) (insert := false)
    (by grind) Builtin.module default (by simp) (by simp) (by grind) (by grind) (by simp)
  obtain ⟨raw₃, b, hb, hs₃⟩ := hs₂.createBlock_total (ts := #[]) (by grind) (show r.InBounds raw₂ by grind)
  refine ⟨raw₃, root, ?_, hs₃⟩
  unfold IRContext.create; grind

theorem createModule_total : ∃ ctx root, WfIRContext.create OpCode = some (ctx, root) ∧ AllocationSafe ctx.raw := by
  obtain ⟨raw, root, hr, hs⟩ := createModule_raw_total
  let ctx : WfIRContext OpCode := ⟨raw, by grind [IRContext.wellFormed_IRContext_create]⟩
  refine ⟨ctx, root, ?_, hs⟩
  unfold WfIRContext.create; split <;> simp_all <;> (dsimp only [ctx]; grind)

end Veir.LLVMLowering
