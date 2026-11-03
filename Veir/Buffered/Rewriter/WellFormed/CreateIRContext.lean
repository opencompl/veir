module

public import Veir.Buffered.Rewriter.WellFormed.CreateOp
public import Veir.Buffered.Rewriter.WellFormed.CreateRegion
public import Veir.Buffered.Rewriter.WellFormed.CreateBlock

public section

namespace Veir.Buffered

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
  [HasBuffedOpCode OpInfo]

theorem Sim.IRContext.empty_wellFormed :
    (Sim.IRContext.empty (OpInfo := OpInfo)).spec.WellFormed := by
  simpa only [Sim.IRContext.empty, Sim.IRContext.spec, Erased.out_mk] using
    Veir.Buffered.IRContext.empty_wellFormed (opInfo := OpInfo)

/-- Successfully creating the initial module, region, and block yields a fully
    well-formed context. -/
theorem IRContext.create_wellFormed
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr}
    (h : IRContext.create OpInfo = some (ctx, op)) :
    ctx.spec.WellFormed := by
  simp only [IRContext.create] at h
  split at h
  · contradiction
  · rename_i regionCtx region hregion
    have regionWf := Rewriter.createRegion_wellFormed Sim.IRContext.empty_wellFormed hregion
    split at h
    · contradiction
    · rename_i operationCtx operation hoperation
      have operationWf := Rewriter.createOp_preserves_wellFormed regionWf hoperation
      split at h
      · contradiction
      · rename_i blockCtx block hblock
        have blockWf := Rewriter.createBlock_preserves_wellFormed operationWf hblock
        grind

end Veir.Buffered
