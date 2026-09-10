module

public import Veir.Rewriter.WellFormed.ConstructionAllocation
public import Veir.Rewriter.WellFormed.ConstructionResults
public import Veir.Rewriter.WellFormed.ConstructionRegions
public import Veir.Rewriter.WellFormed.ConstructionOperands
public import Veir.Rewriter.WellFormed.ConstructionOperandsGetSet
public import Veir.Rewriter.WellFormed.ConstructionBlockOperands
public import Veir.Rewriter.WellFormed.InsertOp

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
  [HasBuffedOpCode OpInfo]

/-- Once the operand and successor arrays are filled, all construction obligations
    imply the original, unchanged well-formedness predicate. -/
theorem Rewriter.finishOpOperands_wellFormed
    {ctx operandsCtx finalCtx : Sim.IRContext OpInfo} {op : Sim.OperationPtr}
    {operands : Sim.ArrayValuePtr} {blockOperands : Sim.ArrayBlockPtr}
    {hop hv hi hc hb hvb hib hcb}
    (wf : ConstructionWellFormed ctx.spec op.spec ∅ ∅)
    (results : (op.spec.get! ctx.spec).capResults = op.spec.getNumResults! ctx.spec)
    (regions : (op.spec.get! ctx.spec).capRegions = op.spec.getNumRegions! ctx.spec)
    (operandCapacity : (op.spec.get! ctx.spec).capOperands = operands.size)
    (blockCapacity : (op.spec.get! ctx.spec).capBlockOperands = blockOperands.size)
    (hoper : Rewriter.initOpOperands op ctx hop operands hv 0 hi hc = operandsCtx)
    (hblock : Rewriter.initBlockOperands op operandsCtx blockOperands 0 hb hvb hib hcb = finalCtx) :
    finalCtx.spec.WellFormed := by
  rw [← hblock]
  apply IRContext.ConstructionWellFormed.to_wellFormed
    (Rewriter.initBlockOperands_constructionWellFormed
      (Rewriter.initOpOperands_constructionWellFormed wf hoper) rfl)
  · rw [Rewriter.initBlockOperands_preserves_capResults,
      Rewriter.initBlockOperands_preserves_numResults,
      Rewriter.initOpOperands_preserves_capResults _ hoper,
      Rewriter.initOpOperands_preserves_numResults _ hoper]
    exact results
  · rw [Rewriter.initBlockOperands_preserves_capRegions,
      Rewriter.initBlockOperands_preserves_numRegions,
      Rewriter.initOpOperands_preserves_capRegions _ hoper,
      Rewriter.initOpOperands_preserves_numRegions _ hoper]
    exact regions
  · rw [Rewriter.initBlockOperands_preserves_capOperands,
      Rewriter.initBlockOperands_preserves_numOperands,
      Rewriter.initOpOperands_preserves_capOperands _ hoper,
      Rewriter.initOpOperands_numOperands hoper (by simp)]
    exact operandCapacity
  · rw [Rewriter.initBlockOperands_preserves_capBlockOperands,
      Rewriter.initBlockOperands_numSuccessors (by simp),
      ← hoper, Rewriter.initOpOperands_preserves_capBlockOperands]
    exact blockCapacity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem Rewriter.createOp_preserves_wellFormed
    {ctx newCtx : Sim.IRContext OpInfo} {newOp : Sim.OperationPtr}
    {opType : OpInfo} {resultTypes : Array TypeAttr}
    {operands : Sim.ArrayValuePtr} {blockOperands : Sim.ArrayBlockPtr}
    {regions : Sim.ArrayRegionPtr} {properties : HasOpInfo.propertiesOf opType}
    {insertionPoint : Option InsertPoint}
    {hoper : operands.InBounds ctx} {hblockOperands : blockOperands.InBounds ctx}
    {hregions : regions.InBounds ctx} {hins : insertionPoint.maybe InsertPoint.InBounds ctx.spec}
    {hrep : insertionPoint.maybe₁ InsertPoint.IsRepr} {htypes : resultTypes.size < 2^32}
    {hx : ctx.spec.FieldsInBounds}
    (wf : ctx.spec.WellFormed)
    (h : Rewriter.createOp ctx opType resultTypes operands blockOperands regions
      properties insertionPoint hoper hblockOperands hregions hins hrep htypes hx =
      some (newCtx, newOp)) :
    newCtx.spec.WellFormed := by
  simp only [Rewriter.createOp_def, Rewriter.createOpSim] at h
  split at h
  · contradiction
  · rename_i allocated allocatedCtx halloc
    have hallocWf := Sim.OperationPtr.allocRecycled_constructionWellFormed wf halloc
    split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i regionsCtx hregionsCtx
        have hregionsWf := Rewriter.initOpRegions_constructionWellFormed
          (Rewriter.initOpResults_constructionWellFormed rfl hallocWf) hregionsCtx
        have hspecAlloc := Sim.OperationPtr.allocRecycled_spec' halloc
        have hresultsFull : (allocated.spec.get! regionsCtx.spec).capResults =
            allocated.spec.getNumResults! regionsCtx.spec := by
          rw [Rewriter.initOpRegions_preserves_capResults _ hregionsCtx,
            Rewriter.initOpRegions_preserves_numResults _ hregionsCtx,
            Rewriter.initOpResults_preserves_capResults _ (heq := rfl),
            Rewriter.initOpResults_numResults (heq := rfl) (by simp)]
          grind [Operation.empty, Array.sizeU64_toNat]
        have hregionsFull : (allocated.spec.get! regionsCtx.spec).capRegions =
            allocated.spec.getNumRegions! regionsCtx.spec := by
          rw [Rewriter.initOpRegions_preserves_capRegions _ hregionsCtx,
            Rewriter.initOpRegions_numRegions (by simp) hregionsCtx,
            Rewriter.initOpResults_preserves_capRegions _ (heq := rfl)]
          grind [Operation.empty]
        have hoperandCapacity : (allocated.spec.get! regionsCtx.spec).capOperands = operands.size := by
          rw [Rewriter.initOpRegions_preserves_capOperands _ hregionsCtx,
            Rewriter.initOpResults_preserves_capOperands _ (heq := rfl)]
          grind [Operation.empty]
        have hblockCapacity : (allocated.spec.get! regionsCtx.spec).capBlockOperands = blockOperands.size := by
          rw [Rewriter.initOpRegions_preserves_capBlockOperands _ hregionsCtx,
            Rewriter.initOpResults_preserves_capBlockOperands _ (heq := rfl)]
          grind [Operation.empty]
        split at h
        · rename_i ip hip
          simp only [Option.bind_eq_bind, Option.bind] at h
          split at h
          · contradiction
          · rename_i insertedCtx hinsert
            have hinsertWf : insertedCtx.spec.WellFormed := by
              apply Rewriter.insertOp?_WellFormed _ _ _ _ _ _ _ _ hinsert
              exact Rewriter.finishOpOperands_wellFormed hregionsWf hresultsFull hregionsFull
                hoperandCapacity hblockCapacity rfl rfl
            grind
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨hctxEq, hptrEq⟩
          exact Rewriter.finishOpOperands_wellFormed hregionsWf hresultsFull hregionsFull
            hoperandCapacity hblockCapacity rfl hctxEq

end Veir
