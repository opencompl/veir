module

public import Veir.Rewriter.WellFormed.BlockConstructionAllocation
public import Veir.Rewriter.WellFormed.ConstructionBlockArguments
public import Veir.Rewriter.WellFormed.InsertBlock

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
  [HasBuffedOpCode OpInfo]

/-- Successful block creation, including argument initialization and optional insertion,
    preserves the original well-formedness predicate. -/
theorem Rewriter.createBlock_preserves_wellFormed
    {ctx newCtx : Sim.IRContext OpInfo} {newBlock : Sim.BlockPtr}
    {argTypes : Array TypeAttr} {insertionPoint : Option BlockInsertPoint}
    {hip : insertionPoint.maybe BlockInsertPoint.InBounds ctx.spec}
    {hrep : insertionPoint.maybe₁ BlockInsertPoint.IsRepr}
    (wf : ctx.spec.WellFormed)
    (h : Rewriter.createBlock ctx argTypes insertionPoint hip hrep = some (newCtx, newBlock)) :
    newCtx.spec.WellFormed := by
  simp only [Rewriter.createBlock_def, Rewriter.createBlockSim] at h
  split at h
  · split at h
    · contradiction
    · rename_i allocated allocatedCtx halloc
      have allocatedWf := Sim.BlockPtr.allocRecycled_constructionWellFormed wf halloc
      have hallocSpec := Sim.BlockPtr.allocRecycled_spec' _ halloc
      have capacity : (allocated.spec.get! allocatedCtx.spec).capArguments = argTypes.size := by
        grind [Block.empty, Array.size_toUInt64_toNat]
      split at h
      · contradiction
      · rename_i initializedCtx hinit
        have initializedWf := Rewriter.initBlockArguments_wellFormed allocatedWf capacity (by simp) hinit
        split at h
        · simp only [Option.bind_eq_bind, Option.bind] at h
          split at h
          · contradiction
          · rename_i insertedCtx hinsert
            have insertedWf := Rewriter.insertBlock?_WellFormed _ _ _ _ _ _ _ initializedWf hinsert
            grind
        · grind
  · contradiction

end Veir
