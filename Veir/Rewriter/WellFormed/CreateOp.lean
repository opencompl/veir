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

theorem Rewriter.createOp_preserves_wellFormed
    {ctx newCtx : Sim.IRContext OpInfo} {newOp : Sim.OperationPtr}
    {opType : OpInfo} {resultTypes : Array TypeAttr}
    {operands : Array Sim.ValuePtr} {blockOperands : Array Sim.BlockPtr}
    {regions : Array Sim.RegionPtr} {properties : HasOpInfo.propertiesOf opType}
    {insertionPoint : Option InsertPoint}
    {hoper : (∀ i (hi : i < operands.size), operands[i].InBounds ctx)} {hblockOperands : (∀ i (hi : i < blockOperands.size), blockOperands[i].InBounds ctx)}
    {hregions : (∀ i (hi : i < regions.size), regions[i].InBounds ctx)} {hins : insertionPoint.maybe InsertPoint.InBounds ctx.spec}
    {hrep : insertionPoint.maybe₁ InsertPoint.IsRepr} {htypes : resultTypes.size < 2^32}
    {hx : ctx.spec.FieldsInBounds}
    (wf : ctx.spec.WellFormed)
    (h : Rewriter.createOp ctx opType resultTypes operands blockOperands regions
      properties insertionPoint hoper hblockOperands hregions hins hrep htypes hx =
      some (newCtx, newOp)) :
    newCtx.spec.WellFormed := by
  simp only [Rewriter.createOp.unfold] at h
  split at h <;> try contradiction
  split at h
  · contradiction
  · rename_i allocated allocatedCtx halloc
    have allocatedWf := Sim.OperationPtr.allocFresh_wellFormed wf halloc
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i regionsCtx hregionsCtx
    have regionsWf := Rewriter.initOpRegions_wellFormed
      (Rewriter.initOpResults_wellFormed rfl
        allocatedWf) hregionsCtx
    split at h
    · simp only [Option.bind_eq_bind, Option.bind] at h
      split at h <;> try contradiction
      rename_i inserted hinsert
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      apply Rewriter.insertOp?_WellFormed _ _ _ _ _ _ _ _ hinsert
      exact Rewriter.initBlockOperands_wellFormed (Rewriter.initOpOperands_wellFormed regionsWf rfl) rfl
    · obtain ⟨rfl, rfl⟩ := Option.some.inj h
      exact Rewriter.initBlockOperands_wellFormed (Rewriter.initOpOperands_wellFormed regionsWf rfl) rfl

end Veir
