module

public import Veir.Rewriter.Basic
public import Veir.Rewriter.LinkedList.WellFormed

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
  [HasBuffedOpCode OpInfo]

@[grind .]
theorem Rewriter.insertBlock?_WellFormed
    (ctx : Sim.IRContext OpInfo) (newBlock : Sim.BlockPtr) (ip : BlockInsertPoint)
    (newBlockIn : newBlock.InBounds ctx)
    (ipIn : ip.InBounds ctx.spec)
    (ipRepr : ip.IsRepr)
    (ctxIn : ctx.spec.FieldsInBounds)
    (wf : ctx.spec.WellFormed)
    (heq : Rewriter.insertBlock? ctx newBlock ip newBlockIn ipIn ipRepr ctxIn =
      some newCtx) :
    newCtx.spec.WellFormed := by
  simp only [Rewriter.insertBlock?_def, Rewriter.insertBlock?Sim] at heq
  split at heq
  · simp at heq
  · rename_i parent hParent
    have hParentIB : parent.InBounds ctx :=
      BlockInsertPoint.region_InBounds ctxIn ipIn ipRepr hParent ipIn
    have hRegionIB : (ip.region ctx ipIn ipRepr).InBounds ctx := by
      cases ip <;>
        grind [BlockInsertPoint.region_def, BlockInsertPoint.regionSim,
          generic_ptr_grind]
    have hParentSpec : (ip.region ctx ipIn ipRepr).spec = some parent.spec :=
      Sim.OptionRegionPtr.toOption_some hRegionIB hParent
    have hRegion : ip.region! ctx.spec = some parent.spec := by
      rw [BlockInsertPoint.region!_eq_region ip ctx ipIn ipRepr]
      exact hParentSpec
    have hPrevParent : (ip.prev ctx ipIn).spec.maybe₁
        (fun prev => (prev.get! ctx.spec).parent = some parent.spec) := by
      rw [Option.maybe₁_def]
      intro prev hPrev
      have hPrevSpec : ip.prev! ctx.spec = some prev := by
        rw [BlockInsertPoint.prev!_eq_prev ipIn]
        exact hPrev
      have := BlockInsertPoint.BlockPtr_parent!_of_prev_eq_some
        (ip := ip) (ctx := ctx.spec) wf ipIn hRegion
        hPrevSpec
      simpa [hRegion] using this
    have hNextParent : ip.next.spec.maybe₁
        (fun next => (next.get! ctx.spec).parent = some parent.spec) := by
      cases ip with
      | before block =>
          simpa only [BlockInsertPoint.next_before, Option.maybe₁_some,
            BlockInsertPoint.region!_before] using hRegion
      | atEnd region =>
          simp [BlockInsertPoint.next_atEnd, Sim.OptionBlockPtr.none,
            Option.maybe₁_def]
    exact Sim.IRContext.wellFormed_BlockPtr_linkBetweenWithParent wf heq
      hPrevParent hNextParent (ipRepr := ipRepr) ipIn hRegion rfl
      (BlockInsertPoint.prev!_eq_prev ipIn)

end Veir
