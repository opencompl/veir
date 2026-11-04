module

public import Veir.IR.Buffed.ContainerDealloc

@[expose] public section
namespace Veir
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

/-- Logically erase a detached block, retaining its arena storage. As with operation
 deallocation, `hDealloc` rules out dangling references from surviving IR:
 the block must have no operations, successor uses, or argument uses. -/
buffed (inline := true)
def Rewriter.eraseBlockSim (ctx : Sim.IRContext OpInfo) (block : Sim.BlockPtr)
    (ib : block.InBounds ctx)
    (_hparent : (block.spec.get! ctx.spec).parent = none)
    (hDealloc : (block.spec.dealloc ctx.spec).FieldsInBounds) : Sim.IRContext OpInfo :=
  Sim.BlockPtr.dealloc ctx block ib hDealloc

/-- Logically erase a detached region, retaining its arena storage. `hDealloc` rules out
 surviving blocks or operations that still reference the region. -/
buffed (inline := true)
def Rewriter.eraseRegionSim (ctx : Sim.IRContext OpInfo) (region : Sim.RegionPtr)
    (ib : region.InBounds ctx)
    (_hparent : (region.spec.get! ctx.spec).parent = none)
    (hDealloc : (region.spec.dealloc ctx.spec).FieldsInBounds) : Sim.IRContext OpInfo :=
  Sim.RegionPtr.dealloc ctx region ib hDealloc

@[simp]
theorem Rewriter.eraseBlock_spec (ctx : Sim.IRContext OpInfo) (block : Sim.BlockPtr)
    (ib : block.InBounds ctx) (hp hd) :
    (eraseBlock ctx block ib hp hd).spec = block.spec.dealloc ctx.spec := by
  simp [eraseBlock.unfold, Sim.BlockPtr.dealloc.unfold, Sim.BlockPtr.forget.unfold,
    Sim.IRContext.spec]

@[simp]
theorem Rewriter.eraseRegion_spec (ctx : Sim.IRContext OpInfo) (region : Sim.RegionPtr)
    (ib : region.InBounds ctx) (hp hd) :
    (eraseRegion ctx region ib hp hd).spec = region.spec.dealloc ctx.spec := by
  simp [eraseRegion.unfold, Sim.RegionPtr.dealloc.unfold, Sim.RegionPtr.forget.unfold,
    Sim.IRContext.spec]

theorem Rewriter.eraseBlock_wellFormed (ctx : Sim.IRContext OpInfo) (block : Sim.BlockPtr)
    (ib : block.InBounds ctx) (hp hd) (wf : ctx.spec.WellFormed) :
    (eraseBlock ctx block ib hp hd).spec.WellFormed := by
  rw [eraseBlock_spec]
  exact IRContext.wellFormed_BlockPtr_dealloc wf hp hd

theorem Rewriter.eraseRegion_wellFormed (ctx : Sim.IRContext OpInfo) (region : Sim.RegionPtr)
    (ib : region.InBounds ctx) (hp hd) (wf : ctx.spec.WellFormed) :
    (eraseRegion ctx region ib hp hd).spec.WellFormed := by
  rw [eraseRegion_spec]
  exact IRContext.wellFormed_RegionPtr_dealloc wf hp hd

end Veir
