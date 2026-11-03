module

public import Veir.Buffered.Parser.IRPointers
public import Veir.Buffered.Rewriter.WellFormed.EraseOp
public import Veir.Buffered.Rewriter.EraseContainers
import all Veir.Buffered.Rewriter.Basic
import all Veir.Buffered.IR.Buffed.Basic

public section
namespace Veir.Buffered

/-- Successful block allocation returns a live block, including after optional insertion. -/
theorem Rewriter.createBlock_new_inBounds
    {ctx next : Parser.IR.RawContext} {types ip hip hrep p}
    (heq : createBlock ctx types ip hip hrep = some (next, p)) : p.InBounds next := by
  simp only [createBlock] at heq
  split at heq
  · split at heq
    · grind
    · simp at heq
      split at heq
      · grind
      · split at heq
        · simp [Option.bind] at heq
          split at heq
          · grind
          · grind [generic_ptr_grind]
        · grind [generic_ptr_grind]
  · grind

theorem Rewriter.createRegion_inBounds_mono {ctx next : Parser.IR.RawContext} {p}
    (hc : createRegion ctx = some (next, p)) (q : Sim.GenericPtr) (hq : q.InBounds ctx) :
    q.InBounds next := by
  simp only [createRegion] at hc
  split at hc
  · simp at hc
  · simp at hc
    grind

private theorem dealloc_operation {ctx : Parser.IR.RawContext} {op p : Sim.OperationPtr}
    {hi hd} (hp : p.InBounds ctx) (hne : p.spec ≠ op.spec) :
    p.InBounds (op.dealloc ctx hi hd) := by
  constructor
  · exact hp.sim
  · simp only [Sim.OperationPtr.dealloc, Sim.OperationPtr.forget, Sim.IRContext.releaseRange,
      Sim.IRContext.spec, Erased.out_mk]
    grind [OperationPtr.dealloc, OperationPtr.inBounds_def]

private theorem dealloc_block {ctx : Parser.IR.RawContext} {op : Sim.OperationPtr} {p : Sim.BlockPtr}
    {hi hd} (hp : p.InBounds ctx) : p.InBounds (op.dealloc ctx hi hd) := by
  constructor
  · exact hp.sim
  · simp only [Sim.OperationPtr.dealloc, Sim.OperationPtr.forget, Sim.IRContext.releaseRange,
      Sim.IRContext.spec, Erased.out_mk]
    grind [OperationPtr.dealloc, BlockPtr.inBounds_def]

private theorem dealloc_region {ctx : Parser.IR.RawContext} {op : Sim.OperationPtr} {p : Sim.RegionPtr}
    {hi hd} (hp : p.InBounds ctx) : p.InBounds (op.dealloc ctx hi hd) := by
  constructor
  · exact hp.sim
  · simp only [Sim.OperationPtr.dealloc, Sim.OperationPtr.forget, Sim.IRContext.releaseRange,
      Sim.IRContext.spec, Erased.out_mk]
    grind [OperationPtr.dealloc, RegionPtr.inBounds_def]

theorem Rewriter.eraseOp_operation_inBounds {ctx : Parser.IR.RawContext} {op p : Sim.OperationPtr}
    {hc hi ho hs hd} (hp : p.InBounds ctx) (hne : p.spec ≠ op.spec) :
    p.InBounds (eraseOp ctx op hc hi ho hs hd) := by
  simp only [eraseOp]
  apply dealloc_operation (hne := hne)
  grind [generic_ptr_grind]

theorem Rewriter.eraseOp_block_inBounds {ctx : Parser.IR.RawContext} {op : Sim.OperationPtr} {p : Sim.BlockPtr}
    {hc hi ho hs hd} (hp : p.InBounds ctx) : p.InBounds (eraseOp ctx op hc hi ho hs hd) := by
  simp only [eraseOp]
  apply dealloc_block
  grind [generic_ptr_grind]

theorem Rewriter.eraseOp_region_inBounds {ctx : Parser.IR.RawContext} {op : Sim.OperationPtr} {p : Sim.RegionPtr}
    {hc hi ho hs hd} (hp : p.InBounds ctx) : p.InBounds (eraseOp ctx op hc hi ho hs hd) := by
  simp only [eraseOp]
  apply dealloc_region
  grind [generic_ptr_grind]

end Veir.Buffered
