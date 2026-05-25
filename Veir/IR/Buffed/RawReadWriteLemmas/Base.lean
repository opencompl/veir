module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs
import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs

public section

namespace Veir.Buffed

section read_write

variable [HasOpInfo OpInfo] {ctx : Sim.IRContext OpInfo}

theorem Sim.OperationPtr.after_lt_ctx (op : Veir.OperationPtr) (opIb : op.InBounds ctx.spec) :
    op.id + Buffed.Operation.Offsets.afterInt op ctx.spec ≤ ctx.buf.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.operation op) (by grind)
  simp_all [OperationPtr.range, layout_simp]
  grind [= Buffed.Operation.Offsets.after_ideal]

theorem Sim.BlockPtr.after_lt_ctx (bl : Veir.BlockPtr) (opIb : bl.InBounds ctx.spec) :
    bl.id + Buffed.Block.Offsets.afterInt bl ctx.spec ≤ ctx.buf.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.block bl) (by grind)
  simp_all [BlockPtr.range, layout_simp]
  grind [= Buffed.Block.Offsets.after_ideal]

theorem Sim.RegionPtr.after_lt_ctx (rg : Veir.RegionPtr) (opIb : rg.InBounds ctx.spec) :
    rg.id + Buffed.Region.Offsets.afterInt ≤ ctx.buf.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.region rg) (by grind)
  simp_all [RegionPtr.range, layout_simp]
  grind

end read_write

end Veir.Buffed
