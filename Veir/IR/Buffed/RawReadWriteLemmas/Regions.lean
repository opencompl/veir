module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs
public import Veir.IR.Buffed.RawReadWriteLemmas.Tactics

set_option warn.sorry false
set_option linter.unusedVariables false

public section

namespace Veir.Buffed

open scoped Veir.Buffed

section read_write

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] {ctx : Sim.IRContext OpInfo}

theorem Sim.RegionPtr.after_lt_ctx (rg : Veir.RegionPtr) (opIb : rg.InBounds ctx.spec) :
    rg.id + Buffed.Region.Offsets.afterInt ≤ ctx.buf.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.region rg) (by grind)
  simp_all [RegionPtr.range, layout_simp]
  grind

/-! ## RegionMPtr.readFirstBlock! after RegionMPtr.writeFirstBlock -/

@[layout_grind =]
theorem RegionMPtr.readFirstBlock!_regionMPtr_writeFirstBlock (rg : Veir.RegionPtr) (ptr : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (writeFirstBlock ctx.buf ptr.impl val.impl h) rg.toM =
    if rg = ptr.spec then val.impl else Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_rg readFirstBlock!, writeFirstBlock, rg, ptr, rgIb, ptrIb

/-! ## RegionMPtr.readFirstBlock! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_regionMPtr_writeLastBlock (rg : Veir.RegionPtr) (ptr : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (writeLastBlock ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_rg readFirstBlock!, writeLastBlock, rg, ptr, rgIb, ptrIb

/-! ## RegionMPtr.readFirstBlock! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_regionMPtr_writeParent (rg : Veir.RegionPtr) (ptr : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (writeParent ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_rg readFirstBlock!, writeParent, rg, ptr, rgIb, ptrIb

/-! ## RegionMPtr.readLastBlock! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_regionMPtr_writeFirstBlock (rg : Veir.RegionPtr) (ptr : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (writeFirstBlock ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_rg readLastBlock!, writeFirstBlock, rg, ptr, rgIb, ptrIb

/-! ## RegionMPtr.readLastBlock! after RegionMPtr.writeLastBlock -/

@[layout_grind =]
theorem RegionMPtr.readLastBlock!_regionMPtr_writeLastBlock (rg : Veir.RegionPtr) (ptr : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (writeLastBlock ctx.buf ptr.impl val.impl h) rg.toM =
    if rg = ptr.spec then val.impl else Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_rg readLastBlock!, writeLastBlock, rg, ptr, rgIb, ptrIb

/-! ## RegionMPtr.readLastBlock! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_regionMPtr_writeParent (rg : Veir.RegionPtr) (ptr : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (writeParent ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_rg readLastBlock!, writeParent, rg, ptr, rgIb, ptrIb

/-! ## RegionMPtr.readParent! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_regionMPtr_writeFirstBlock (rg : Veir.RegionPtr) (ptr : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (writeFirstBlock ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_rg readParent!, writeFirstBlock, rg, ptr, rgIb, ptrIb

/-! ## RegionMPtr.readParent! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_regionMPtr_writeLastBlock (rg : Veir.RegionPtr) (ptr : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (writeLastBlock ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_rg readParent!, writeLastBlock, rg, ptr, rgIb, ptrIb

/-! ## RegionMPtr.readParent! after RegionMPtr.writeParent -/

@[layout_grind =]
theorem RegionMPtr.readParent!_regionMPtr_writeParent (rg : Veir.RegionPtr) (ptr : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (writeParent ctx.buf ptr.impl val.impl h) rg.toM =
    if rg = ptr.spec then val.impl else Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_rg readParent!, writeParent, rg, ptr, rgIb, ptrIb

end read_write

end Veir.Buffed
