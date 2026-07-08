module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs
public import Veir.IR.Buffed.RawReadWriteLemmas.Tactics
import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs

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

/-! ## RegionMPtr.readFirstBlock! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_operationMPtr_writeNext (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readFirstBlock!, OperationMPtr.writeNext, rg, op2

/-! ## RegionMPtr.readLastBlock! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_operationMPtr_writeNext (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readLastBlock!, OperationMPtr.writeNext, rg, op2

/-! ## RegionMPtr.readParent! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_operationMPtr_writeNext (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opScalar readParent!, OperationMPtr.writeNext, rg, op2

/-! ## RegionMPtr.readFirstBlock! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_operationMPtr_writeNumResults (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readFirstBlock!, OperationMPtr.writeNumResults, rg, op2

/-! ## RegionMPtr.readLastBlock! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_operationMPtr_writeNumResults (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readLastBlock!, OperationMPtr.writeNumResults, rg, op2

/-! ## RegionMPtr.readParent! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_operationMPtr_writeNumResults (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opScalar readParent!, OperationMPtr.writeNumResults, rg, op2

/-! ## RegionMPtr.readFirstBlock! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_operationMPtr_writeNumBlockOperands (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readFirstBlock!, OperationMPtr.writeNumBlockOperands, rg, op2

/-! ## RegionMPtr.readLastBlock! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_operationMPtr_writeNumBlockOperands (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readLastBlock!, OperationMPtr.writeNumBlockOperands, rg, op2

/-! ## RegionMPtr.readParent! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_operationMPtr_writeNumBlockOperands (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opScalar readParent!, OperationMPtr.writeNumBlockOperands, rg, op2

/-! ## RegionMPtr.readFirstBlock! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_operationMPtr_writeNumRegions (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readFirstBlock!, OperationMPtr.writeNumRegions, rg, op2

/-! ## RegionMPtr.readLastBlock! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_operationMPtr_writeNumRegions (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readLastBlock!, OperationMPtr.writeNumRegions, rg, op2

/-! ## RegionMPtr.readParent! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_operationMPtr_writeNumRegions (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opScalar readParent!, OperationMPtr.writeNumRegions, rg, op2

/-! ## RegionMPtr.readFirstBlock! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_operationMPtr_writeNumOperands (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readFirstBlock!, OperationMPtr.writeNumOperands, rg, op2

/-! ## RegionMPtr.readLastBlock! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_operationMPtr_writeNumOperands (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readLastBlock!, OperationMPtr.writeNumOperands, rg, op2

/-! ## RegionMPtr.readParent! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_operationMPtr_writeNumOperands (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opScalar readParent!, OperationMPtr.writeNumOperands, rg, op2

/-! ## RegionMPtr.readFirstBlock! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_operationMPtr_writeAttrs (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readFirstBlock!, OperationMPtr.writeAttrs, rg, op2

/-! ## RegionMPtr.readLastBlock! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_operationMPtr_writeAttrs (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readLastBlock!, OperationMPtr.writeAttrs, rg, op2

/-! ## RegionMPtr.readParent! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_operationMPtr_writeAttrs (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opScalar readParent!, OperationMPtr.writeAttrs, rg, op2

/-! ## RegionMPtr.readFirstBlock! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_operationMPtr_writeOpType (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readFirstBlock!, OperationMPtr.writeOpType, rg, op2

/-! ## RegionMPtr.readLastBlock! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_operationMPtr_writeOpType (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readLastBlock!, OperationMPtr.writeOpType, rg, op2

/-! ## RegionMPtr.readParent! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_operationMPtr_writeOpType (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opScalar readParent!, OperationMPtr.writeOpType, rg, op2

/-! ## RegionMPtr.readFirstBlock! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_operationMPtr_writePrev (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readFirstBlock!, OperationMPtr.writePrev, rg, op2

/-! ## RegionMPtr.readLastBlock! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_operationMPtr_writePrev (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readLastBlock!, OperationMPtr.writePrev, rg, op2

/-! ## RegionMPtr.readParent! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_operationMPtr_writePrev (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opScalar readParent!, OperationMPtr.writePrev, rg, op2

/-! ## RegionMPtr.readFirstBlock! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_operationMPtr_writeParent (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readFirstBlock!, OperationMPtr.writeParent, rg, op2

/-! ## RegionMPtr.readLastBlock! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_operationMPtr_writeParent (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opScalar readLastBlock!, OperationMPtr.writeParent, rg, op2

/-! ## RegionMPtr.readParent! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_operationMPtr_writeParent (rg : Veir.RegionPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opScalar readParent!, OperationMPtr.writeParent, rg, op2

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

/-! ## RegionMPtr.readFirstBlock! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockMPtr_writeFirstUse (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_block readFirstBlock!, BlockMPtr.writeFirstUse, rg, w2, w2Ib

/-! ## RegionMPtr.readFirstBlock! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockMPtr_writePrev (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_block readFirstBlock!, BlockMPtr.writePrev, rg, w2, w2Ib

/-! ## RegionMPtr.readFirstBlock! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockMPtr_writeNext (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_block readFirstBlock!, BlockMPtr.writeNext, rg, w2, w2Ib

/-! ## RegionMPtr.readFirstBlock! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockMPtr_writeParent (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_block readFirstBlock!, BlockMPtr.writeParent, rg, w2, w2Ib

/-! ## RegionMPtr.readFirstBlock! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockMPtr_writeFirstOp (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_block readFirstBlock!, BlockMPtr.writeFirstOp, rg, w2, w2Ib

/-! ## RegionMPtr.readFirstBlock! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockMPtr_writeLastOp (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_block readFirstBlock!, BlockMPtr.writeLastOp, rg, w2, w2Ib

/-! ## RegionMPtr.readFirstBlock! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockMPtr_writeNumArguments (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_block readFirstBlock!, BlockMPtr.writeNumArguments, rg, w2, w2Ib

/-! ## RegionMPtr.readLastBlock! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockMPtr_writeFirstUse (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_block readLastBlock!, BlockMPtr.writeFirstUse, rg, w2, w2Ib

/-! ## RegionMPtr.readLastBlock! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockMPtr_writePrev (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_block readLastBlock!, BlockMPtr.writePrev, rg, w2, w2Ib

/-! ## RegionMPtr.readLastBlock! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockMPtr_writeNext (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_block readLastBlock!, BlockMPtr.writeNext, rg, w2, w2Ib

/-! ## RegionMPtr.readLastBlock! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockMPtr_writeParent (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_block readLastBlock!, BlockMPtr.writeParent, rg, w2, w2Ib

/-! ## RegionMPtr.readLastBlock! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockMPtr_writeFirstOp (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_block readLastBlock!, BlockMPtr.writeFirstOp, rg, w2, w2Ib

/-! ## RegionMPtr.readLastBlock! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockMPtr_writeLastOp (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_block readLastBlock!, BlockMPtr.writeLastOp, rg, w2, w2Ib

/-! ## RegionMPtr.readLastBlock! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockMPtr_writeNumArguments (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_block readLastBlock!, BlockMPtr.writeNumArguments, rg, w2, w2Ib

/-! ## RegionMPtr.readParent! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockMPtr_writeFirstUse (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_block readParent!, BlockMPtr.writeFirstUse, rg, w2, w2Ib

/-! ## RegionMPtr.readParent! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockMPtr_writePrev (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_block readParent!, BlockMPtr.writePrev, rg, w2, w2Ib

/-! ## RegionMPtr.readParent! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockMPtr_writeNext (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_block readParent!, BlockMPtr.writeNext, rg, w2, w2Ib

/-! ## RegionMPtr.readParent! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockMPtr_writeParent (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_block readParent!, BlockMPtr.writeParent, rg, w2, w2Ib

/-! ## RegionMPtr.readParent! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockMPtr_writeFirstOp (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_block readParent!, BlockMPtr.writeFirstOp, rg, w2, w2Ib

/-! ## RegionMPtr.readParent! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockMPtr_writeLastOp (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_block readParent!, BlockMPtr.writeLastOp, rg, w2, w2Ib

/-! ## RegionMPtr.readParent! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockMPtr_writeNumArguments (rg : Veir.RegionPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_block readParent!, BlockMPtr.writeNumArguments, rg, w2, w2Ib

/-! ## RegionMPtr.readFirstBlock! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_opResultMPtr_writeType (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opResult readFirstBlock!, OpResultMPtr.writeType, rg, w2

/-! ## RegionMPtr.readFirstBlock! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_opResultMPtr_writeFirstUse (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opResult readFirstBlock!, OpResultMPtr.writeFirstUse, rg, w2

/-! ## RegionMPtr.readFirstBlock! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_opResultMPtr_writeIndex (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opResult readFirstBlock!, OpResultMPtr.writeIndex, rg, w2

/-! ## RegionMPtr.readFirstBlock! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_opResultMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opResult readFirstBlock!, OpResultMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readLastBlock! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_opResultMPtr_writeType (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opResult readLastBlock!, OpResultMPtr.writeType, rg, w2

/-! ## RegionMPtr.readLastBlock! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_opResultMPtr_writeFirstUse (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opResult readLastBlock!, OpResultMPtr.writeFirstUse, rg, w2

/-! ## RegionMPtr.readLastBlock! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_opResultMPtr_writeIndex (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opResult readLastBlock!, OpResultMPtr.writeIndex, rg, w2

/-! ## RegionMPtr.readLastBlock! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_opResultMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opResult readLastBlock!, OpResultMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readParent! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_opResultMPtr_writeType (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opResult readParent!, OpResultMPtr.writeType, rg, w2

/-! ## RegionMPtr.readParent! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_opResultMPtr_writeFirstUse (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opResult readParent!, OpResultMPtr.writeFirstUse, rg, w2

/-! ## RegionMPtr.readParent! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_opResultMPtr_writeIndex (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opResult readParent!, OpResultMPtr.writeIndex, rg, w2

/-! ## RegionMPtr.readParent! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_opResultMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opResult readParent!, OpResultMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readFirstBlock! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_opOperandMPtr_writeNextUse (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opOperand readFirstBlock!, OpOperandMPtr.writeNextUse, rg, w2

/-! ## RegionMPtr.readFirstBlock! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_opOperandMPtr_writeBack (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opOperand readFirstBlock!, OpOperandMPtr.writeBack, rg, w2

/-! ## RegionMPtr.readFirstBlock! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_opOperandMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opOperand readFirstBlock!, OpOperandMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readFirstBlock! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_opOperandMPtr_writeValue (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_opOperand readFirstBlock!, OpOperandMPtr.writeValue, rg, w2

/-! ## RegionMPtr.readLastBlock! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_opOperandMPtr_writeNextUse (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opOperand readLastBlock!, OpOperandMPtr.writeNextUse, rg, w2

/-! ## RegionMPtr.readLastBlock! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_opOperandMPtr_writeBack (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opOperand readLastBlock!, OpOperandMPtr.writeBack, rg, w2

/-! ## RegionMPtr.readLastBlock! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_opOperandMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opOperand readLastBlock!, OpOperandMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readLastBlock! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_opOperandMPtr_writeValue (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_opOperand readLastBlock!, OpOperandMPtr.writeValue, rg, w2

/-! ## RegionMPtr.readParent! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_opOperandMPtr_writeNextUse (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opOperand readParent!, OpOperandMPtr.writeNextUse, rg, w2

/-! ## RegionMPtr.readParent! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_opOperandMPtr_writeBack (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opOperand readParent!, OpOperandMPtr.writeBack, rg, w2

/-! ## RegionMPtr.readParent! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_opOperandMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opOperand readParent!, OpOperandMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readParent! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_opOperandMPtr_writeValue (rg : Veir.RegionPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_opOperand readParent!, OpOperandMPtr.writeValue, rg, w2

/-! ## RegionMPtr.readFirstBlock! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockOperandMPtr_writeNextUse (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_blockOperand readFirstBlock!, BlockOperandMPtr.writeNextUse, rg, w2

/-! ## RegionMPtr.readFirstBlock! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockOperandMPtr_writeBack (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_blockOperand readFirstBlock!, BlockOperandMPtr.writeBack, rg, w2

/-! ## RegionMPtr.readFirstBlock! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockOperandMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_blockOperand readFirstBlock!, BlockOperandMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readFirstBlock! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockOperandMPtr_writeValue (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_blockOperand readFirstBlock!, BlockOperandMPtr.writeValue, rg, w2

/-! ## RegionMPtr.readLastBlock! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockOperandMPtr_writeNextUse (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_blockOperand readLastBlock!, BlockOperandMPtr.writeNextUse, rg, w2

/-! ## RegionMPtr.readLastBlock! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockOperandMPtr_writeBack (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_blockOperand readLastBlock!, BlockOperandMPtr.writeBack, rg, w2

/-! ## RegionMPtr.readLastBlock! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockOperandMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_blockOperand readLastBlock!, BlockOperandMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readLastBlock! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockOperandMPtr_writeValue (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_blockOperand readLastBlock!, BlockOperandMPtr.writeValue, rg, w2

/-! ## RegionMPtr.readParent! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockOperandMPtr_writeNextUse (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_blockOperand readParent!, BlockOperandMPtr.writeNextUse, rg, w2

/-! ## RegionMPtr.readParent! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockOperandMPtr_writeBack (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_blockOperand readParent!, BlockOperandMPtr.writeBack, rg, w2

/-! ## RegionMPtr.readParent! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockOperandMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_blockOperand readParent!, BlockOperandMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readParent! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockOperandMPtr_writeValue (rg : Veir.RegionPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_blockOperand readParent!, BlockOperandMPtr.writeValue, rg, w2

/-! ## RegionMPtr.readFirstBlock! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockArgumentMPtr_writeType (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_blockArg readFirstBlock!, BlockArgumentMPtr.writeType, rg, w2

/-! ## RegionMPtr.readFirstBlock! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockArgumentMPtr_writeFirstUse (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_blockArg readFirstBlock!, BlockArgumentMPtr.writeFirstUse, rg, w2

/-! ## RegionMPtr.readFirstBlock! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockArgumentMPtr_writeIndex (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_blockArg readFirstBlock!, BlockArgumentMPtr.writeIndex, rg, w2

/-! ## RegionMPtr.readFirstBlock! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockArgumentMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  rw_rg_blockArg readFirstBlock!, BlockArgumentMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readLastBlock! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockArgumentMPtr_writeType (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_blockArg readLastBlock!, BlockArgumentMPtr.writeType, rg, w2

/-! ## RegionMPtr.readLastBlock! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockArgumentMPtr_writeFirstUse (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_blockArg readLastBlock!, BlockArgumentMPtr.writeFirstUse, rg, w2

/-! ## RegionMPtr.readLastBlock! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockArgumentMPtr_writeIndex (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_blockArg readLastBlock!, BlockArgumentMPtr.writeIndex, rg, w2

/-! ## RegionMPtr.readLastBlock! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockArgumentMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  rw_rg_blockArg readLastBlock!, BlockArgumentMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readParent! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockArgumentMPtr_writeType (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_blockArg readParent!, BlockArgumentMPtr.writeType, rg, w2

/-! ## RegionMPtr.readParent! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockArgumentMPtr_writeFirstUse (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_blockArg readParent!, BlockArgumentMPtr.writeFirstUse, rg, w2

/-! ## RegionMPtr.readParent! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockArgumentMPtr_writeIndex (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_blockArg readParent!, BlockArgumentMPtr.writeIndex, rg, w2

/-! ## RegionMPtr.readParent! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockArgumentMPtr_writeOwner (rg : Veir.RegionPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (rgIb : rg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  rw_rg_blockArg readParent!, BlockArgumentMPtr.writeOwner, rg, w2

/-! ## RegionMPtr.readFirstBlock! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_valueImplMPtr_writeType (rg : Veir.RegionPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstBlock!, ValueImplMPtr.writeType, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstBlock!, ValueImplMPtr.writeType, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readLastBlock! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_valueImplMPtr_writeType (rg : Veir.RegionPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readLastBlock!, ValueImplMPtr.writeType, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readLastBlock!, ValueImplMPtr.writeType, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readParent! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_valueImplMPtr_writeType (rg : Veir.RegionPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (rgIb : rg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readParent!, ValueImplMPtr.writeType, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readParent!, ValueImplMPtr.writeType, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readFirstBlock! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_valueImplMPtr_writeFirstUse (rg : Veir.RegionPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstBlock!, ValueImplMPtr.writeFirstUse, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstBlock!, ValueImplMPtr.writeFirstUse, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readLastBlock! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_valueImplMPtr_writeFirstUse (rg : Veir.RegionPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readLastBlock!, ValueImplMPtr.writeFirstUse, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readLastBlock!, ValueImplMPtr.writeFirstUse, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readParent! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_valueImplMPtr_writeFirstUse (rg : Veir.RegionPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readParent!, ValueImplMPtr.writeFirstUse, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readParent!, ValueImplMPtr.writeFirstUse, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readFirstBlock! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_blockOperandPtrMPtr_write (rg : Veir.RegionPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readFirstBlock!, BlockOperandPtrMPtr.write, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat,
      IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readFirstBlock!, BlockOperandPtrMPtr.write, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readLastBlock! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_blockOperandPtrMPtr_write (rg : Veir.RegionPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readLastBlock!, BlockOperandPtrMPtr.write, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat,
      IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readLastBlock!, BlockOperandPtrMPtr.write, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readParent! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_blockOperandPtrMPtr_write (rg : Veir.RegionPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readParent!, BlockOperandPtrMPtr.write, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat,
      IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readParent!, BlockOperandPtrMPtr.write, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readFirstBlock! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readFirstBlock!_opOperandPtrMPtr_write (rg : Veir.RegionPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readFirstBlock! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readFirstBlock! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation opr.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readFirstBlock!, OpOperandPtrMPtr.write, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation res.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readFirstBlock!, OpOperandPtrMPtr.write, layout_grind,
        RegionPtr.range, RegionPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block arg.block) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      have := @Sim.BlockArgumentPtr.after_lt_ctx
      grind (splits := 20) [readFirstBlock!, OpOperandPtrMPtr.write, layout_grind,
        RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readLastBlock! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readLastBlock!_opOperandPtrMPtr_write (rg : Veir.RegionPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readLastBlock! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readLastBlock! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation opr.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readLastBlock!, OpOperandPtrMPtr.write, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation res.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readLastBlock!, OpOperandPtrMPtr.write, layout_grind,
        RegionPtr.range, RegionPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block arg.block) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      have := @Sim.BlockArgumentPtr.after_lt_ctx
      grind (splits := 20) [readLastBlock!, OpOperandPtrMPtr.write, layout_grind,
        RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## RegionMPtr.readParent! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem RegionMPtr.readParent!_opOperandPtrMPtr_write (rg : Veir.RegionPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (rgIb : rg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.RegionMPtr.readParent! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) rg.toM =
    Buffed.RegionMPtr.readParent! ctx.buf rg.toM := by
  have := @Sim.RegionPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation opr.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readParent!, OpOperandPtrMPtr.write, layout_grind,
      RegionPtr.range, RegionPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.region rg) (.operation res.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readParent!, OpOperandPtrMPtr.write, layout_grind,
        RegionPtr.range, RegionPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.region rg) (.block arg.block) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      have := @Sim.BlockArgumentPtr.after_lt_ctx
      grind (splits := 20) [readParent!, OpOperandPtrMPtr.write, layout_grind,
        RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
