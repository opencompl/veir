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

theorem Sim.BlockArgumentPtr.after_lt_ctx (op : Veir.BlockArgumentPtr) (opIb : op.InBounds ctx.spec) :
    op.toFlat + Buffed.BlockArgument.Offsets.afterInt ≤ ctx.buf.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.block op.block) (by grind)
  have hincl₁ := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) op (by grind)
  rw [BlockArgumentPtr.toFlat_ideal]
  simp_all only [BlockArgumentPtr.range_ideal]
  grind [layout_grind]

@[local ext, local grind ext]
theorem _root_.Veir.BlockArgumentPtr.ext (x y : BlockArgumentPtr) : x.block = y.block → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

/-! ## BlockArgumentMPtr.readType! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_operationMPtr_writeNext (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opScalar readType!, OperationMPtr.writeNext, arg, op2

/-! ## BlockArgumentMPtr.readFirstUse! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_operationMPtr_writeNext (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opScalar readFirstUse!, OperationMPtr.writeNext, arg, op2

/-! ## BlockArgumentMPtr.readIndex! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_operationMPtr_writeNext (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opScalar readIndex!, OperationMPtr.writeNext, arg, op2

/-! ## BlockArgumentMPtr.readOwner! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_operationMPtr_writeNext (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opScalar readOwner!, OperationMPtr.writeNext, arg, op2

/-! ## BlockArgumentMPtr.readType! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_operationMPtr_writeNumResults (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opScalar readType!, OperationMPtr.writeNumResults, arg, op2

/-! ## BlockArgumentMPtr.readFirstUse! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_operationMPtr_writeNumResults (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opScalar readFirstUse!, OperationMPtr.writeNumResults, arg, op2

/-! ## BlockArgumentMPtr.readIndex! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_operationMPtr_writeNumResults (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opScalar readIndex!, OperationMPtr.writeNumResults, arg, op2

/-! ## BlockArgumentMPtr.readOwner! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_operationMPtr_writeNumResults (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opScalar readOwner!, OperationMPtr.writeNumResults, arg, op2

/-! ## BlockArgumentMPtr.readType! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_operationMPtr_writeNumBlockOperands (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opScalar readType!, OperationMPtr.writeNumBlockOperands, arg, op2

/-! ## BlockArgumentMPtr.readFirstUse! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_operationMPtr_writeNumBlockOperands (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opScalar readFirstUse!, OperationMPtr.writeNumBlockOperands, arg, op2

/-! ## BlockArgumentMPtr.readIndex! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_operationMPtr_writeNumBlockOperands (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opScalar readIndex!, OperationMPtr.writeNumBlockOperands, arg, op2

/-! ## BlockArgumentMPtr.readOwner! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_operationMPtr_writeNumBlockOperands (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opScalar readOwner!, OperationMPtr.writeNumBlockOperands, arg, op2

/-! ## BlockArgumentMPtr.readType! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_operationMPtr_writeNumRegions (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opScalar readType!, OperationMPtr.writeNumRegions, arg, op2

/-! ## BlockArgumentMPtr.readFirstUse! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_operationMPtr_writeNumRegions (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opScalar readFirstUse!, OperationMPtr.writeNumRegions, arg, op2

/-! ## BlockArgumentMPtr.readIndex! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_operationMPtr_writeNumRegions (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opScalar readIndex!, OperationMPtr.writeNumRegions, arg, op2

/-! ## BlockArgumentMPtr.readOwner! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_operationMPtr_writeNumRegions (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opScalar readOwner!, OperationMPtr.writeNumRegions, arg, op2

/-! ## BlockArgumentMPtr.readType! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_operationMPtr_writeNumOperands (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opScalar readType!, OperationMPtr.writeNumOperands, arg, op2

/-! ## BlockArgumentMPtr.readFirstUse! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_operationMPtr_writeNumOperands (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opScalar readFirstUse!, OperationMPtr.writeNumOperands, arg, op2

/-! ## BlockArgumentMPtr.readIndex! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_operationMPtr_writeNumOperands (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opScalar readIndex!, OperationMPtr.writeNumOperands, arg, op2

/-! ## BlockArgumentMPtr.readOwner! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_operationMPtr_writeNumOperands (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opScalar readOwner!, OperationMPtr.writeNumOperands, arg, op2

/-! ## BlockArgumentMPtr.readType! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_operationMPtr_writeAttrs (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opScalar readType!, OperationMPtr.writeAttrs, arg, op2

/-! ## BlockArgumentMPtr.readFirstUse! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_operationMPtr_writeAttrs (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opScalar readFirstUse!, OperationMPtr.writeAttrs, arg, op2

/-! ## BlockArgumentMPtr.readIndex! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_operationMPtr_writeAttrs (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opScalar readIndex!, OperationMPtr.writeAttrs, arg, op2

/-! ## BlockArgumentMPtr.readOwner! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_operationMPtr_writeAttrs (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opScalar readOwner!, OperationMPtr.writeAttrs, arg, op2

/-! ## BlockArgumentMPtr.readType! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_operationMPtr_writeOpType (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opScalar readType!, OperationMPtr.writeOpType, arg, op2

/-! ## BlockArgumentMPtr.readFirstUse! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_operationMPtr_writeOpType (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opScalar readFirstUse!, OperationMPtr.writeOpType, arg, op2

/-! ## BlockArgumentMPtr.readIndex! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_operationMPtr_writeOpType (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opScalar readIndex!, OperationMPtr.writeOpType, arg, op2

/-! ## BlockArgumentMPtr.readOwner! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_operationMPtr_writeOpType (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opScalar readOwner!, OperationMPtr.writeOpType, arg, op2

/-! ## BlockArgumentMPtr.readType! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_operationMPtr_writePrev (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opScalar readType!, OperationMPtr.writePrev, arg, op2

/-! ## BlockArgumentMPtr.readFirstUse! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_operationMPtr_writePrev (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opScalar readFirstUse!, OperationMPtr.writePrev, arg, op2

/-! ## BlockArgumentMPtr.readIndex! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_operationMPtr_writePrev (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opScalar readIndex!, OperationMPtr.writePrev, arg, op2

/-! ## BlockArgumentMPtr.readOwner! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_operationMPtr_writePrev (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opScalar readOwner!, OperationMPtr.writePrev, arg, op2

/-! ## BlockArgumentMPtr.readType! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_operationMPtr_writeParent (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opScalar readType!, OperationMPtr.writeParent, arg, op2

/-! ## BlockArgumentMPtr.readFirstUse! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_operationMPtr_writeParent (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opScalar readFirstUse!, OperationMPtr.writeParent, arg, op2

/-! ## BlockArgumentMPtr.readIndex! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_operationMPtr_writeParent (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opScalar readIndex!, OperationMPtr.writeParent, arg, op2

/-! ## BlockArgumentMPtr.readOwner! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_operationMPtr_writeParent (arg : Veir.BlockArgumentPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opScalar readOwner!, OperationMPtr.writeParent, arg, op2

/-! ## BlockArgumentMPtr.readType! after BlockArgumentMPtr.writeType -/

@[layout_grind =]
theorem BlockArgumentMPtr.readType!_blockArgumentMPtr_writeType (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockArgumentMPtr.writeType ctx.buf ptr.impl val h) arg.toM =
    if arg = ptr.spec then val else Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_ba readType!, BlockArgumentMPtr.writeType, arg, ptr

/-! ## BlockArgumentMPtr.readType! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockArgumentMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_ba readType!, BlockArgumentMPtr.writeFirstUse, arg, ptr

/-! ## BlockArgumentMPtr.readType! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockArgumentMPtr_writeIndex (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf ptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_ba readType!, BlockArgumentMPtr.writeIndex, arg, ptr

/-! ## BlockArgumentMPtr.readType! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockArgumentMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_ba readType!, BlockArgumentMPtr.writeOwner, arg, ptr

/-! ## BlockArgumentMPtr.readFirstUse! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockArgumentMPtr_writeType (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeType ctx.buf ptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_ba readFirstUse!, BlockArgumentMPtr.writeType, arg, ptr

/-! ## BlockArgumentMPtr.readFirstUse! after BlockArgumentMPtr.writeFirstUse -/

@[layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockArgumentMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) arg.toM =
    if arg = ptr.spec then val.impl else Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_ba readFirstUse!, BlockArgumentMPtr.writeFirstUse, arg, ptr

/-! ## BlockArgumentMPtr.readFirstUse! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockArgumentMPtr_writeIndex (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf ptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_ba readFirstUse!, BlockArgumentMPtr.writeIndex, arg, ptr

/-! ## BlockArgumentMPtr.readFirstUse! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockArgumentMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_ba readFirstUse!, BlockArgumentMPtr.writeOwner, arg, ptr

/-! ## BlockArgumentMPtr.readIndex! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockArgumentMPtr_writeType (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockArgumentMPtr.writeType ctx.buf ptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_ba readIndex!, BlockArgumentMPtr.writeType, arg, ptr

/-! ## BlockArgumentMPtr.readIndex! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockArgumentMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_ba readIndex!, BlockArgumentMPtr.writeFirstUse, arg, ptr

/-! ## BlockArgumentMPtr.readIndex! after BlockArgumentMPtr.writeIndex -/

@[layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockArgumentMPtr_writeIndex (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf ptr.impl val h) arg.toM =
    if arg = ptr.spec then val else Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_ba readIndex!, BlockArgumentMPtr.writeIndex, arg, ptr

/-! ## BlockArgumentMPtr.readIndex! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockArgumentMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_ba readIndex!, BlockArgumentMPtr.writeOwner, arg, ptr

/-! ## BlockArgumentMPtr.readOwner! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockArgumentMPtr_writeType (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeType ctx.buf ptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_ba readOwner!, BlockArgumentMPtr.writeType, arg, ptr

/-! ## BlockArgumentMPtr.readOwner! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockArgumentMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_ba readOwner!, BlockArgumentMPtr.writeFirstUse, arg, ptr

/-! ## BlockArgumentMPtr.readOwner! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockArgumentMPtr_writeIndex (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf ptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_ba readOwner!, BlockArgumentMPtr.writeIndex, arg, ptr

/-! ## BlockArgumentMPtr.readOwner! after BlockArgumentMPtr.writeOwner -/

@[layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockArgumentMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf ptr.impl val.impl h) arg.toM =
    if arg = ptr.spec then val.impl else Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_ba readOwner!, BlockArgumentMPtr.writeOwner, arg, ptr

/-! ## BlockArgumentMPtr.readType! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockMPtr.writeFirstUse ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_block readType!, BlockMPtr.writeFirstUse, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readType! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockMPtr_writePrev (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockMPtr.writePrev ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_block readType!, BlockMPtr.writePrev, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readType! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockMPtr_writeNext (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockMPtr.writeNext ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_block readType!, BlockMPtr.writeNext, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readType! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockMPtr_writeParent (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockMPtr.writeParent ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_block readType!, BlockMPtr.writeParent, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readType! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockMPtr_writeFirstOp (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockMPtr.writeFirstOp ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_block readType!, BlockMPtr.writeFirstOp, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readType! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockMPtr_writeLastOp (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockMPtr.writeLastOp ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_block readType!, BlockMPtr.writeLastOp, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readType! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockMPtr_writeNumArguments (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockMPtr.writeNumArguments ctx.buf bl2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_block readType!, BlockMPtr.writeNumArguments, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readFirstUse! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockMPtr.writeFirstUse ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_block readFirstUse!, BlockMPtr.writeFirstUse, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readFirstUse! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockMPtr_writePrev (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockMPtr.writePrev ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_block readFirstUse!, BlockMPtr.writePrev, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readFirstUse! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockMPtr_writeNext (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockMPtr.writeNext ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_block readFirstUse!, BlockMPtr.writeNext, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readFirstUse! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockMPtr_writeParent (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockMPtr.writeParent ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_block readFirstUse!, BlockMPtr.writeParent, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readFirstUse! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockMPtr_writeFirstOp (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockMPtr.writeFirstOp ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_block readFirstUse!, BlockMPtr.writeFirstOp, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readFirstUse! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockMPtr_writeLastOp (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockMPtr.writeLastOp ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_block readFirstUse!, BlockMPtr.writeLastOp, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readFirstUse! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockMPtr_writeNumArguments (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockMPtr.writeNumArguments ctx.buf bl2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_block readFirstUse!, BlockMPtr.writeNumArguments, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readIndex! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockMPtr.writeFirstUse ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_block readIndex!, BlockMPtr.writeFirstUse, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readIndex! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockMPtr_writePrev (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockMPtr.writePrev ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_block readIndex!, BlockMPtr.writePrev, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readIndex! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockMPtr_writeNext (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockMPtr.writeNext ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_block readIndex!, BlockMPtr.writeNext, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readIndex! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockMPtr_writeParent (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockMPtr.writeParent ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_block readIndex!, BlockMPtr.writeParent, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readIndex! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockMPtr_writeFirstOp (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockMPtr.writeFirstOp ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_block readIndex!, BlockMPtr.writeFirstOp, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readIndex! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockMPtr_writeLastOp (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockMPtr.writeLastOp ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_block readIndex!, BlockMPtr.writeLastOp, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readIndex! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockMPtr_writeNumArguments (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockMPtr.writeNumArguments ctx.buf bl2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_block readIndex!, BlockMPtr.writeNumArguments, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readOwner! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockMPtr.writeFirstUse ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_block readOwner!, BlockMPtr.writeFirstUse, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readOwner! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockMPtr_writePrev (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockMPtr.writePrev ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_block readOwner!, BlockMPtr.writePrev, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readOwner! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockMPtr_writeNext (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockMPtr.writeNext ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_block readOwner!, BlockMPtr.writeNext, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readOwner! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockMPtr_writeParent (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockMPtr.writeParent ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_block readOwner!, BlockMPtr.writeParent, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readOwner! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockMPtr_writeFirstOp (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockMPtr.writeFirstOp ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_block readOwner!, BlockMPtr.writeFirstOp, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readOwner! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockMPtr_writeLastOp (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockMPtr.writeLastOp ctx.buf bl2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_block readOwner!, BlockMPtr.writeLastOp, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readOwner! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockMPtr_writeNumArguments (arg : Veir.BlockArgumentPtr) (bl2 : Sim.BlockPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockMPtr.writeNumArguments ctx.buf bl2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_block readOwner!, BlockMPtr.writeNumArguments, arg, bl2, bl2Ib

/-! ## BlockArgumentMPtr.readType! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_opResultMPtr_writeType (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opResult readType!, OpResultMPtr.writeType, arg, w2

/-! ## BlockArgumentMPtr.readType! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_opResultMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opResult readType!, OpResultMPtr.writeFirstUse, arg, w2

/-! ## BlockArgumentMPtr.readType! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_opResultMPtr_writeIndex (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opResult readType!, OpResultMPtr.writeIndex, arg, w2

/-! ## BlockArgumentMPtr.readType! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_opResultMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opResult readType!, OpResultMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_opResultMPtr_writeType (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opResult readFirstUse!, OpResultMPtr.writeType, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_opResultMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opResult readFirstUse!, OpResultMPtr.writeFirstUse, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_opResultMPtr_writeIndex (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opResult readFirstUse!, OpResultMPtr.writeIndex, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_opResultMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opResult readFirstUse!, OpResultMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_opResultMPtr_writeType (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opResult readIndex!, OpResultMPtr.writeType, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_opResultMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opResult readIndex!, OpResultMPtr.writeFirstUse, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_opResultMPtr_writeIndex (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opResult readIndex!, OpResultMPtr.writeIndex, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_opResultMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opResult readIndex!, OpResultMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_opResultMPtr_writeType (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opResult readOwner!, OpResultMPtr.writeType, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_opResultMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opResult readOwner!, OpResultMPtr.writeFirstUse, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_opResultMPtr_writeIndex (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opResult readOwner!, OpResultMPtr.writeIndex, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_opResultMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opResult readOwner!, OpResultMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readType! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_opOperandMPtr_writeNextUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opOperand readType!, OpOperandMPtr.writeNextUse, arg, w2

/-! ## BlockArgumentMPtr.readType! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_opOperandMPtr_writeBack (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opOperand readType!, OpOperandMPtr.writeBack, arg, w2

/-! ## BlockArgumentMPtr.readType! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_opOperandMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opOperand readType!, OpOperandMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readType! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_opOperandMPtr_writeValue (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_opOperand readType!, OpOperandMPtr.writeValue, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_opOperandMPtr_writeNextUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opOperand readFirstUse!, OpOperandMPtr.writeNextUse, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_opOperandMPtr_writeBack (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opOperand readFirstUse!, OpOperandMPtr.writeBack, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_opOperandMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opOperand readFirstUse!, OpOperandMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_opOperandMPtr_writeValue (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_opOperand readFirstUse!, OpOperandMPtr.writeValue, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_opOperandMPtr_writeNextUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opOperand readIndex!, OpOperandMPtr.writeNextUse, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_opOperandMPtr_writeBack (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opOperand readIndex!, OpOperandMPtr.writeBack, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_opOperandMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opOperand readIndex!, OpOperandMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_opOperandMPtr_writeValue (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_opOperand readIndex!, OpOperandMPtr.writeValue, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_opOperandMPtr_writeNextUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opOperand readOwner!, OpOperandMPtr.writeNextUse, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_opOperandMPtr_writeBack (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opOperand readOwner!, OpOperandMPtr.writeBack, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_opOperandMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opOperand readOwner!, OpOperandMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_opOperandMPtr_writeValue (arg : Veir.BlockArgumentPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_opOperand readOwner!, OpOperandMPtr.writeValue, arg, w2

/-! ## BlockArgumentMPtr.readType! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockOperandMPtr_writeNextUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_blockOperand readType!, BlockOperandMPtr.writeNextUse, arg, w2

/-! ## BlockArgumentMPtr.readType! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockOperandMPtr_writeBack (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_blockOperand readType!, BlockOperandMPtr.writeBack, arg, w2

/-! ## BlockArgumentMPtr.readType! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockOperandMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_blockOperand readType!, BlockOperandMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readType! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockOperandMPtr_writeValue (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_blockOperand readType!, BlockOperandMPtr.writeValue, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockOperandMPtr_writeNextUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_blockOperand readFirstUse!, BlockOperandMPtr.writeNextUse, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockOperandMPtr_writeBack (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_blockOperand readFirstUse!, BlockOperandMPtr.writeBack, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockOperandMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_blockOperand readFirstUse!, BlockOperandMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockOperandMPtr_writeValue (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_blockOperand readFirstUse!, BlockOperandMPtr.writeValue, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockOperandMPtr_writeNextUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_blockOperand readIndex!, BlockOperandMPtr.writeNextUse, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockOperandMPtr_writeBack (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_blockOperand readIndex!, BlockOperandMPtr.writeBack, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockOperandMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_blockOperand readIndex!, BlockOperandMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockOperandMPtr_writeValue (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_blockOperand readIndex!, BlockOperandMPtr.writeValue, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockOperandMPtr_writeNextUse (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_blockOperand readOwner!, BlockOperandMPtr.writeNextUse, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockOperandMPtr_writeBack (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_blockOperand readOwner!, BlockOperandMPtr.writeBack, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockOperandMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_blockOperand readOwner!, BlockOperandMPtr.writeOwner, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockOperandMPtr_writeValue (arg : Veir.BlockArgumentPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_blockOperand readOwner!, BlockOperandMPtr.writeValue, arg, w2

/-! ## BlockArgumentMPtr.readType! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_regionMPtr_writeFirstBlock (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_region readType!, RegionMPtr.writeFirstBlock, arg, w2

/-! ## BlockArgumentMPtr.readType! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_regionMPtr_writeLastBlock (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_region readType!, RegionMPtr.writeLastBlock, arg, w2

/-! ## BlockArgumentMPtr.readType! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_regionMPtr_writeParent (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  rw_ba_region readType!, RegionMPtr.writeParent, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_regionMPtr_writeFirstBlock (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_region readFirstUse!, RegionMPtr.writeFirstBlock, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_regionMPtr_writeLastBlock (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_region readFirstUse!, RegionMPtr.writeLastBlock, arg, w2

/-! ## BlockArgumentMPtr.readFirstUse! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_regionMPtr_writeParent (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  rw_ba_region readFirstUse!, RegionMPtr.writeParent, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_regionMPtr_writeFirstBlock (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_region readIndex!, RegionMPtr.writeFirstBlock, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_regionMPtr_writeLastBlock (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_region readIndex!, RegionMPtr.writeLastBlock, arg, w2

/-! ## BlockArgumentMPtr.readIndex! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_regionMPtr_writeParent (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  rw_ba_region readIndex!, RegionMPtr.writeParent, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_regionMPtr_writeFirstBlock (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_region readOwner!, RegionMPtr.writeFirstBlock, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_regionMPtr_writeLastBlock (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_region readOwner!, RegionMPtr.writeLastBlock, arg, w2

/-! ## BlockArgumentMPtr.readOwner! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_regionMPtr_writeParent (arg : Veir.BlockArgumentPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (argIb : arg.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  rw_ba_region readOwner!, RegionMPtr.writeParent, arg, w2

/-! ## BlockArgumentMPtr.readType! after ValueImplMPtr.writeType -/

@[layout_grind =]
theorem BlockArgumentMPtr.readType!_valueImplMPtr_writeType (arg : Veir.BlockArgumentPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) arg.toM =
    if vptr.spec = .blockArgument arg then val
    else Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
    have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    by_cases vptr.spec = .blockArgument arg
    ·
      grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind,
          BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
          BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
          ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]
    · have : arg ≠ arg2 := by grind
      grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind,
          BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
          BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
          ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readFirstUse! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_valueImplMPtr_writeType (arg : Veir.BlockArgumentPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
    have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readIndex! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_valueImplMPtr_writeType (arg : Veir.BlockArgumentPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readIndex!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
    have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readIndex!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readOwner! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_valueImplMPtr_writeType (arg : Veir.BlockArgumentPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
    have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readType! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_valueImplMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
    have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readType!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readFirstUse! after ValueImplMPtr.writeFirstUse -/

@[layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_valueImplMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) arg.toM =
    if vptr.spec = .blockArgument arg then val.impl
    else Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
    have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    by_cases vptr.spec = .blockArgument arg
    ·
      grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind,
          BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
          BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
          ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]
    · have : arg ≠ arg2 := by grind
      grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind,
          BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
          BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
          ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readIndex! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_valueImplMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readIndex!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
    have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readIndex!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readOwner! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_valueImplMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
    have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readType! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_blockOperandPtrMPtr_write (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  rcases hcase : ptr.spec with bo | bl
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block arg.block) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl) (.block arg.block) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readType!, BlockOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      BlockPtr.range, BlockPtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readFirstUse! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_blockOperandPtrMPtr_write (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  rcases hcase : ptr.spec with bo | bl
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block arg.block) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl) (.block arg.block) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      BlockPtr.range, BlockPtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readIndex! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_blockOperandPtrMPtr_write (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  rcases hcase : ptr.spec with bo | bl
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block arg.block) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readIndex!, BlockOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl) (.block arg.block) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readIndex!, BlockOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      BlockPtr.range, BlockPtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readOwner! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_blockOperandPtrMPtr_write (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  rcases hcase : ptr.spec with bo | bl
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block arg.block) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readOwner!, BlockOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl) (.block arg.block) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readOwner!, BlockOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      BlockPtr.range, BlockPtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readType! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readType!_opOperandPtrMPtr_write (arg : Veir.BlockArgumentPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readType! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readType! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg2
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
      have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
      have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
      grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readFirstUse! after OpOperandPtrMPtr.write -/

@[layout_grind =]
theorem BlockArgumentMPtr.readFirstUse!_opOperandPtrMPtr_write (arg : Veir.BlockArgumentPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readFirstUse! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) arg.toM =
    if ptr.spec = .valueFirstUse (.blockArgument arg) then val.impl
    else Buffed.BlockArgumentMPtr.readFirstUse! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg2
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
      have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
      have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
      by_cases ptr.spec = .valueFirstUse (.blockArgument arg)
      ·
        grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
            BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
            BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
            ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]
      · have : arg ≠ arg2 := by grind
        grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
            BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
            BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
            ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readIndex! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readIndex!_opOperandPtrMPtr_write (arg : Veir.BlockArgumentPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readIndex! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readIndex! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readIndex!, OpOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg2
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readIndex!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
      have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
      have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
      grind (splits := 20) [readIndex!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readOwner! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readOwner!_opOperandPtrMPtr_write (arg : Veir.BlockArgumentPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readOwner! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readOwner! ctx.buf arg.toM := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
  have : arg.index < (arg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block arg.block) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg2
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
      have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
      have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
      grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
