module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs
import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.Sim
import all Veir.IR.Buffed.SimDefs

public section

namespace Veir.Buffed

section read_write

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] {ctx : Sim.IRContext OpInfo}

/-! ## OperationMPtr.readNumResults! -/

@[layout_grind =]
theorem OperationMPtr.readNumResults!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM =
    if op = ptr.spec then val else Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeAttrs, layout_grind]


/-! ## OperationMPtr.readPrev! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeNumResults, layout_grind]

@[layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (prev : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl prev.impl h) op.toM =
    if op = ptr.spec then prev.impl else Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  grind (splits := 20) [readPrev!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (next : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl next.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeAttrs, layout_grind]


/-! ## OperationMPtr.readNext! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  grind (splits := 20) [readNext!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  grind (splits := 20) [readNext!, writePrev, layout_grind]

@[layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    if op = ptr.spec then val.impl else Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  grind (splits := 20) [readNext!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  grind (splits := 20) [readNext!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  grind (splits := 20) [readNext!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  grind (splits := 20) [readNext!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  grind (splits := 20) [readNext!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  grind (splits := 20) [readNext!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  grind (splits := 20) [readNext!, writeAttrs, layout_grind]


/-! ## OperationMPtr.readParent! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  grind (splits := 20) [readParent!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  grind (splits := 20) [readParent!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  grind (splits := 20) [readParent!, writeNext, layout_grind]

@[layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    if op = ptr.spec then val.impl else Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  grind (splits := 20) [readParent!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  grind (splits := 20) [readParent!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  grind (splits := 20) [readParent!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  grind (splits := 20) [readParent!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  grind (splits := 20) [readParent!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  grind (splits := 20) [readParent!, writeAttrs, layout_grind]


/-! ## OperationMPtr.readOpType! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, writeParent, layout_grind]

@[layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM =
    if op = ptr.spec then val else Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, writeAttrs, layout_grind]


/-! ## OperationMPtr.readNumBlockOperands! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  grind (splits := 20) [readNumBlockOperands!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  grind (splits := 20) [readNumBlockOperands!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  grind (splits := 20) [readNumBlockOperands!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  grind (splits := 20) [readNumBlockOperands!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  grind (splits := 20) [readNumBlockOperands!, writeOpType, layout_grind]

@[layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM =
    if op = ptr.spec then val else Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  grind (splits := 20) [readNumBlockOperands!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  grind (splits := 20) [readNumBlockOperands!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  grind (splits := 20) [readNumBlockOperands!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  grind (splits := 20) [readNumBlockOperands!, writeAttrs, layout_grind]


/-! ## OperationMPtr.readNumRegions! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  grind (splits := 20) [readNumRegions!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  grind (splits := 20) [readNumRegions!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  grind (splits := 20) [readNumRegions!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  grind (splits := 20) [readNumRegions!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  grind (splits := 20) [readNumRegions!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  grind (splits := 20) [readNumRegions!, writeNumBlockOperands, layout_grind]

@[layout_grind =]
theorem OperationMPtr.readNumRegions!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM =
    if op = ptr.spec then val else Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  grind (splits := 20) [readNumRegions!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  grind (splits := 20) [readNumRegions!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  grind (splits := 20) [readNumRegions!, writeAttrs, layout_grind]


/-! ## OperationMPtr.readNumOperands! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  grind (splits := 20) [readNumOperands!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  grind (splits := 20) [readNumOperands!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  grind (splits := 20) [readNumOperands!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  grind (splits := 20) [readNumOperands!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  grind (splits := 20) [readNumOperands!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  grind (splits := 20) [readNumOperands!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  grind (splits := 20) [readNumOperands!, writeNumRegions, layout_grind]

@[layout_grind =]
theorem OperationMPtr.readNumOperands!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM =
    if op = ptr.spec then val else Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  grind (splits := 20) [readNumOperands!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  grind (splits := 20) [readNumOperands!, writeAttrs, layout_grind]


/-! ## OperationMPtr.readAttrs! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  grind (splits := 20) [readAttrs!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  grind (splits := 20) [readAttrs!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  grind (splits := 20) [readAttrs!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  grind (splits := 20) [readAttrs!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  grind (splits := 20) [readAttrs!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  grind (splits := 20) [readAttrs!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  grind (splits := 20) [readAttrs!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  grind (splits := 20) [readAttrs!, writeNumOperands, layout_grind]

@[layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM =
    if op = ptr.spec then val else Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  grind (splits := 20) [readAttrs!, writeAttrs, layout_grind]

/-! ## OperationMPtr.readNthResult! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeAttrs, layout_grind]


/-! ## OperationMPtr.readNthBlockOperand! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readOpType!, readNumOperands!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readOpType!, readNumOperands!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readOpType!, readNumOperands!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readOpType!, readNumOperands!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readOpType!, readNumOperands!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readOpType!, readNumOperands!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readOpType!, readNumOperands!, writeAttrs, layout_grind]

/-! ## OperationMPtr.readNthResult! against all remaining writers -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_operationMPtr_writeNumResults (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64) (hne : op ≠ ptr.spec)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  grind (splits := 20) [readNumResults!, writeNumResults, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr) (idx : UInt64)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumResults!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumResults!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumResults!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumResults!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr) (idx : UInt64)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumResults!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumResults!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr) (idx : UInt64)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readNumResults!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readNumResults!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNumResults!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNthBlockOperand! against all remaining writers -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64) (hne : op ≠ ptr.spec)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, readNumOperands!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64) (hne : op ≠ ptr.spec)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  grind (splits := 20) [readOpType!, readNumOperands!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, readNumOperands!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr) (idx : UInt64)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readOpType!, readNumOperands!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readOpType!, readNumOperands!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readOpType!, readNumOperands!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOpType!, readNumOperands!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr) (idx : UInt64)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readOpType!, readNumOperands!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOpType!, readNumOperands!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr) (idx : UInt64)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readOpType!, readNumOperands!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readOpType!, readNumOperands!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readOpType!, readNumOperands!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr) (idx : UInt64)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthBlockOperand!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthBlockOperand! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthBlockOperand! ctx.buf op.toM idx := by
  simp only [readNthBlockOperand!, computeBlockOperandOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, readNumOperands!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! OperationMPtr.readNthRegion! against all remaining writers -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, writePrev, layout_grind]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, writePrev, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, writeNext, layout_grind]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, writeNext, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, writeParent, layout_grind]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, writeParent, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_operationMPtr_writeNumBlockOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (hne : op ≠ ptr.spec)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OperationMPtr.writeNumBlockOperands ctx.buf ptr.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, writeNumBlockOperands, layout_grind]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, writeNumBlockOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_operationMPtr_writeNumRegions (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OperationMPtr.writeNumRegions ctx.buf ptr.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, writeNumRegions, layout_grind]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, writeNumRegions, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_operationMPtr_writeAttrs (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OperationMPtr.writeAttrs ctx.buf ptr.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, writeAttrs, layout_grind]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, writeAttrs, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_operationMPtr_writeOpType (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64) (hne : op ≠ ptr.spec)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (_hne : op ≠ ptr.spec)
    (val : UInt32) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OperationMPtr.writeOpType ctx.buf ptr.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, writeOpType, layout_grind]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, writeOpType, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_operationMPtr_writeNumOperands (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64) (hne : op ≠ ptr.spec)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (_hne : op ≠ ptr.spec)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OperationMPtr.writeNumOperands ctx.buf ptr.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, writeNumOperands, layout_grind]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, writeNumOperands, layout_grind]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpOperandMPtr.writeNextUse, layout_grind, OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat]
  rw [hoff]
  have hwbridge := Sim.OpOperandPtr.toFlat_eq_impl_toNat operIb
  have hwaddr := hincl
  simp only [OpOperandPtr.range, OpOperandPtr.toFlat, OperationPtr.range, Operation.range,
    OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
  have hwnat : (oper.impl + OpOperand.Offsets.nextUse).toNat
      = oper.impl.toNat + OpOperand.Offsets.nextUse.toInt.toNat := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hopidx := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.operands
  have hopcap := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.capOperands
  have hidxlt : oper.spec.index < oper.spec.op.getNumOperands! ctx.spec := by
    have := (OpOperandPtr.inBounds_def (opr := oper.spec) (ctx := ctx.spec)).mp operIb.ib
    grind
  have hdisj : IsDisjoint
      ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
        ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
      ((oper.impl + OpOperand.Offsets.nextUse).toNat
        ...((oper.impl + OpOperand.Offsets.nextUse).toNat + 8)) := by
    simp only [IsDisjoint]
    rw [hwnat, ← hwbridge]
    simp only [OpOperandPtr.toFlat, OperationPtr.toFlat]
    grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
  simp only [OpOperandMPtr.writeNextUse]
  exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpOperandMPtr.writeBack, layout_grind, OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat]
  rw [hoff]
  have hwbridge := Sim.OpOperandPtr.toFlat_eq_impl_toNat operIb
  have hwaddr := hincl
  simp only [OpOperandPtr.range, OpOperandPtr.toFlat, OperationPtr.range, Operation.range,
    OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
  have himpllt : (oper.impl.toNat : Int) < Int64.maxValue.toInt := by
    have := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper.spec operIb.ib
    rw [OpOperandPtr.toFlat_ideal (by grind) _ (by grind)] at this
    grind [layout_grind]
  have hwnat : (oper.impl + OpOperand.Offsets.back).toNat
      = oper.impl.toNat + OpOperand.Offsets.back.toInt.toNat := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hopidx := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.operands
  have hopcap := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.capOperands
  have hidxlt : oper.spec.index < oper.spec.op.getNumOperands! ctx.spec := by
    have := (OpOperandPtr.inBounds_def (opr := oper.spec) (ctx := ctx.spec)).mp operIb.ib
    grind
  have hdisj : IsDisjoint
      ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
        ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
      ((oper.impl + OpOperand.Offsets.back).toNat
        ...((oper.impl + OpOperand.Offsets.back).toNat + 8)) := by
    simp only [IsDisjoint]
    rw [hwnat, ← hwbridge]
    simp only [OpOperandPtr.toFlat, OperationPtr.toFlat]
    grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
  simp only [OpOperandMPtr.writeBack]
  exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpOperandMPtr.writeOwner, layout_grind, OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat]
  rw [hoff]
  have hwbridge := Sim.OpOperandPtr.toFlat_eq_impl_toNat operIb
  have hwaddr := hincl
  simp only [OpOperandPtr.range, OpOperandPtr.toFlat, OperationPtr.range, Operation.range,
    OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
  have himpllt : (oper.impl.toNat : Int) < Int64.maxValue.toInt := by
    have := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper.spec operIb.ib
    rw [OpOperandPtr.toFlat_ideal (by grind) _ (by grind)] at this
    grind [layout_grind]
  have hwnat : (oper.impl + OpOperand.Offsets.owner).toNat
      = oper.impl.toNat + OpOperand.Offsets.owner.toInt.toNat := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hopidx := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.operands
  have hopcap := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.capOperands
  have hidxlt : oper.spec.index < oper.spec.op.getNumOperands! ctx.spec := by
    have := (OpOperandPtr.inBounds_def (opr := oper.spec) (ctx := ctx.spec)).mp operIb.ib
    grind
  have hdisj : IsDisjoint
      ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
        ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
      ((oper.impl + OpOperand.Offsets.owner).toNat
        ...((oper.impl + OpOperand.Offsets.owner).toNat + 8)) := by
    simp only [IsDisjoint]
    rw [hwnat, ← hwbridge]
    simp only [OpOperandPtr.toFlat, OperationPtr.toFlat]
    grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
  simp only [OpOperandMPtr.writeOwner]
  exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpOperandMPtr.writeValue, layout_grind, OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat]
  rw [hoff]
  have hwbridge := Sim.OpOperandPtr.toFlat_eq_impl_toNat operIb
  have hwaddr := hincl
  simp only [OpOperandPtr.range, OpOperandPtr.toFlat, OperationPtr.range, Operation.range,
    OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
  have himpllt : (oper.impl.toNat : Int) < Int64.maxValue.toInt := by
    have := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper.spec operIb.ib
    rw [OpOperandPtr.toFlat_ideal (by grind) _ (by grind)] at this
    grind [layout_grind]
  have hwnat : (oper.impl + OpOperand.Offsets.value).toNat
      = oper.impl.toNat + OpOperand.Offsets.value.toInt.toNat := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hopidx := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.operands
  have hopcap := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.capOperands
  have hidxlt : oper.spec.index < oper.spec.op.getNumOperands! ctx.spec := by
    have := (OpOperandPtr.inBounds_def (opr := oper.spec) (ctx := ctx.spec)).mp operIb.ib
    grind
  have hdisj : IsDisjoint
      ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
        ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
      ((oper.impl + OpOperand.Offsets.value).toNat
        ...((oper.impl + OpOperand.Offsets.value).toNat + 8)) := by
    simp only [IsDisjoint]
    rw [hwnat, ← hwbridge]
    simp only [OpOperandPtr.toFlat, OperationPtr.toFlat]
    grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
  simp only [OpOperandMPtr.writeValue]
  exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockOperandMPtr.writeNextUse, layout_grind, BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat]
  rw [hoff]
  have hwbridge := Sim.BlockOperandPtr.toFlat_eq_impl_toNat operIb
  have hwaddr := hincl
  simp only [BlockOperandPtr.range, BlockOperandPtr.toFlat, OperationPtr.range, Operation.range,
    OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
  have himpllt : (oper.impl.toNat : Int) < Int64.maxValue.toInt := by
    have := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) oper.spec operIb.ib
    rw [BlockOperandPtr.toFlat_ideal (by grind) _ (by grind)] at this
    grind [layout_grind]
  have hwnat : (oper.impl + BlockOperand.Offsets.nextUse).toNat
      = oper.impl.toNat + BlockOperand.Offsets.nextUse.toInt.toNat := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hopidx := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.blockOperands
  have hopcap := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.capBlockOperands
  have hidxlt : oper.spec.index < oper.spec.op.getNumSuccessors! ctx.spec := by
    have := (BlockOperandPtr.inBounds_def (opr := oper.spec) (ctx := ctx.spec)).mp operIb.ib
    grind
  have hdisj : IsDisjoint
      ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
        ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
      ((oper.impl + BlockOperand.Offsets.nextUse).toNat
        ...((oper.impl + BlockOperand.Offsets.nextUse).toNat + 8)) := by
    simp only [IsDisjoint]
    rw [hwnat, ← hwbridge]
    simp only [BlockOperandPtr.toFlat, OperationPtr.toFlat]
    grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
  simp only [BlockOperandMPtr.writeNextUse]
  exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockOperandMPtr.writeBack, layout_grind, BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat]
  rw [hoff]
  have hwbridge := Sim.BlockOperandPtr.toFlat_eq_impl_toNat operIb
  have hwaddr := hincl
  simp only [BlockOperandPtr.range, BlockOperandPtr.toFlat, OperationPtr.range, Operation.range,
    OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
  have himpllt : (oper.impl.toNat : Int) < Int64.maxValue.toInt := by
    have := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) oper.spec operIb.ib
    rw [BlockOperandPtr.toFlat_ideal (by grind) _ (by grind)] at this
    grind [layout_grind]
  have hwnat : (oper.impl + BlockOperand.Offsets.back).toNat
      = oper.impl.toNat + BlockOperand.Offsets.back.toInt.toNat := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hopidx := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.blockOperands
  have hopcap := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.capBlockOperands
  have hidxlt : oper.spec.index < oper.spec.op.getNumSuccessors! ctx.spec := by
    have := (BlockOperandPtr.inBounds_def (opr := oper.spec) (ctx := ctx.spec)).mp operIb.ib
    grind
  have hdisj : IsDisjoint
      ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
        ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
      ((oper.impl + BlockOperand.Offsets.back).toNat
        ...((oper.impl + BlockOperand.Offsets.back).toNat + 8)) := by
    simp only [IsDisjoint]
    rw [hwnat, ← hwbridge]
    simp only [BlockOperandPtr.toFlat, OperationPtr.toFlat]
    grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
  simp only [BlockOperandMPtr.writeBack]
  exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockOperandMPtr.writeOwner, layout_grind, BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat]
  rw [hoff]
  have hwbridge := Sim.BlockOperandPtr.toFlat_eq_impl_toNat operIb
  have hwaddr := hincl
  simp only [BlockOperandPtr.range, BlockOperandPtr.toFlat, OperationPtr.range, Operation.range,
    OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
  have himpllt : (oper.impl.toNat : Int) < Int64.maxValue.toInt := by
    have := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) oper.spec operIb.ib
    rw [BlockOperandPtr.toFlat_ideal (by grind) _ (by grind)] at this
    grind [layout_grind]
  have hwnat : (oper.impl + BlockOperand.Offsets.owner).toNat
      = oper.impl.toNat + BlockOperand.Offsets.owner.toInt.toNat := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hopidx := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.blockOperands
  have hopcap := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.capBlockOperands
  have hidxlt : oper.spec.index < oper.spec.op.getNumSuccessors! ctx.spec := by
    have := (BlockOperandPtr.inBounds_def (opr := oper.spec) (ctx := ctx.spec)).mp operIb.ib
    grind
  have hdisj : IsDisjoint
      ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
        ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
      ((oper.impl + BlockOperand.Offsets.owner).toNat
        ...((oper.impl + BlockOperand.Offsets.owner).toNat + 8)) := by
    simp only [IsDisjoint]
    rw [hwnat, ← hwbridge]
    simp only [BlockOperandPtr.toFlat, OperationPtr.toFlat]
    grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
  simp only [BlockOperandMPtr.writeOwner]
  exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockOperandMPtr.writeValue, layout_grind, BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat]
  rw [hoff]
  have hwbridge := Sim.BlockOperandPtr.toFlat_eq_impl_toNat operIb
  have hwaddr := hincl
  simp only [BlockOperandPtr.range, BlockOperandPtr.toFlat, OperationPtr.range, Operation.range,
    OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
  have himpllt : (oper.impl.toNat : Int) < Int64.maxValue.toInt := by
    have := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) oper.spec operIb.ib
    rw [BlockOperandPtr.toFlat_ideal (by grind) _ (by grind)] at this
    grind [layout_grind]
  have hwnat : (oper.impl + BlockOperand.Offsets.value).toNat
      = oper.impl.toNat + BlockOperand.Offsets.value.toInt.toNat := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hopidx := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.blockOperands
  have hopcap := ctx.sim.repr.operations_indices oper.spec.op (by grind) |>.capBlockOperands
  have hidxlt : oper.spec.index < oper.spec.op.getNumSuccessors! ctx.spec := by
    have := (BlockOperandPtr.inBounds_def (opr := oper.spec) (ctx := ctx.spec)).mp operIb.ib
    grind
  have hdisj : IsDisjoint
      ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
        ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
      ((oper.impl + BlockOperand.Offsets.value).toNat
        ...((oper.impl + BlockOperand.Offsets.value).toNat + 8)) := by
    simp only [IsDisjoint]
    rw [hwnat, ← hwbridge]
    simp only [BlockOperandPtr.toFlat, OperationPtr.toFlat]
    grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
  simp only [BlockOperandMPtr.writeValue]
  exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OpResultMPtr.writeType ctx.buf res.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpResultMPtr.writeType, layout_grind, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpResultMPtr.writeFirstUse, layout_grind, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpResultMPtr.writeIndex, layout_grind, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpResultMPtr.writeOwner, layout_grind, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    have hoff : (OperationMPtr.computeRegionsOffset! (BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM)
        = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
      simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
      grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockOperandPtrMPtr.write, layout_grind, BlockOperandPtr.range, BlockOperandPtr.toFlat]
    rw [hoff]
    have hwaddr := hincl
    simp only [BlockOperandPtr.range, BlockOperandPtr.toFlat, OperationPtr.range, Operation.range,
      OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
    have hopidx := ctx.sim.repr.operations_indices bo.op (by grind) |>.blockOperands
    have hopcap := ctx.sim.repr.operations_indices bo.op (by grind) |>.capBlockOperands
    have hidxlt : bo.index < bo.op.getNumSuccessors! ctx.spec := by
      have := (BlockOperandPtr.inBounds_def (opr := bo) (ctx := ctx.spec)).mp (by grind)
      grind
    have hdisj2 : IsDisjoint
        ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
          ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
        (ptr.impl.toNat ...(ptr.impl.toNat + 8)) := by
      simp only [IsDisjoint]
      rw [← hbridge]
      simp only [BlockOperandPtr.toFlat, OperationPtr.toFlat]
      grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
    simp only [BlockOperandPtrMPtr.write]
    exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj2
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    have hoff : (OperationMPtr.computeRegionsOffset! (BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM)
        = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
      simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
      grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockOperandPtrMPtr.write, layout_grind, BlockPtr.range, BlockPtr.toFlat]
    rw [hoff]
    have hwaddr := hincl
    simp only [BlockPtr.rangeInt, BlockPtr.toFlat, add_nat_range_def] at hwaddr
    have hbin := ctx.sim.in_bounds (.block bl) (by grind)
    have hdisj2 : IsDisjoint
        ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
          ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
        (ptr.impl.toNat ...(ptr.impl.toNat + 8)) := by
      simp only [IsDisjoint]
      rw [← hbridge]
      grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind, OperationPtr.toFlat, BlockPtr.toFlat]
    simp only [BlockOperandPtrMPtr.write]
    exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj2

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hoff : (OperationMPtr.computeRegionsOffset! (ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM)
        = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
      simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
      grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, ValueImplMPtr.writeType, layout_grind, OpResultPtr.range, OpResultPtr.toFlat]
    rw [hoff]
    grind (splits := 20) [readOpType!, readNumOperands!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjoint]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    have hoff : (OperationMPtr.computeRegionsOffset! (ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM)
        = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
      simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
      grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, ValueImplMPtr.writeType, layout_grind, BlockArgumentPtr.range, BlockArgumentPtr.toFlat]
    rw [hoff]
    grind (splits := 20) [readOpType!, readNumOperands!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hoff : (OperationMPtr.computeRegionsOffset! (ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM)
        = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
      simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
      grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, ValueImplMPtr.writeFirstUse, layout_grind, OpResultPtr.range, OpResultPtr.toFlat]
    rw [hoff]
    grind (splits := 20) [readOpType!, readNumOperands!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjoint]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    have hoff : (OperationMPtr.computeRegionsOffset! (ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM)
        = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
      simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
      grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, ValueImplMPtr.writeFirstUse, layout_grind, BlockArgumentPtr.range, BlockArgumentPtr.toFlat]
    rw [hoff]
    grind (splits := 20) [readOpType!, readNumOperands!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    simp only [hcase, OpOperandPtrPtr.toFlat, layout_simp] at hbridge
    have hoff : (OperationMPtr.computeRegionsOffset! (OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM)
        = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
      simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
      grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpOperandPtrMPtr.write, layout_grind, OpOperandPtr.range, OpOperandPtr.toFlat]
    rw [hoff]
    have hwaddr := hincl
    simp only [OpOperandPtr.range, OpOperandPtr.toFlat, OperationPtr.range, Operation.range,
      OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
    have hopidx := ctx.sim.repr.operations_indices opr.op (by grind) |>.operands
    have hopcap := ctx.sim.repr.operations_indices opr.op (by grind) |>.capOperands
    have hidxlt : opr.index < opr.op.getNumOperands! ctx.spec := by
      have := (OpOperandPtr.inBounds_def (opr := opr) (ctx := ctx.spec)).mp (by grind)
      grind
    have hdisj2 : IsDisjoint
        ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
          ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
        (ptr.impl.toNat ...(ptr.impl.toNat + 8)) := by
      simp only [IsDisjoint]
      rw [← hbridge]
      simp only [OpOperandPtr.toFlat, OperationPtr.toFlat]
      grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
    simp only [OpOperandPtrMPtr.write]
    exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj2
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      simp only [hcase, hvcase, OpOperandPtrPtr.toFlat, ValuePtr.toFlat, layout_simp] at hbridge
      have hoff : (OperationMPtr.computeRegionsOffset! (OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM)
          = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
        simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
        grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpOperandPtrMPtr.write, layout_grind, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat]
      rw [hoff]
      have hwaddr := hincl
      simp only [OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.range, Operation.range,
        OperationPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
      have hopidx := ctx.sim.repr.operations_indices res.op (by grind) |>.results
      have hopcap := ctx.sim.repr.operations_indices res.op (by grind) |>.capResults
      have hidxlt : res.index < res.op.getNumResults! ctx.spec := by
        have := (OpResultPtr.inBounds_def (res := res) (ctx := ctx.spec)).mp (by grind)
        grind
      have hdisj2 : IsDisjoint
          ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
            ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
          (ptr.impl.toNat ...(ptr.impl.toNat + 8)) := by
        simp only [IsDisjoint]
        rw [← hbridge]
        simp only [OpResultPtr.toFlat, OperationPtr.toFlat]
        grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind]
      simp only [OpOperandPtrMPtr.write]
      exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj2
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      simp only [hcase, hvcase, OpOperandPtrPtr.toFlat, ValuePtr.toFlat, layout_simp] at hbridge
      have hoff : (OperationMPtr.computeRegionsOffset! (OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM)
          = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
        simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
        grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, OpOperandPtrMPtr.write, layout_grind, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat]
      rw [hoff]
      have hwaddr := hincl
      simp only [BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, Block.range,
        BlockPtr.toFlat, add_nat_range_def, IsIncludedI] at hwaddr
      have hdisj2 : IsDisjoint
          ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat
            ...((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat + 8))
          (ptr.impl.toNat ...(ptr.impl.toNat + 8)) := by
        simp only [IsDisjoint]
        rw [← hbridge]
        grind (splits := 30) [IsDisjointI, IsIncludedI, layout_grind, OperationPtr.toFlat, BlockPtr.toFlat, BlockArgumentPtr.toFlat]
      simp only [OpOperandPtrMPtr.write]
      exact ExArray.read64!_blit64_disjoint _ _ _ _ _ hdisj2

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hraddr : ((op.toM + (OperationMPtr.computeRegionsOffset! ctx.buf op.toM + ptrSize * idx)).toNat : Int)
      = op.toM.toNat + (Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockMPtr.writeFirstUse, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockMPtr.writePrev, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockMPtr.writeNext, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockMPtr.writeParent, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockMPtr.writeFirstOp, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockMPtr.writeLastOp, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockMPtr.writeNumArguments, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, RegionMPtr.writeFirstBlock, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, RegionMPtr.writeLastBlock, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, RegionMPtr.writeParent, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockArgumentMPtr.writeType, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockArgumentMPtr.writeFirstUse, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockArgumentMPtr.writeIndex, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjoint]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have hopin := ctx.sim.in_bounds (.operation op) (by grind)
  have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op idx hidx opIb
  simp only [OperationPtr.rangeInt, Operation.rangeInt, OperationPtr.toFlat, add_nat_range_def,
    IsIncludedI] at hincl2
  have hoff : (OperationMPtr.computeRegionsOffset! (BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, BlockArgumentMPtr.writeOwner, layout_grind, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat]
  rw [hoff]
  grind (splits := 20) [readOpType!, readNumOperands!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjoint]


/-! ## OperationMPtr.readNumResults! after OpOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readPrev! after OpOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNext! after OpOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNext!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNext!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNext!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNext!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readParent! after OpOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readParent!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readParent!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readParent!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readParent!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readOpType! after OpOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNumBlockOperands! after OpOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNumRegions! after OpOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNumOperands! after OpOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readAttrs! after OpOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_opOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OpOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, OpOperandMPtr.writeNextUse, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_opOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OpOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, OpOperandMPtr.writeBack, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_opOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OpOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, OpOperandMPtr.writeOwner, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_opOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.OpOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OpOperandMPtr.writeValue ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := OpOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.OpOperandPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, OpOperandMPtr.writeValue, layout_grind,
    OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncluded]

/-! ## OperationMPtr.readNumResults! after BlockOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readPrev! after BlockOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNext! after BlockOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNext!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNext!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNext!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNext!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readParent! after BlockOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readParent!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readParent!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readParent!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readParent!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readOpType! after BlockOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNumBlockOperands! after BlockOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNumRegions! after BlockOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNumOperands! after BlockOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readAttrs! after BlockOperandMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockOperandMPtr_writeNextUse (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, BlockOperandMPtr.writeNextUse, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockOperandMPtr_writeBack (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockOperandMPtr.writeBack ctx.buf oper.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, BlockOperandMPtr.writeBack, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockOperandMPtr_writeOwner (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockOperandMPtr.writeOwner ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, BlockOperandMPtr.writeOwner, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockOperandMPtr_writeValue (op : Veir.OperationPtr) (oper : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (operIb : oper.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockOperandMPtr.writeValue ctx.buf oper.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation oper.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := BlockOperandPtr.range_included_op_range (by grind) oper.spec operIb.ib
  have hsim := operIb.sim
  simp only [Sim.BlockOperandPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, BlockOperandMPtr.writeValue, layout_grind,
    BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncluded]

/-! ## OperationMPtr.readNumResults! after OpResultMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumResults!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readPrev! after OpResultMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNext! after OpResultMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNext!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNext!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNext!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNext!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readParent! after OpResultMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readParent!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readParent!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readParent!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readParent!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readOpType! after OpResultMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readOpType!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNumBlockOperands! after OpResultMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumBlockOperands!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNumRegions! after OpResultMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumRegions!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readNumOperands! after OpResultMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readNumOperands!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]


/-! ## OperationMPtr.readAttrs! after OpResultMPtr writes -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_opResultMPtr_writeType (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OpResultMPtr.writeType ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, OpResultMPtr.writeType, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_opResultMPtr_writeFirstUse (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, OpResultMPtr.writeFirstUse, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_opResultMPtr_writeIndex (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OpResultMPtr.writeIndex ctx.buf res.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, OpResultMPtr.writeIndex, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_opResultMPtr_writeOwner (op : Veir.OperationPtr) (res : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (opIb : op.InBounds ctx.spec) (resIb : res.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OpResultMPtr.writeOwner ctx.buf res.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have disj := ctx.sim.disjoint_allocs (.operation res.spec.op) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hincl := OpResultPtr.range_included_op_range res.spec resIb.ib
  have hsim := resIb.sim
  have := ctx.sim.in_bounds (.operation op) (by grind)
  simp only [Sim.OpResultPtr.Sim] at hsim
  grind (splits := 20) [readAttrs!, OpResultMPtr.writeOwner, layout_grind,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncluded]

/-! ## OperationMPtr.readNumResults! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumResults!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumResults!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readPrev!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readPrev!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNext!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNext!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readParent!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readParent!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readOpType!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readOpType!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumBlockOperands!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumBlockOperands!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumRegions!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumRegions!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumOperands!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readNumOperands!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readAttrs!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    simp only [hcase, BlockOperandPtrPtr.toFlat, layout_simp] at hbridge
    grind (splits := 20) [readAttrs!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after ValueImplMPtr.writeType (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumResults!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumResults!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after ValueImplMPtr.writeFirstUse (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumResults!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumResults!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after ValueImplMPtr.writeType (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readPrev!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readPrev!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after ValueImplMPtr.writeFirstUse (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readPrev!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readPrev!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after ValueImplMPtr.writeType (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNext!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNext!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after ValueImplMPtr.writeFirstUse (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNext!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNext!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after ValueImplMPtr.writeType (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readParent!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readParent!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after ValueImplMPtr.writeFirstUse (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readParent!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readParent!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after ValueImplMPtr.writeType (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readOpType!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOpType!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after ValueImplMPtr.writeFirstUse (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readOpType!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOpType!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after ValueImplMPtr.writeType (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumBlockOperands!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumBlockOperands!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after ValueImplMPtr.writeFirstUse (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumBlockOperands!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumBlockOperands!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after ValueImplMPtr.writeType (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumRegions!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumRegions!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after ValueImplMPtr.writeFirstUse (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumRegions!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumRegions!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after ValueImplMPtr.writeType (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumOperands!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumOperands!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after ValueImplMPtr.writeFirstUse (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readNumOperands!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumOperands!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after ValueImplMPtr.writeType (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_valueImplMPtr_writeType (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readAttrs!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readAttrs!, ValueImplMPtr.writeType, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after ValueImplMPtr.writeFirstUse (via ValuePtr) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_valueImplMPtr_writeFirstUse (op : Veir.OperationPtr) (ptr : Sim.ValuePtr)
    (val : OpOperandOPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    grind (splits := 20) [readAttrs!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readAttrs!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]


/-! ## OperationMPtr.readNumResults! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readNumResults!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readNumResults!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNumResults!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readPrev!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readPrev!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readPrev!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readNext!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readNext!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNext!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readParent!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readParent!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readParent!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readOpType!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readOpType!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readOpType!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readNumBlockOperands!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readNumBlockOperands!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNumBlockOperands!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readNumRegions!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readNumRegions!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNumRegions!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readNumOperands!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readNumOperands!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNumOperands!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_opOperandPtrMPtr_write (op : Veir.OperationPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    grind (splits := 20) [readAttrs!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      grind (splits := 20) [readAttrs!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readAttrs!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]


/-! ## OperationMPtr.readAttrs! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockMPtr_writePrev (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockMPtr.writePrev, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockMPtr_writeNext (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockMPtr_writeFirstOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockMPtr.writeFirstOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockMPtr_writeLastOp (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockMPtr.writeLastOp, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockMPtr_writeNumArguments (op : Veir.OperationPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockMPtr.writeNumArguments, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_regionMPtr_writeFirstBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, RegionMPtr.writeFirstBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_regionMPtr_writeLastBlock (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, RegionMPtr.writeLastBlock, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_regionMPtr_writeParent (op : Veir.OperationPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.region w2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.region w2.spec) (by grind) (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, RegionMPtr.writeParent, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readAttrs! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.attrs
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readAttrs!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNext! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.next
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNext!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumResults! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumResults!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumResults! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumResults! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumBlockOperands! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumBlockOperands!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumBlockOperands! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumRegions! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumRegions!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumRegions! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumRegions! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numRegions
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumRegions!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readNumOperands! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNumOperands!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNumOperands! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumOperands!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readOpType! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.opType
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readOpType!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readPrev! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.prev
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readPrev!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockArgumentMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockArgumentMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockArgumentMPtr_writeFirstUse (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockArgumentMPtr_writeIndex (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockArgumentMPtr.writeIndex, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OperationMPtr.readParent! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_blockArgumentMPtr_writeOwner (op : Veir.OperationPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.parent
  have hw := ctx.sim.in_bounds (.block w2.spec.block) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.block w2.spec.block) (by grind) (by grind)
  have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readParent!, BlockArgumentMPtr.writeOwner, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
