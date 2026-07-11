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

/-! ## BlockMPtr.readFirstUse! -/

@[layout_grind =]
theorem BlockMPtr.readFirstUse!_blockMPtr_writeFirstUse (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) bl.toM =
    if bl = ptr.spec then val.impl else Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  grind (splits := 20) [readFirstUse!, writeFirstUse, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockMPtr_writePrev (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockMPtr.writePrev ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  grind (splits := 20) [readFirstUse!, writePrev, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockMPtr_writeNext (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockMPtr.writeNext ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  grind (splits := 20) [readFirstUse!, writeNext, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockMPtr_writeParent (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockMPtr.writeParent ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  grind (splits := 20) [readFirstUse!, writeParent, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockMPtr_writeFirstOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockMPtr.writeFirstOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  grind (splits := 20) [readFirstUse!, writeFirstOp, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockMPtr_writeLastOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockMPtr.writeLastOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  grind (splits := 20) [readFirstUse!, writeLastOp, layout_grind, BlockPtr.range]

/-! ## BlockMPtr.readPrev! -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockMPtr_writeFirstUse (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeFirstUse, layout_grind, BlockPtr.range]

@[layout_grind =]
theorem BlockMPtr.readPrev!_blockMPtr_writePrev (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockMPtr.writePrev ctx.buf ptr.impl val.impl h) bl.toM =
    if bl = ptr.spec then val.impl else Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  grind (splits := 20) [readPrev!, writePrev, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockMPtr_writeNext (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockMPtr.writeNext ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeNext, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockMPtr_writeParent (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockMPtr.writeParent ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeParent, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockMPtr_writeFirstOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockMPtr.writeFirstOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeFirstOp, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockMPtr_writeLastOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockMPtr.writeLastOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeLastOp, layout_grind, BlockPtr.range]

/-! ## BlockMPtr.readNext! -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockMPtr_writeFirstUse (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  grind (splits := 20) [readNext!, writeFirstUse, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockMPtr_writePrev (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockMPtr.writePrev ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  grind (splits := 20) [readNext!, writePrev, layout_grind, BlockPtr.range]

@[layout_grind =]
theorem BlockMPtr.readNext!_blockMPtr_writeNext (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockMPtr.writeNext ctx.buf ptr.impl val.impl h) bl.toM =
    if bl = ptr.spec then val.impl else Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  grind (splits := 20) [readNext!, writeNext, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockMPtr_writeParent (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockMPtr.writeParent ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  grind (splits := 20) [readNext!, writeParent, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockMPtr_writeFirstOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockMPtr.writeFirstOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  grind (splits := 20) [readNext!, writeFirstOp, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockMPtr_writeLastOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockMPtr.writeLastOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  grind (splits := 20) [readNext!, writeLastOp, layout_grind, BlockPtr.range]

/-! ## BlockMPtr.readParent! -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockMPtr_writeFirstUse (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  grind (splits := 20) [readParent!, writeFirstUse, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockMPtr_writePrev (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockMPtr.writePrev ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  grind (splits := 20) [readParent!, writePrev, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockMPtr_writeNext (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockMPtr.writeNext ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  grind (splits := 20) [readParent!, writeNext, layout_grind, BlockPtr.range]

@[layout_grind =]
theorem BlockMPtr.readParent!_blockMPtr_writeParent (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockMPtr.writeParent ctx.buf ptr.impl val.impl h) bl.toM =
    if bl = ptr.spec then val.impl else Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  grind (splits := 20) [readParent!, writeParent, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockMPtr_writeFirstOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockMPtr.writeFirstOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  grind (splits := 20) [readParent!, writeFirstOp, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockMPtr_writeLastOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockMPtr.writeLastOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  grind (splits := 20) [readParent!, writeLastOp, layout_grind, BlockPtr.range]

/-! ## BlockMPtr.readFirstOp! -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockMPtr_writeFirstUse (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  grind (splits := 20) [readFirstOp!, writeFirstUse, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockMPtr_writePrev (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockMPtr.writePrev ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  grind (splits := 20) [readFirstOp!, writePrev, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockMPtr_writeNext (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockMPtr.writeNext ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  grind (splits := 20) [readFirstOp!, writeNext, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockMPtr_writeParent (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockMPtr.writeParent ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  grind (splits := 20) [readFirstOp!, writeParent, layout_grind, BlockPtr.range]

@[layout_grind =]
theorem BlockMPtr.readFirstOp!_blockMPtr_writeFirstOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockMPtr.writeFirstOp ctx.buf ptr.impl val.impl h) bl.toM =
    if bl = ptr.spec then val.impl else Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  grind (splits := 20) [readFirstOp!, writeFirstOp, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockMPtr_writeLastOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockMPtr.writeLastOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  grind (splits := 20) [readFirstOp!, writeLastOp, layout_grind, BlockPtr.range]

/-! ## BlockMPtr.readLastOp! -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockMPtr_writeFirstUse (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  grind (splits := 20) [readLastOp!, writeFirstUse, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockMPtr_writePrev (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockMPtr.writePrev ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  grind (splits := 20) [readLastOp!, writePrev, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockMPtr_writeNext (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockMPtr.writeNext ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  grind (splits := 20) [readLastOp!, writeNext, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockMPtr_writeParent (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockMPtr.writeParent ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  grind (splits := 20) [readLastOp!, writeParent, layout_grind, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockMPtr_writeFirstOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockMPtr.writeFirstOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  grind (splits := 20) [readLastOp!, writeFirstOp, layout_grind, BlockPtr.range]

@[layout_grind =]
theorem BlockMPtr.readLastOp!_blockMPtr_writeLastOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockMPtr.writeLastOp ctx.buf ptr.impl val.impl h) bl.toM =
    if bl = ptr.spec then val.impl else Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  grind (splits := 20) [readLastOp!, writeLastOp, layout_grind, BlockPtr.range]

/-! ## BlockMPtr.readFirstUse! after BlockOperandPtrMPtr.write -/

@[layout_grind =]
theorem BlockMPtr.readFirstUse!_blockOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    if ptr.spec = .blockFirstUse bl then val.impl
    else Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with bo | bl2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block bl) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    by_cases ptr.spec = .blockFirstUse bl
    ·
      grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind,
        BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]
    · have : bl ≠ bl2 := by grind
      grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind,
        BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readPrev! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with bo | bl2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block bl) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readPrev!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readPrev!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readNext! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.next
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with bo | bl2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block bl) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readNext!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readNext!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readParent! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with bo | bl2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block bl) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readParent!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readParent!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readFirstOp! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with bo | bl2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block bl) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readFirstOp!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readFirstOp!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readLastOp! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with bo | bl2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block bl) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readLastOp!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readLastOp!, BlockOperandPtrMPtr.write, layout_grind,
      BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
