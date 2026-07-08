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
  grind (splits := 20) [readFirstUse!, writeFirstUse, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstUse!, writePrev, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstUse!, writeNext, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstUse!, writeParent, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstUse!, writeFirstOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstUse!, writeLastOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockMPtr_writeNumArguments (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockMPtr.writeNumArguments ctx.buf ptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  grind (splits := 20) [readFirstUse!, writeNumArguments, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]


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
  grind (splits := 20) [readPrev!, writeFirstUse, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readPrev!, writePrev, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readPrev!, writeNext, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readPrev!, writeParent, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readPrev!, writeFirstOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readPrev!, writeLastOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockMPtr_writeNumArguments (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockMPtr.writeNumArguments ctx.buf ptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  grind (splits := 20) [readPrev!, writeNumArguments, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]


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
  grind (splits := 20) [readNext!, writeFirstUse, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readNext!, writePrev, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readNext!, writeNext, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readNext!, writeParent, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readNext!, writeFirstOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readNext!, writeLastOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockMPtr_writeNumArguments (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockMPtr.writeNumArguments ctx.buf ptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  grind (splits := 20) [readNext!, writeNumArguments, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]


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
  grind (splits := 20) [readParent!, writeFirstUse, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readParent!, writePrev, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readParent!, writeNext, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readParent!, writeParent, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readParent!, writeFirstOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readParent!, writeLastOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockMPtr_writeNumArguments (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockMPtr.writeNumArguments ctx.buf ptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  grind (splits := 20) [readParent!, writeNumArguments, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]


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
  grind (splits := 20) [readFirstOp!, writeFirstUse, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstOp!, writePrev, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstOp!, writeNext, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstOp!, writeParent, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstOp!, writeFirstOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readFirstOp!, writeLastOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockMPtr_writeNumArguments (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockMPtr.writeNumArguments ctx.buf ptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  grind (splits := 20) [readFirstOp!, writeNumArguments, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]


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
  grind (splits := 20) [readLastOp!, writeFirstUse, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readLastOp!, writePrev, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readLastOp!, writeNext, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readLastOp!, writeParent, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readLastOp!, writeFirstOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

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
  grind (splits := 20) [readLastOp!, writeLastOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockMPtr_writeNumArguments (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockMPtr.writeNumArguments ctx.buf ptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  grind (splits := 20) [readLastOp!, writeNumArguments, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]


/-! ## BlockMPtr.readNumArguments! -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockMPtr_writeFirstUse (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  grind (splits := 20) [readNumArguments!, writeFirstUse, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockMPtr_writePrev (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockMPtr.writePrev ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  grind (splits := 20) [readNumArguments!, writePrev, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockMPtr_writeNext (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockMPtr.writeNext ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  grind (splits := 20) [readNumArguments!, writeNext, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockMPtr_writeParent (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockMPtr.writeParent ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  grind (splits := 20) [readNumArguments!, writeParent, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockMPtr_writeFirstOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockMPtr.writeFirstOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  grind (splits := 20) [readNumArguments!, writeFirstOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockMPtr_writeLastOp (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockMPtr.writeLastOp ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  grind (splits := 20) [readNumArguments!, writeLastOp, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

@[layout_grind =]
theorem BlockMPtr.readNumArguments!_blockMPtr_writeNumArguments (bl : Veir.BlockPtr) (ptr : Sim.BlockPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockMPtr.writeNumArguments ctx.buf ptr.impl val h) bl.toM =
    if bl = ptr.spec then val else Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ptr.spec ptrIb.ib
  have disj := ctx.sim.disjoint_allocs (.block ptr.spec) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  grind (splits := 20) [readNumArguments!, writeNumArguments, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]

/-! ## BlockMPtr.readFirstUse! after BlockArgumentMPtr writes -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockArgumentMPtr_writeType (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeType, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockArgumentMPtr_writeFirstUse (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeFirstUse, layout_grind,
     = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
     BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockArgumentMPtr_writeIndex (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeIndex, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockArgumentMPtr_writeOwner (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeOwner, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]


/-! ## BlockMPtr.readPrev! after BlockArgumentMPtr writes -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockArgumentMPtr_writeType (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, BlockArgumentMPtr.writeType, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockArgumentMPtr_writeFirstUse (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockArgumentMPtr_writeIndex (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, BlockArgumentMPtr.writeIndex, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockArgumentMPtr_writeOwner (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readPrev!, BlockArgumentMPtr.writeOwner, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]


/-! ## BlockMPtr.readNext! after BlockArgumentMPtr writes -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockArgumentMPtr_writeType (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readNext!, BlockArgumentMPtr.writeType, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockArgumentMPtr_writeFirstUse (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readNext!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockArgumentMPtr_writeIndex (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readNext!, BlockArgumentMPtr.writeIndex, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockArgumentMPtr_writeOwner (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.next
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readNext!, BlockArgumentMPtr.writeOwner, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]


/-! ## BlockMPtr.readParent! after BlockArgumentMPtr writes -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockArgumentMPtr_writeType (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readParent!, BlockArgumentMPtr.writeType, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockArgumentMPtr_writeFirstUse (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readParent!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockArgumentMPtr_writeIndex (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readParent!, BlockArgumentMPtr.writeIndex, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockArgumentMPtr_writeOwner (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readParent!, BlockArgumentMPtr.writeOwner, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]


/-! ## BlockMPtr.readFirstOp! after BlockArgumentMPtr writes -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockArgumentMPtr_writeType (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readFirstOp!, BlockArgumentMPtr.writeType, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockArgumentMPtr_writeFirstUse (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readFirstOp!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockArgumentMPtr_writeIndex (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readFirstOp!, BlockArgumentMPtr.writeIndex, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockArgumentMPtr_writeOwner (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readFirstOp!, BlockArgumentMPtr.writeOwner, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]


/-! ## BlockMPtr.readLastOp! after BlockArgumentMPtr writes -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockArgumentMPtr_writeType (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readLastOp!, BlockArgumentMPtr.writeType, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockArgumentMPtr_writeFirstUse (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readLastOp!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockArgumentMPtr_writeIndex (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readLastOp!, BlockArgumentMPtr.writeIndex, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockArgumentMPtr_writeOwner (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readLastOp!, BlockArgumentMPtr.writeOwner, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]


/-! ## BlockMPtr.readNumArguments! after BlockArgumentMPtr writes -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockArgumentMPtr_writeType (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readNumArguments!, BlockArgumentMPtr.writeType, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockArgumentMPtr_writeFirstUse (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readNumArguments!, BlockArgumentMPtr.writeFirstUse, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockArgumentMPtr_writeIndex (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readNumArguments!, BlockArgumentMPtr.writeIndex, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockArgumentMPtr_writeOwner (bl : Veir.BlockPtr) (arg : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (argIb : arg.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have disj := ctx.sim.disjoint_allocs (.block arg.spec.block) (.block bl)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  have hincl := BlockArgumentPtr.range_included_block_range (by grind) arg.spec argIb.ib
  have hsim := argIb.sim
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.in_bounds (.block arg.spec.block) (by grind)
  simp only [Sim.BlockArgumentPtr.Sim] at hsim
  grind (splits := 20) [readNumArguments!, BlockArgumentMPtr.writeOwner, layout_grind,
    = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]


/-! ## BlockMPtr.readFirstUse! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_operationMPtr_writeNext (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstUse!, OperationMPtr.writeNext, bl, op2

/-! ## BlockMPtr.readPrev! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_operationMPtr_writeNext (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opScalar readPrev!, OperationMPtr.writeNext, bl, op2

/-! ## BlockMPtr.readNext! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_operationMPtr_writeNext (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opScalar readNext!, OperationMPtr.writeNext, bl, op2

/-! ## BlockMPtr.readParent! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_operationMPtr_writeNext (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opScalar readParent!, OperationMPtr.writeNext, bl, op2

/-! ## BlockMPtr.readFirstOp! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_operationMPtr_writeNext (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstOp!, OperationMPtr.writeNext, bl, op2

/-! ## BlockMPtr.readLastOp! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_operationMPtr_writeNext (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opScalar readLastOp!, OperationMPtr.writeNext, bl, op2

/-! ## BlockMPtr.readNumArguments! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_operationMPtr_writeNext (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opScalar readNumArguments!, OperationMPtr.writeNext, bl, op2

/-! ## BlockMPtr.readFirstUse! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_operationMPtr_writeNumResults (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstUse!, OperationMPtr.writeNumResults, bl, op2

/-! ## BlockMPtr.readPrev! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_operationMPtr_writeNumResults (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opScalar readPrev!, OperationMPtr.writeNumResults, bl, op2

/-! ## BlockMPtr.readNext! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_operationMPtr_writeNumResults (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opScalar readNext!, OperationMPtr.writeNumResults, bl, op2

/-! ## BlockMPtr.readParent! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_operationMPtr_writeNumResults (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opScalar readParent!, OperationMPtr.writeNumResults, bl, op2

/-! ## BlockMPtr.readFirstOp! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_operationMPtr_writeNumResults (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstOp!, OperationMPtr.writeNumResults, bl, op2

/-! ## BlockMPtr.readLastOp! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_operationMPtr_writeNumResults (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opScalar readLastOp!, OperationMPtr.writeNumResults, bl, op2

/-! ## BlockMPtr.readNumArguments! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_operationMPtr_writeNumResults (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opScalar readNumArguments!, OperationMPtr.writeNumResults, bl, op2

/-! ## BlockMPtr.readFirstUse! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_operationMPtr_writeNumBlockOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstUse!, OperationMPtr.writeNumBlockOperands, bl, op2

/-! ## BlockMPtr.readPrev! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_operationMPtr_writeNumBlockOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opScalar readPrev!, OperationMPtr.writeNumBlockOperands, bl, op2

/-! ## BlockMPtr.readNext! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_operationMPtr_writeNumBlockOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opScalar readNext!, OperationMPtr.writeNumBlockOperands, bl, op2

/-! ## BlockMPtr.readParent! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_operationMPtr_writeNumBlockOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opScalar readParent!, OperationMPtr.writeNumBlockOperands, bl, op2

/-! ## BlockMPtr.readFirstOp! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_operationMPtr_writeNumBlockOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstOp!, OperationMPtr.writeNumBlockOperands, bl, op2

/-! ## BlockMPtr.readLastOp! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_operationMPtr_writeNumBlockOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opScalar readLastOp!, OperationMPtr.writeNumBlockOperands, bl, op2

/-! ## BlockMPtr.readNumArguments! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_operationMPtr_writeNumBlockOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opScalar readNumArguments!, OperationMPtr.writeNumBlockOperands, bl, op2

/-! ## BlockMPtr.readFirstUse! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_operationMPtr_writeNumRegions (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstUse!, OperationMPtr.writeNumRegions, bl, op2

/-! ## BlockMPtr.readPrev! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_operationMPtr_writeNumRegions (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opScalar readPrev!, OperationMPtr.writeNumRegions, bl, op2

/-! ## BlockMPtr.readNext! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_operationMPtr_writeNumRegions (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opScalar readNext!, OperationMPtr.writeNumRegions, bl, op2

/-! ## BlockMPtr.readParent! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_operationMPtr_writeNumRegions (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opScalar readParent!, OperationMPtr.writeNumRegions, bl, op2

/-! ## BlockMPtr.readFirstOp! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_operationMPtr_writeNumRegions (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstOp!, OperationMPtr.writeNumRegions, bl, op2

/-! ## BlockMPtr.readLastOp! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_operationMPtr_writeNumRegions (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opScalar readLastOp!, OperationMPtr.writeNumRegions, bl, op2

/-! ## BlockMPtr.readNumArguments! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_operationMPtr_writeNumRegions (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opScalar readNumArguments!, OperationMPtr.writeNumRegions, bl, op2

/-! ## BlockMPtr.readFirstUse! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_operationMPtr_writeNumOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstUse!, OperationMPtr.writeNumOperands, bl, op2

/-! ## BlockMPtr.readPrev! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_operationMPtr_writeNumOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opScalar readPrev!, OperationMPtr.writeNumOperands, bl, op2

/-! ## BlockMPtr.readNext! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_operationMPtr_writeNumOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opScalar readNext!, OperationMPtr.writeNumOperands, bl, op2

/-! ## BlockMPtr.readParent! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_operationMPtr_writeNumOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opScalar readParent!, OperationMPtr.writeNumOperands, bl, op2

/-! ## BlockMPtr.readFirstOp! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_operationMPtr_writeNumOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstOp!, OperationMPtr.writeNumOperands, bl, op2

/-! ## BlockMPtr.readLastOp! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_operationMPtr_writeNumOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opScalar readLastOp!, OperationMPtr.writeNumOperands, bl, op2

/-! ## BlockMPtr.readNumArguments! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_operationMPtr_writeNumOperands (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opScalar readNumArguments!, OperationMPtr.writeNumOperands, bl, op2

/-! ## BlockMPtr.readFirstUse! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_operationMPtr_writeAttrs (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstUse!, OperationMPtr.writeAttrs, bl, op2

/-! ## BlockMPtr.readPrev! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_operationMPtr_writeAttrs (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opScalar readPrev!, OperationMPtr.writeAttrs, bl, op2

/-! ## BlockMPtr.readNext! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_operationMPtr_writeAttrs (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opScalar readNext!, OperationMPtr.writeAttrs, bl, op2

/-! ## BlockMPtr.readParent! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_operationMPtr_writeAttrs (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opScalar readParent!, OperationMPtr.writeAttrs, bl, op2

/-! ## BlockMPtr.readFirstOp! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_operationMPtr_writeAttrs (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstOp!, OperationMPtr.writeAttrs, bl, op2

/-! ## BlockMPtr.readLastOp! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_operationMPtr_writeAttrs (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opScalar readLastOp!, OperationMPtr.writeAttrs, bl, op2

/-! ## BlockMPtr.readNumArguments! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_operationMPtr_writeAttrs (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opScalar readNumArguments!, OperationMPtr.writeAttrs, bl, op2

/-! ## BlockMPtr.readFirstUse! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_operationMPtr_writeOpType (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstUse!, OperationMPtr.writeOpType, bl, op2

/-! ## BlockMPtr.readPrev! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_operationMPtr_writeOpType (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opScalar readPrev!, OperationMPtr.writeOpType, bl, op2

/-! ## BlockMPtr.readNext! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_operationMPtr_writeOpType (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opScalar readNext!, OperationMPtr.writeOpType, bl, op2

/-! ## BlockMPtr.readParent! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_operationMPtr_writeOpType (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opScalar readParent!, OperationMPtr.writeOpType, bl, op2

/-! ## BlockMPtr.readFirstOp! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_operationMPtr_writeOpType (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstOp!, OperationMPtr.writeOpType, bl, op2

/-! ## BlockMPtr.readLastOp! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_operationMPtr_writeOpType (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opScalar readLastOp!, OperationMPtr.writeOpType, bl, op2

/-! ## BlockMPtr.readNumArguments! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_operationMPtr_writeOpType (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opScalar readNumArguments!, OperationMPtr.writeOpType, bl, op2

/-! ## BlockMPtr.readFirstUse! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_operationMPtr_writePrev (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstUse!, OperationMPtr.writePrev, bl, op2

/-! ## BlockMPtr.readPrev! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_operationMPtr_writePrev (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opScalar readPrev!, OperationMPtr.writePrev, bl, op2

/-! ## BlockMPtr.readNext! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_operationMPtr_writePrev (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opScalar readNext!, OperationMPtr.writePrev, bl, op2

/-! ## BlockMPtr.readParent! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_operationMPtr_writePrev (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opScalar readParent!, OperationMPtr.writePrev, bl, op2

/-! ## BlockMPtr.readFirstOp! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_operationMPtr_writePrev (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstOp!, OperationMPtr.writePrev, bl, op2

/-! ## BlockMPtr.readLastOp! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_operationMPtr_writePrev (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opScalar readLastOp!, OperationMPtr.writePrev, bl, op2

/-! ## BlockMPtr.readNumArguments! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_operationMPtr_writePrev (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opScalar readNumArguments!, OperationMPtr.writePrev, bl, op2

/-! ## BlockMPtr.readFirstUse! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_operationMPtr_writeParent (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstUse!, OperationMPtr.writeParent, bl, op2

/-! ## BlockMPtr.readPrev! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_operationMPtr_writeParent (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opScalar readPrev!, OperationMPtr.writeParent, bl, op2

/-! ## BlockMPtr.readNext! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_operationMPtr_writeParent (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opScalar readNext!, OperationMPtr.writeParent, bl, op2

/-! ## BlockMPtr.readParent! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_operationMPtr_writeParent (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opScalar readParent!, OperationMPtr.writeParent, bl, op2

/-! ## BlockMPtr.readFirstOp! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_operationMPtr_writeParent (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opScalar readFirstOp!, OperationMPtr.writeParent, bl, op2

/-! ## BlockMPtr.readLastOp! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_operationMPtr_writeParent (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opScalar readLastOp!, OperationMPtr.writeParent, bl, op2

/-! ## BlockMPtr.readNumArguments! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_operationMPtr_writeParent (bl : Veir.BlockPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opScalar readNumArguments!, OperationMPtr.writeParent, bl, op2

/-! ## BlockMPtr.readFirstUse! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_regionMPtr_writeFirstBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_region readFirstUse!, RegionMPtr.writeFirstBlock, bl, w2

/-! ## BlockMPtr.readFirstUse! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_regionMPtr_writeLastBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_region readFirstUse!, RegionMPtr.writeLastBlock, bl, w2

/-! ## BlockMPtr.readFirstUse! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_regionMPtr_writeParent (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_region readFirstUse!, RegionMPtr.writeParent, bl, w2

/-! ## BlockMPtr.readPrev! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_regionMPtr_writeFirstBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_region readPrev!, RegionMPtr.writeFirstBlock, bl, w2

/-! ## BlockMPtr.readPrev! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_regionMPtr_writeLastBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_region readPrev!, RegionMPtr.writeLastBlock, bl, w2

/-! ## BlockMPtr.readPrev! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_regionMPtr_writeParent (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_region readPrev!, RegionMPtr.writeParent, bl, w2

/-! ## BlockMPtr.readNext! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_regionMPtr_writeFirstBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_region readNext!, RegionMPtr.writeFirstBlock, bl, w2

/-! ## BlockMPtr.readNext! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_regionMPtr_writeLastBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_region readNext!, RegionMPtr.writeLastBlock, bl, w2

/-! ## BlockMPtr.readNext! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_regionMPtr_writeParent (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_region readNext!, RegionMPtr.writeParent, bl, w2

/-! ## BlockMPtr.readParent! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_regionMPtr_writeFirstBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_region readParent!, RegionMPtr.writeFirstBlock, bl, w2

/-! ## BlockMPtr.readParent! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_regionMPtr_writeLastBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_region readParent!, RegionMPtr.writeLastBlock, bl, w2

/-! ## BlockMPtr.readParent! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_regionMPtr_writeParent (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_region readParent!, RegionMPtr.writeParent, bl, w2

/-! ## BlockMPtr.readFirstOp! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_regionMPtr_writeFirstBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_region readFirstOp!, RegionMPtr.writeFirstBlock, bl, w2

/-! ## BlockMPtr.readFirstOp! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_regionMPtr_writeLastBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_region readFirstOp!, RegionMPtr.writeLastBlock, bl, w2

/-! ## BlockMPtr.readFirstOp! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_regionMPtr_writeParent (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_region readFirstOp!, RegionMPtr.writeParent, bl, w2

/-! ## BlockMPtr.readLastOp! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_regionMPtr_writeFirstBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_region readLastOp!, RegionMPtr.writeFirstBlock, bl, w2

/-! ## BlockMPtr.readLastOp! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_regionMPtr_writeLastBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_region readLastOp!, RegionMPtr.writeLastBlock, bl, w2

/-! ## BlockMPtr.readLastOp! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_regionMPtr_writeParent (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_region readLastOp!, RegionMPtr.writeParent, bl, w2

/-! ## BlockMPtr.readNumArguments! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_regionMPtr_writeFirstBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_region readNumArguments!, RegionMPtr.writeFirstBlock, bl, w2

/-! ## BlockMPtr.readNumArguments! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_regionMPtr_writeLastBlock (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_region readNumArguments!, RegionMPtr.writeLastBlock, bl, w2

/-! ## BlockMPtr.readNumArguments! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_regionMPtr_writeParent (bl : Veir.BlockPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_region readNumArguments!, RegionMPtr.writeParent, bl, w2

/-! ## BlockMPtr.readFirstUse! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_opResultMPtr_writeType (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opResult readFirstUse!, OpResultMPtr.writeType, bl, w2

/-! ## BlockMPtr.readFirstUse! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_opResultMPtr_writeFirstUse (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opResult readFirstUse!, OpResultMPtr.writeFirstUse, bl, w2

/-! ## BlockMPtr.readFirstUse! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_opResultMPtr_writeIndex (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opResult readFirstUse!, OpResultMPtr.writeIndex, bl, w2

/-! ## BlockMPtr.readFirstUse! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_opResultMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opResult readFirstUse!, OpResultMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readPrev! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_opResultMPtr_writeType (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opResult readPrev!, OpResultMPtr.writeType, bl, w2

/-! ## BlockMPtr.readPrev! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_opResultMPtr_writeFirstUse (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opResult readPrev!, OpResultMPtr.writeFirstUse, bl, w2

/-! ## BlockMPtr.readPrev! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_opResultMPtr_writeIndex (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opResult readPrev!, OpResultMPtr.writeIndex, bl, w2

/-! ## BlockMPtr.readPrev! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_opResultMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opResult readPrev!, OpResultMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readNext! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_opResultMPtr_writeType (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opResult readNext!, OpResultMPtr.writeType, bl, w2

/-! ## BlockMPtr.readNext! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_opResultMPtr_writeFirstUse (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opResult readNext!, OpResultMPtr.writeFirstUse, bl, w2

/-! ## BlockMPtr.readNext! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_opResultMPtr_writeIndex (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opResult readNext!, OpResultMPtr.writeIndex, bl, w2

/-! ## BlockMPtr.readNext! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_opResultMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opResult readNext!, OpResultMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readParent! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_opResultMPtr_writeType (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opResult readParent!, OpResultMPtr.writeType, bl, w2

/-! ## BlockMPtr.readParent! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_opResultMPtr_writeFirstUse (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opResult readParent!, OpResultMPtr.writeFirstUse, bl, w2

/-! ## BlockMPtr.readParent! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_opResultMPtr_writeIndex (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opResult readParent!, OpResultMPtr.writeIndex, bl, w2

/-! ## BlockMPtr.readParent! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_opResultMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opResult readParent!, OpResultMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readFirstOp! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_opResultMPtr_writeType (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opResult readFirstOp!, OpResultMPtr.writeType, bl, w2

/-! ## BlockMPtr.readFirstOp! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_opResultMPtr_writeFirstUse (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opResult readFirstOp!, OpResultMPtr.writeFirstUse, bl, w2

/-! ## BlockMPtr.readFirstOp! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_opResultMPtr_writeIndex (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opResult readFirstOp!, OpResultMPtr.writeIndex, bl, w2

/-! ## BlockMPtr.readFirstOp! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_opResultMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opResult readFirstOp!, OpResultMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readLastOp! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_opResultMPtr_writeType (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opResult readLastOp!, OpResultMPtr.writeType, bl, w2

/-! ## BlockMPtr.readLastOp! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_opResultMPtr_writeFirstUse (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opResult readLastOp!, OpResultMPtr.writeFirstUse, bl, w2

/-! ## BlockMPtr.readLastOp! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_opResultMPtr_writeIndex (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opResult readLastOp!, OpResultMPtr.writeIndex, bl, w2

/-! ## BlockMPtr.readLastOp! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_opResultMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opResult readLastOp!, OpResultMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readNumArguments! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_opResultMPtr_writeType (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opResult readNumArguments!, OpResultMPtr.writeType, bl, w2

/-! ## BlockMPtr.readNumArguments! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_opResultMPtr_writeFirstUse (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opResult readNumArguments!, OpResultMPtr.writeFirstUse, bl, w2

/-! ## BlockMPtr.readNumArguments! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_opResultMPtr_writeIndex (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opResult readNumArguments!, OpResultMPtr.writeIndex, bl, w2

/-! ## BlockMPtr.readNumArguments! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_opResultMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opResult readNumArguments!, OpResultMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readFirstUse! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_opOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opOperand readFirstUse!, OpOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readFirstUse! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_opOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opOperand readFirstUse!, OpOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readFirstUse! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_opOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opOperand readFirstUse!, OpOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readFirstUse! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_opOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_opOperand readFirstUse!, OpOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readPrev! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_opOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opOperand readPrev!, OpOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readPrev! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_opOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opOperand readPrev!, OpOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readPrev! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_opOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opOperand readPrev!, OpOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readPrev! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_opOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_opOperand readPrev!, OpOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readNext! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_opOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opOperand readNext!, OpOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readNext! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_opOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opOperand readNext!, OpOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readNext! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_opOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opOperand readNext!, OpOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readNext! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_opOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_opOperand readNext!, OpOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readParent! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_opOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opOperand readParent!, OpOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readParent! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_opOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opOperand readParent!, OpOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readParent! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_opOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opOperand readParent!, OpOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readParent! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_opOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_opOperand readParent!, OpOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readFirstOp! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_opOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opOperand readFirstOp!, OpOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readFirstOp! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_opOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opOperand readFirstOp!, OpOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readFirstOp! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_opOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opOperand readFirstOp!, OpOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readFirstOp! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_opOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_opOperand readFirstOp!, OpOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readLastOp! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_opOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opOperand readLastOp!, OpOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readLastOp! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_opOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opOperand readLastOp!, OpOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readLastOp! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_opOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opOperand readLastOp!, OpOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readLastOp! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_opOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_opOperand readLastOp!, OpOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readNumArguments! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_opOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opOperand readNumArguments!, OpOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readNumArguments! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_opOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opOperand readNumArguments!, OpOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readNumArguments! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_opOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opOperand readNumArguments!, OpOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readNumArguments! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_opOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_opOperand readNumArguments!, OpOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readFirstUse! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_blockOperand readFirstUse!, BlockOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readFirstUse! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_blockOperand readFirstUse!, BlockOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readFirstUse! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_blockOperand readFirstUse!, BlockOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readFirstUse! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_blockOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  rw_bl_blockOperand readFirstUse!, BlockOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readPrev! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_blockOperand readPrev!, BlockOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readPrev! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_blockOperand readPrev!, BlockOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readPrev! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_blockOperand readPrev!, BlockOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readPrev! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_blockOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  rw_bl_blockOperand readPrev!, BlockOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readNext! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_blockOperand readNext!, BlockOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readNext! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_blockOperand readNext!, BlockOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readNext! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_blockOperand readNext!, BlockOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readNext! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_blockOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  rw_bl_blockOperand readNext!, BlockOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readParent! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_blockOperand readParent!, BlockOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readParent! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_blockOperand readParent!, BlockOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readParent! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_blockOperand readParent!, BlockOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readParent! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_blockOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  rw_bl_blockOperand readParent!, BlockOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readFirstOp! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_blockOperand readFirstOp!, BlockOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readFirstOp! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_blockOperand readFirstOp!, BlockOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readFirstOp! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_blockOperand readFirstOp!, BlockOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readFirstOp! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_blockOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  rw_bl_blockOperand readFirstOp!, BlockOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readLastOp! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_blockOperand readLastOp!, BlockOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readLastOp! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_blockOperand readLastOp!, BlockOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readLastOp! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_blockOperand readLastOp!, BlockOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readLastOp! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_blockOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  rw_bl_blockOperand readLastOp!, BlockOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readNumArguments! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockOperandMPtr_writeNextUse (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_blockOperand readNumArguments!, BlockOperandMPtr.writeNextUse, bl, w2

/-! ## BlockMPtr.readNumArguments! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockOperandMPtr_writeBack (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_blockOperand readNumArguments!, BlockOperandMPtr.writeBack, bl, w2

/-! ## BlockMPtr.readNumArguments! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockOperandMPtr_writeOwner (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_blockOperand readNumArguments!, BlockOperandMPtr.writeOwner, bl, w2

/-! ## BlockMPtr.readNumArguments! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockOperandMPtr_writeValue (bl : Veir.BlockPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (blIb : bl.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  rw_bl_blockOperand readNumArguments!, BlockOperandMPtr.writeValue, bl, w2

/-! ## BlockMPtr.readFirstUse! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_valueImplMPtr_writeType (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readPrev! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_valueImplMPtr_writeType (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readPrev!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readPrev!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readNext! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_valueImplMPtr_writeType (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.next
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readNext!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNext!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readParent! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_valueImplMPtr_writeType (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readParent!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readParent!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readFirstOp! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_valueImplMPtr_writeType (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstOp!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readFirstOp!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readLastOp! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_valueImplMPtr_writeType (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readLastOp!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readLastOp!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readNumArguments! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_valueImplMPtr_writeType (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readNumArguments!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumArguments!, ValueImplMPtr.writeType, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readFirstUse! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_valueImplMPtr_writeFirstUse (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readPrev! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_valueImplMPtr_writeFirstUse (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readPrev!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readPrev!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readNext! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_valueImplMPtr_writeFirstUse (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.next
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readNext!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNext!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readParent! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_valueImplMPtr_writeFirstUse (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readParent!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readParent!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readFirstOp! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_valueImplMPtr_writeFirstUse (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstOp!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readFirstOp!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readLastOp! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_valueImplMPtr_writeFirstUse (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readLastOp!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readLastOp!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readNumArguments! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_valueImplMPtr_writeFirstUse (bl : Veir.BlockPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readNumArguments!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNumArguments!, ValueImplMPtr.writeFirstUse, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

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
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    by_cases ptr.spec = .blockFirstUse bl
    ·
      grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]
    · have : bl ≠ bl2 := by grind
      grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

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
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readPrev!, BlockOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

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
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readNext!, BlockOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

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
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readParent!, BlockOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

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
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readFirstOp!, BlockOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

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
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readLastOp!, BlockOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readNumArguments! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_blockOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with bo | bl2
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.block bl) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    have := @Sim.BlockOperandPtr.after_lt_ctx
    grind (splits := 20) [readNumArguments!, BlockOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block bl2) (.block bl) (by grind) (by grind)
    have hinclw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl2) (by grind)
    grind (splits := 20) [readNumArguments!, BlockOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readFirstUse! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstUse!_opOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstUse! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstUse! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.firstUse
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block bl) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readPrev! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readPrev!_opOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readPrev! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readPrev! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.prev
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block bl) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readPrev!, OpOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readPrev!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readPrev!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readNext! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNext!_opOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNext! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNext! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.next
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block bl) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readNext!, OpOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readNext!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNext!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readParent! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readParent!_opOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readParent! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readParent! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.parent
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block bl) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readParent!, OpOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readParent!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readParent!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readFirstOp! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readFirstOp!_opOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readFirstOp! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readFirstOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.firstOp
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block bl) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readFirstOp!, OpOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readFirstOp!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readFirstOp!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readLastOp! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readLastOp!_opOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readLastOp! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readLastOp! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.lastOp
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block bl) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readLastOp!, OpOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readLastOp!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readLastOp!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockMPtr.readNumArguments! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockMPtr.readNumArguments!_opOperandPtrMPtr_write (bl : Veir.BlockPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (blIb : bl.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockMPtr.readNumArguments! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) bl.toM =
    Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM := by
  have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl blIb
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have := ctx.sim.encoding_block bl (by grind) |>.numArguments
  have := ctx.sim.in_bounds (.block bl) (by grind)
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.block bl) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readNumArguments!, OpOperandPtrMPtr.write, layout_grind,
      = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
      OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block bl) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readNumArguments!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.block bl) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNumArguments!, OpOperandPtrMPtr.write, layout_grind,
        = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
