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

@[local ext, local grind ext]
theorem _root_.Veir.OpResultPtr.ext (x y : OpResultPtr) : x.op = y.op → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

@[local ext, local grind ext]
theorem _root_.Veir.BlockArgumentPtr.ext (x y : BlockArgumentPtr) : x.block = y.block → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

/-! ## same-struct CONDITIONAL: readType! after ValueImplMPtr.writeType -/

@[layout_grind =]
theorem ValueImplMPtr.readType!_valueImplMPtr_writeType (vp : Veir.ValuePtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) (vp.toM ctx.spec) =
    if vp = ptr.spec then val else Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hr : vp with rres | rarg <;> rcases hw : ptr.spec with wres | warg
  · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wres.op) (by grind) (by grind)
    have hi1 := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hi2 := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wres.op) (by grind)
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wres.index < (wres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    by_cases vp = ptr.spec
    · grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    · have : rres ≠ wres := by grind
      grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block warg.block) (by grind) (by grind)
    have hi1 := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hi2 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block warg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wres.op) (by grind) (by grind)
    have hi1 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hi2 := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block warg.block) (by grind) (by grind)
    have hi1 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hi2 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block warg.block) (by grind)
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : warg.index < (warg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    by_cases vp = ptr.spec
    · grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]
    · have : rarg ≠ warg := by grind
      grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]


/-! ## ValueImplMPtr.readType! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_valueImplMPtr_writeFirstUse (vp : Veir.ValuePtr) (ptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hr : vp with rres | rarg <;> rcases hw : ptr.spec with wres | warg
  · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wres.op) (by grind) (by grind)
    have hi1 := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hi2 := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wres.op) (by grind)
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wres.index < (wres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    grind (splits := 20) [readType!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block warg.block) (by grind) (by grind)
    have hi1 := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hi2 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block warg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wres.op) (by grind) (by grind)
    have hi1 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hi2 := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block warg.block) (by grind) (by grind)
    have hi1 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hi2 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block warg.block) (by grind)
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : warg.index < (warg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    grind (splits := 20) [readType!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_valueImplMPtr_writeType (vp : Veir.ValuePtr) (ptr : Sim.ValuePtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.ValueImplMPtr.writeType ctx.buf ptr.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hr : vp with rres | rarg <;> rcases hw : ptr.spec with wres | warg
  · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wres.op) (by grind) (by grind)
    have hi1 := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hi2 := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wres.op) (by grind)
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wres.index < (wres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block warg.block) (by grind) (by grind)
    have hi1 := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hi2 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block warg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wres.op) (by grind) (by grind)
    have hi1 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hi2 := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block warg.block) (by grind) (by grind)
    have hi1 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hi2 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block warg.block) (by grind)
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : warg.index < (warg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after ValueImplMPtr.writeFirstUse -/

@[layout_grind =]
theorem ValueImplMPtr.readFirstUse!_valueImplMPtr_writeFirstUse (vp : Veir.ValuePtr) (ptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (vp.toM ctx.spec) =
    if vp = ptr.spec then val.impl else Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hr : vp with rres | rarg <;> rcases hw : ptr.spec with wres | warg
  · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wres.op) (by grind) (by grind)
    have hi1 := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hi2 := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wres.op) (by grind)
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wres.index < (wres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    by_cases vp = ptr.spec
    · grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    · have : rres ≠ wres := by grind
      grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block warg.block) (by grind) (by grind)
    have hi1 := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hi2 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block warg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wres.op) (by grind) (by grind)
    have hi1 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hi2 := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block warg.block) (by grind) (by grind)
    have hi1 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hi2 := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block warg.block) (by grind)
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : warg.index < (warg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    by_cases vp = ptr.spec
    · grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]
    · have : rarg ≠ warg := by grind
      grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockMPtr_writeFirstUse (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockMPtr_writePrev (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writePrev, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writePrev, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockMPtr_writeNext (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeNext, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeNext, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockMPtr_writeParent (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeParent, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeParent, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockMPtr_writeFirstOp (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeFirstOp, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeFirstOp, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockMPtr_writeLastOp (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeLastOp, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeLastOp, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockMPtr_writeNumArguments (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeNumArguments, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockMPtr.writeNumArguments, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockMPtr_writeFirstUse (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockMPtr_writePrev (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writePrev, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writePrev, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockMPtr_writeNext (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeNext, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeNext, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockMPtr_writeParent (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeParent, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeParent, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockMPtr_writeFirstOp (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeFirstOp, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeFirstOp, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockMPtr_writeLastOp (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeLastOp, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeLastOp, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockMPtr_writeNumArguments (vp : Veir.ValuePtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockPtr.after_lt_ctx
  have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) w2.spec w2Ib.ib
  have hww := ctx.sim.in_bounds (.block w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeNumArguments, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockMPtr.writeNumArguments, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_regionMPtr_writeFirstBlock (vp : Veir.ValuePtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.region w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.region w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, RegionMPtr.writeFirstBlock, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.region w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, RegionMPtr.writeFirstBlock, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_regionMPtr_writeLastBlock (vp : Veir.ValuePtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.region w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.region w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, RegionMPtr.writeLastBlock, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.region w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, RegionMPtr.writeLastBlock, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_regionMPtr_writeParent (vp : Veir.ValuePtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.region w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.region w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, RegionMPtr.writeParent, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.region w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, RegionMPtr.writeParent, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_regionMPtr_writeFirstBlock (vp : Veir.ValuePtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.region w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.region w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, RegionMPtr.writeFirstBlock, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.region w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, RegionMPtr.writeFirstBlock, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_regionMPtr_writeLastBlock (vp : Veir.ValuePtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.region w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.region w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, RegionMPtr.writeLastBlock, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.region w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, RegionMPtr.writeLastBlock, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_regionMPtr_writeParent (vp : Veir.ValuePtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.region w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.region w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, RegionMPtr.writeParent, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.region w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, RegionMPtr.writeParent, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_operationMPtr_writeNext (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OperationMPtr.writeNext ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNext, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNext, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_operationMPtr_writeNumResults (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OperationMPtr.writeNumResults ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNumResults, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNumResults, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_operationMPtr_writeNumBlockOperands (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNumBlockOperands, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNumBlockOperands, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_operationMPtr_writeNumRegions (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OperationMPtr.writeNumRegions ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNumRegions, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNumRegions, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_operationMPtr_writeNumOperands (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OperationMPtr.writeNumOperands ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNumOperands, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeNumOperands, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_operationMPtr_writeAttrs (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OperationMPtr.writeAttrs ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeAttrs, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeAttrs, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_operationMPtr_writeOpType (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt32) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OperationMPtr.writeOpType ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeOpType, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeOpType, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_operationMPtr_writePrev (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OperationMPtr.writePrev ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writePrev, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writePrev, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_operationMPtr_writeParent (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OperationMPtr.writeParent ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeParent, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OperationMPtr.writeParent, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_operationMPtr_writeNext (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OperationMPtr.writeNext ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNext, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNext, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_operationMPtr_writeNumResults (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumResults ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNumResults, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNumResults, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_operationMPtr_writeNumBlockOperands (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNumBlockOperands, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNumBlockOperands, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_operationMPtr_writeNumRegions (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumRegions ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNumRegions, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNumRegions, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_operationMPtr_writeNumOperands (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumOperands ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNumOperands, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeNumOperands, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_operationMPtr_writeAttrs (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OperationMPtr.writeAttrs ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeAttrs, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeAttrs, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_operationMPtr_writeOpType (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : UInt32) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OperationMPtr.writeOpType ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeOpType, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeOpType, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_operationMPtr_writePrev (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OperationMPtr.writePrev ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writePrev, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writePrev, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_operationMPtr_writeParent (vp : Veir.ValuePtr) (w2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OperationMPtr.writeParent ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hww := ctx.sim.in_bounds (.operation w2.spec) (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeParent, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OperationMPtr.writeParent, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_opOperandMPtr_writeNextUse (vp : Veir.ValuePtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.OpOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandMPtr.writeNextUse, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandMPtr.writeNextUse, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_opOperandMPtr_writeBack (vp : Veir.ValuePtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.OpOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandMPtr.writeBack, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandMPtr.writeBack, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_opOperandMPtr_writeOwner (vp : Veir.ValuePtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.OpOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandMPtr.writeOwner, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandMPtr.writeOwner, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_opOperandMPtr_writeValue (vp : Veir.ValuePtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.OpOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandMPtr.writeValue, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandMPtr.writeValue, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_opOperandMPtr_writeNextUse (vp : Veir.ValuePtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.OpOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandMPtr.writeNextUse, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandMPtr.writeNextUse, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_opOperandMPtr_writeBack (vp : Veir.ValuePtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.OpOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandMPtr.writeBack, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandMPtr.writeBack, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_opOperandMPtr_writeOwner (vp : Veir.ValuePtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.OpOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandMPtr.writeOwner, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandMPtr.writeOwner, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_opOperandMPtr_writeValue (vp : Veir.ValuePtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.OpOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandMPtr.writeValue, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandMPtr.writeValue, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockOperandMPtr_writeNextUse (vp : Veir.ValuePtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockOperandMPtr.writeNextUse, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockOperandMPtr.writeNextUse, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockOperandMPtr_writeBack (vp : Veir.ValuePtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockOperandMPtr.writeBack, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockOperandMPtr.writeBack, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockOperandMPtr_writeOwner (vp : Veir.ValuePtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockOperandMPtr.writeOwner, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockOperandMPtr.writeOwner, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockOperandMPtr_writeValue (vp : Veir.ValuePtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockOperandMPtr.writeValue, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockOperandMPtr.writeValue, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockOperandMPtr_writeNextUse (vp : Veir.ValuePtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandMPtr.writeNextUse, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandMPtr.writeNextUse, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockOperandMPtr_writeBack (vp : Veir.ValuePtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandMPtr.writeBack, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandMPtr.writeBack, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockOperandMPtr_writeOwner (vp : Veir.ValuePtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandMPtr.writeOwner, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandMPtr.writeOwner, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockOperandMPtr_writeValue (vp : Veir.ValuePtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (vpIb : vp.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have hww := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) w2.spec (by grind)
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation w2.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandMPtr.writeValue, layout_grind, ValuePtr.toM,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation w2.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockOperandMPtr.writeValue, layout_grind, ValuePtr.toM,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OpResultMPtr.writeType -/

@[layout_grind =]
theorem ValueImplMPtr.readType!_opResultMPtr_writeType (vp : Veir.ValuePtr) (wptr : Sim.OpResultPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OpResultMPtr.writeType ctx.buf wptr.impl val h) (vp.toM ctx.spec) =
    if vp = .opResult wptr.spec then val
    else Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    by_cases vp = .opResult wptr.spec
    ·
      grind (splits := 20) [readType!, OpResultMPtr.writeType, layout_grind, ValuePtr.toM,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have : rres ≠ wptr.spec := by grind
      grind (splits := 20) [readType!, OpResultMPtr.writeType, layout_grind, ValuePtr.toM,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpResultMPtr.writeType, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_opResultMPtr_writeFirstUse (vp : Veir.ValuePtr) (wptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OpResultMPtr.writeFirstUse ctx.buf wptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    grind (splits := 20) [readType!, OpResultMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpResultMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_opResultMPtr_writeIndex (vp : Veir.ValuePtr) (wptr : Sim.OpResultPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OpResultMPtr.writeIndex ctx.buf wptr.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    grind (splits := 20) [readType!, OpResultMPtr.writeIndex, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpResultMPtr.writeIndex, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_opResultMPtr_writeOwner (vp : Veir.ValuePtr) (wptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OpResultMPtr.writeOwner ctx.buf wptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    grind (splits := 20) [readType!, OpResultMPtr.writeOwner, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpResultMPtr.writeOwner, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_opResultMPtr_writeType (vp : Veir.ValuePtr) (wptr : Sim.OpResultPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OpResultMPtr.writeType ctx.buf wptr.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    grind (splits := 20) [readFirstUse!, OpResultMPtr.writeType, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpResultMPtr.writeType, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OpResultMPtr.writeFirstUse -/

@[layout_grind =]
theorem ValueImplMPtr.readFirstUse!_opResultMPtr_writeFirstUse (vp : Veir.ValuePtr) (wptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OpResultMPtr.writeFirstUse ctx.buf wptr.impl val.impl h) (vp.toM ctx.spec) =
    if vp = .opResult wptr.spec then val.impl
    else Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    by_cases vp = .opResult wptr.spec
    ·
      grind (splits := 20) [readFirstUse!, OpResultMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have : rres ≠ wptr.spec := by grind
      grind (splits := 20) [readFirstUse!, OpResultMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
    OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpResultMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_opResultMPtr_writeIndex (vp : Veir.ValuePtr) (wptr : Sim.OpResultPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OpResultMPtr.writeIndex ctx.buf wptr.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    grind (splits := 20) [readFirstUse!, OpResultMPtr.writeIndex, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpResultMPtr.writeIndex, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_opResultMPtr_writeOwner (vp : Veir.ValuePtr) (wptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OpResultMPtr.writeOwner ctx.buf wptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    have : rres.index < (rres.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices rres.op (by grind)
    grind (splits := 20) [readFirstUse!, OpResultMPtr.writeOwner, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wptr.spec.op) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.operation wptr.spec.op) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpResultMPtr.writeOwner, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockArgumentMPtr.writeType -/

@[layout_grind =]
theorem ValueImplMPtr.readType!_blockArgumentMPtr_writeType (vp : Veir.ValuePtr) (wptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockArgumentMPtr.writeType ctx.buf wptr.impl val h) (vp.toM ctx.spec) =
    if vp = .blockArgument wptr.spec then val
    else Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block wptr.spec.block) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockArgumentMPtr.writeType, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block wptr.spec.block) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    by_cases vp = .blockArgument wptr.spec
    ·
      grind (splits := 20) [readType!, BlockArgumentMPtr.writeType, layout_grind, ValuePtr.toM,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have : rarg ≠ wptr.spec := by grind
      grind (splits := 20) [readType!, BlockArgumentMPtr.writeType, layout_grind, ValuePtr.toM,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockArgumentMPtr_writeFirstUse (vp : Veir.ValuePtr) (wptr : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf wptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block wptr.spec.block) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockArgumentMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block wptr.spec.block) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    grind (splits := 20) [readType!, BlockArgumentMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockArgumentMPtr_writeIndex (vp : Veir.ValuePtr) (wptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf wptr.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block wptr.spec.block) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockArgumentMPtr.writeIndex, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block wptr.spec.block) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    grind (splits := 20) [readType!, BlockArgumentMPtr.writeIndex, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockArgumentMPtr_writeOwner (vp : Veir.ValuePtr) (wptr : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf wptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block wptr.spec.block) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readType!, BlockArgumentMPtr.writeOwner, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block wptr.spec.block) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    grind (splits := 20) [readType!, BlockArgumentMPtr.writeOwner, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockArgumentMPtr_writeType (vp : Veir.ValuePtr) (wptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeType ctx.buf wptr.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block wptr.spec.block) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeType, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block wptr.spec.block) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeType, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockArgumentMPtr.writeFirstUse -/

@[layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockArgumentMPtr_writeFirstUse (vp : Veir.ValuePtr) (wptr : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf wptr.impl val.impl h) (vp.toM ctx.spec) =
    if vp = .blockArgument wptr.spec then val.impl
    else Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block wptr.spec.block) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block wptr.spec.block) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    by_cases vp = .blockArgument wptr.spec
    ·
      grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have : rarg ≠ wptr.spec := by grind
      grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeFirstUse, layout_grind, ValuePtr.toM,
    BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockArgumentMPtr_writeIndex (vp : Veir.ValuePtr) (wptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf wptr.impl val h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block wptr.spec.block) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeIndex, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block wptr.spec.block) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeIndex, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockArgumentMPtr_writeOwner (vp : Veir.ValuePtr) (wptr : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (vpIb : vp.InBounds ctx.spec) (wptrIb : wptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf wptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  rcases hr : vp with rres | rarg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block wptr.spec.block) (by grind) (by grind)
    have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.operation rres.op) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.OpResultPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeOwner, layout_grind, ValuePtr.toM,
  OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block wptr.spec.block) (by grind) (by grind)
    have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
    have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) wptr.spec (by grind)
    have := ctx.sim.in_bounds (.block rarg.block) (by grind)
    have := ctx.sim.in_bounds (.block wptr.spec.block) (by grind)
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have := @Sim.BlockArgumentPtr.after_lt_ctx
    have : rarg.index < (rarg.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have : wptr.spec.index < (wptr.spec.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices rarg.block (by grind)
    grind (splits := 20) [readFirstUse!, BlockArgumentMPtr.writeOwner, layout_grind, ValuePtr.toM,
  BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_blockOperandPtrMPtr_write (vp : Veir.ValuePtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (vpIb : vp.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hw : ptr.spec with bo | bl
  ·
    rcases hr : vp with rres | rarg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation bo.op) (by grind) (by grind)
      have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
      have := ctx.sim.in_bounds (.operation rres.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      have hiw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
      have := ctx.sim.in_bounds (.operation bo.op) (by grind)
      have := @Sim.BlockOperandPtr.after_lt_ctx
      grind (splits := 20) [readType!, BlockOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation bo.op) (by grind) (by grind)
      have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
      have := ctx.sim.in_bounds (.block rarg.block) (by grind)
      have := @Sim.BlockArgumentPtr.after_lt_ctx
      have hiw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
      have := ctx.sim.in_bounds (.operation bo.op) (by grind)
      have := @Sim.BlockOperandPtr.after_lt_ctx
      grind (splits := 20) [readType!, BlockOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    rcases hr : vp with rres | rarg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block bl) (by grind) (by grind)
      have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
      have := ctx.sim.in_bounds (.operation rres.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      have hiw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
      grind (splits := 20) [readType!, BlockOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block bl) (by grind) (by grind)
      have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
      have := ctx.sim.in_bounds (.block rarg.block) (by grind)
      have := @Sim.BlockArgumentPtr.after_lt_ctx
      have hiw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
      grind (splits := 20) [readType!, BlockOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readFirstUse!_blockOperandPtrMPtr_write (vp : Veir.ValuePtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (vpIb : vp.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hw : ptr.spec with bo | bl
  ·
    rcases hr : vp with rres | rarg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation bo.op) (by grind) (by grind)
      have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
      have := ctx.sim.in_bounds (.operation rres.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      have hiw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
      have := ctx.sim.in_bounds (.operation bo.op) (by grind)
      have := @Sim.BlockOperandPtr.after_lt_ctx
      grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation bo.op) (by grind) (by grind)
      have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
      have := ctx.sim.in_bounds (.block rarg.block) (by grind)
      have := @Sim.BlockArgumentPtr.after_lt_ctx
      have hiw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
      have := ctx.sim.in_bounds (.operation bo.op) (by grind)
      have := @Sim.BlockOperandPtr.after_lt_ctx
      grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockOperandPtr.range, BlockOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    rcases hr : vp with rres | rarg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block bl) (by grind) (by grind)
      have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
      have := ctx.sim.in_bounds (.operation rres.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      have hiw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
      grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block bl) (by grind) (by grind)
      have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
      have := ctx.sim.in_bounds (.block rarg.block) (by grind)
      have := @Sim.BlockArgumentPtr.after_lt_ctx
      have hiw := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
      grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockPtr.range, BlockPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readType! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem ValueImplMPtr.readType!_opOperandPtrMPtr_write (vp : Veir.ValuePtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readType! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (vp.toM ctx.spec) =
    Buffed.ValueImplMPtr.readType! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hw : ptr.spec with opr | wv
  ·
    rcases hr : vp with rres | rarg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation opr.op) (by grind) (by grind)
      have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
      have := ctx.sim.in_bounds (.operation rres.op) (by grind)
      have := @Sim.OpResultPtr.after_lt_ctx
      have hiw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
      have := ctx.sim.in_bounds (.operation opr.op) (by grind)
      have := @Sim.OpOperandPtr.after_lt_ctx
      grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation opr.op) (by grind) (by grind)
      have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
      have := ctx.sim.in_bounds (.block rarg.block) (by grind)
      have := @Sim.BlockArgumentPtr.after_lt_ctx
      have hiw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
      have := ctx.sim.in_bounds (.operation opr.op) (by grind)
      have := @Sim.OpOperandPtr.after_lt_ctx
      grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    rcases hwv : wv with wres | warg
    ·
      rcases hr : vp with rres | rarg
      ·
        have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wres.op) (by grind) (by grind)
        have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
        have := ctx.sim.in_bounds (.operation rres.op) (by grind)
        have := @Sim.OpResultPtr.after_lt_ctx
        have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
        have := ctx.sim.in_bounds (.operation wres.op) (by grind)
        have := @Sim.OpResultPtr.after_lt_ctx
        grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
          OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
      ·
        have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wres.op) (by grind) (by grind)
        have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
        have := ctx.sim.in_bounds (.block rarg.block) (by grind)
        have := @Sim.BlockArgumentPtr.after_lt_ctx
        have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
        have := ctx.sim.in_bounds (.operation wres.op) (by grind)
        have := @Sim.OpResultPtr.after_lt_ctx
        grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
          BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      rcases hr : vp with rres | rarg
      ·
        have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block warg.block) (by grind) (by grind)
        have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
        have := ctx.sim.in_bounds (.operation rres.op) (by grind)
        have := @Sim.OpResultPtr.after_lt_ctx
        have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
        have := ctx.sim.in_bounds (.block warg.block) (by grind)
        have := @Sim.BlockArgumentPtr.after_lt_ctx
        grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
          OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
      ·
        have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block warg.block) (by grind) (by grind)
        have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
        have := ctx.sim.in_bounds (.block rarg.block) (by grind)
        have := @Sim.BlockArgumentPtr.after_lt_ctx
        have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
        have := ctx.sim.in_bounds (.block warg.block) (by grind)
        have := @Sim.BlockArgumentPtr.after_lt_ctx
        grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
          BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## ValueImplMPtr.readFirstUse! after OpOperandPtrMPtr.write -/

@[layout_grind =]
theorem ValueImplMPtr.readFirstUse!_opOperandPtrMPtr_write (vp : Veir.ValuePtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (vpIb : vp.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.ValueImplMPtr.readFirstUse! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (vp.toM ctx.spec) =
    if ptr.spec = .valueFirstUse vp then val.impl
    else Buffed.ValueImplMPtr.readFirstUse! ctx.buf (vp.toM ctx.spec) := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  rcases hw : ptr.spec with opr | wv
  · rcases hr : vp with rres | rarg
    · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation opr.op) (by grind) (by grind)
      have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
      have hiw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
      have := ctx.sim.in_bounds (.operation opr.op) (by grind)
      grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation opr.op) (by grind) (by grind)
      have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
      have hiw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
      grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpOperandPtr.range, OpOperandPtr.toFlat, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    rcases hwv : wv with wres | warg
    ·
      rcases hr : vp with rres | rarg
      · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.operation wres.op) (by grind) (by grind)
        have hir := OpResultPtr.range_included_op_range (ctx := ctx) rres (by grind)
        have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
        by_cases wres = rres <;>
        grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
          OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
      · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.operation wres.op) (by grind) (by grind)
        have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
        have hiw := OpResultPtr.range_included_op_range (ctx := ctx) wres (by grind)
        grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
          BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    · rcases hr : vp with rres | rarg
      · have hdisj := ctx.sim.disjoint_allocs (.operation rres.op) (.block warg.block) (by grind) (by grind)
        have := ctx.sim.in_bounds (.operation rres.op) (by grind)
        have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
        grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
          OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]
      · have hdisj := ctx.sim.disjoint_allocs (.block rarg.block) (.block warg.block) (by grind) (by grind)
        have hir := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) rarg (by grind)
        have hiw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) warg (by grind)
        by_cases rarg = warg <;>
          grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind, ValuePtr.toM,
              OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices, ValuePtr.toFlat, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
