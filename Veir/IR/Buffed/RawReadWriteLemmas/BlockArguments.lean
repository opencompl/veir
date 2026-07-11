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

/-! ## BlockArgumentMPtr.readKind! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readKind!_blockArgumentMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readKind! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readKind! ctx.buf arg.toM := by
  rw_ba_ba readKind!, BlockArgumentMPtr.writeFirstUse, arg, ptr

/-! ## BlockArgumentMPtr.readKind! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readKind!_blockArgumentMPtr_writeIndex (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : UInt64) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readKind! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf ptr.impl val h) arg.toM =
    Buffed.BlockArgumentMPtr.readKind! ctx.buf arg.toM := by
  rw_ba_ba readKind!, BlockArgumentMPtr.writeIndex, arg, ptr

/-! ## BlockArgumentMPtr.readKind! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readKind!_blockArgumentMPtr_writeOwner (arg : Veir.BlockArgumentPtr) (ptr : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readKind! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readKind! ctx.buf arg.toM := by
  rw_ba_ba readKind!, BlockArgumentMPtr.writeOwner, arg, ptr

/-! ## BlockArgumentMPtr.readKind! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readKind!_valueImplMPtr_writeFirstUse (arg : Veir.BlockArgumentPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readKind! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readKind! ctx.buf arg.toM := by
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
    grind (splits := 20) [readKind!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
    have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
    have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
    grind (splits := 20) [readKind!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
      ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

/-! ## BlockArgumentMPtr.readKind! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockArgumentMPtr.readKind!_opOperandPtrMPtr_write (arg : Veir.BlockArgumentPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (argIb : arg.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockArgumentMPtr.readKind! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) arg.toM =
    Buffed.BlockArgumentMPtr.readKind! ctx.buf arg.toM := by
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
    grind (splits := 20) [readKind!, OpOperandPtrMPtr.write, layout_grind,
      BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg2
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.block arg.block) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readKind!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg2.block) (.block arg.block) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg2 (by grind)
      have : arg2.index < (arg2.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
      have hri := ctx.sim.repr.blocks_indices arg.block (by grind)
      grind (splits := 20) [readKind!, OpOperandPtrMPtr.write, layout_grind,
        BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat,
        ValuePtr.toFlat, Block.ReprIndices, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
