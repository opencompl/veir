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

/-! ## BlockOperandMPtr.readNextUse! -/

@[local ext, local grind ext]
theorem _root_.Veir.BlockOperandPtr.ext (x y : BlockOperandPtr) : x.op = y.op → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

/-! ## BlockOperandMPtr.readNextUse! -/

@[layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockOperandMPtr_writeNextUse (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    if bo = ptr.spec then val.impl else Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readNextUse!, BlockOperandMPtr.writeNextUse, bo, ptr

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockOperandMPtr_writeBack (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockOperandMPtr.writeBack ctx.buf ptr.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readNextUse!, BlockOperandMPtr.writeBack, bo, ptr

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockOperandMPtr_writeOwner (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockOperandMPtr.writeOwner ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readNextUse!, BlockOperandMPtr.writeOwner, bo, ptr

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockOperandMPtr_writeValue (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockOperandMPtr.writeValue ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readNextUse!, BlockOperandMPtr.writeValue, bo, ptr

/-! ## BlockOperandMPtr.readBack! -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockOperandMPtr_writeNextUse (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readBack!, BlockOperandMPtr.writeNextUse, bo, ptr

@[layout_grind =]
theorem BlockOperandMPtr.readBack!_blockOperandMPtr_writeBack (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockOperandMPtr.writeBack ctx.buf ptr.impl val h) (bo.toM ctx.spec) =
    if bo = ptr.spec then val else Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readBack!, BlockOperandMPtr.writeBack, bo, ptr

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockOperandMPtr_writeOwner (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockOperandMPtr.writeOwner ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readBack!, BlockOperandMPtr.writeOwner, bo, ptr

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockOperandMPtr_writeValue (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockOperandMPtr.writeValue ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readBack!, BlockOperandMPtr.writeValue, bo, ptr

/-! ## BlockOperandMPtr.readOwner! -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockOperandMPtr_writeNextUse (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readOwner!, BlockOperandMPtr.writeNextUse, bo, ptr

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockOperandMPtr_writeBack (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockOperandMPtr.writeBack ctx.buf ptr.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readOwner!, BlockOperandMPtr.writeBack, bo, ptr

@[layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockOperandMPtr_writeOwner (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockOperandMPtr.writeOwner ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    if bo = ptr.spec then val.impl else Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readOwner!, BlockOperandMPtr.writeOwner, bo, ptr

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockOperandMPtr_writeValue (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockOperandMPtr.writeValue ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readOwner!, BlockOperandMPtr.writeValue, bo, ptr

/-! ## BlockOperandMPtr.readValue! -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockOperandMPtr_writeNextUse (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readValue!, BlockOperandMPtr.writeNextUse, bo, ptr

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockOperandMPtr_writeBack (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockOperandMPtr.writeBack ctx.buf ptr.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readValue!, BlockOperandMPtr.writeBack, bo, ptr

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockOperandMPtr_writeOwner (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockOperandMPtr.writeOwner ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readValue!, BlockOperandMPtr.writeOwner, bo, ptr

@[layout_grind =]
theorem BlockOperandMPtr.readValue!_blockOperandMPtr_writeValue (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockOperandMPtr.writeValue ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    if bo = ptr.spec then val.impl else Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_bo readValue!, BlockOperandMPtr.writeValue, bo, ptr

/-! ## BlockOperandMPtr.readNextUse! after BlockOperandPtrMPtr.write -/

@[layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockOperandPtrMPtr_write (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    if ptr.spec = .blockOperandNextUse bo then val.impl
    else Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  rcases hcase : ptr.spec with bo2 | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo2.op) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo2 (by grind)
    by_cases ptr.spec = .blockOperandNextUse bo
    ·  grind (splits := 20) [readNextUse!, BlockOperandPtrMPtr.write, layout_grind,
          BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat,
          BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
          IsIncludedI, IsDisjointI, Operation.ReprIndices]
    ·  have : bo ≠ bo2 := by grind
       grind (splits := 20) [readNextUse!, BlockOperandPtrMPtr.write, layout_grind,
          BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat,
          BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
          IsIncludedI, IsDisjointI, Operation.ReprIndices]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readNextUse!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readBack! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockOperandPtrMPtr_write (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  rcases hcase : ptr.spec with bo2 | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo2.op) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo2 (by grind)
    grind (splits := 20) [readBack!, BlockOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readBack!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readOwner! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockOperandPtrMPtr_write (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  rcases hcase : ptr.spec with bo2 | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo2.op) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo2 (by grind)
    grind (splits := 20) [readOwner!, BlockOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readOwner!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readValue! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockOperandPtrMPtr_write (bo : Veir.BlockOperandPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  rcases hcase : ptr.spec with bo2 | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo2.op) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo2 (by grind)
    grind (splits := 20) [readValue!, BlockOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readValue!, BlockOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
