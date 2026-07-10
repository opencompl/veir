module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs
public import Veir.IR.Buffed.RawReadWriteLemmas.Tactics
import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs

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

/-! ## BlockOperandMPtr.readNextUse! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_operationMPtr_writeNext (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf  (bo.toM ctx.spec) := by
  rw_bo_opScalar readNextUse!, OperationMPtr.writeNext, bo, op2

/-! ## BlockOperandMPtr.readBack! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_operationMPtr_writeNext (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readBack!, OperationMPtr.writeNext, bo, op2

/-! ## BlockOperandMPtr.readOwner! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_operationMPtr_writeNext (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readOwner!, OperationMPtr.writeNext, bo, op2

/-! ## BlockOperandMPtr.readValue! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_operationMPtr_writeNext (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readValue!, OperationMPtr.writeNext, bo, op2

/-! ## BlockOperandMPtr.readNextUse! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_operationMPtr_writeNumResults (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readNextUse!, OperationMPtr.writeNumResults, bo, op2

/-! ## BlockOperandMPtr.readBack! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_operationMPtr_writeNumResults (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readBack!, OperationMPtr.writeNumResults, bo, op2

/-! ## BlockOperandMPtr.readOwner! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_operationMPtr_writeNumResults (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readOwner!, OperationMPtr.writeNumResults, bo, op2

/-! ## BlockOperandMPtr.readValue! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_operationMPtr_writeNumResults (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readValue!, OperationMPtr.writeNumResults, bo, op2

/-! ## BlockOperandMPtr.readNextUse! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_operationMPtr_writeNumBlockOperands (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readNextUse!, OperationMPtr.writeNumBlockOperands, bo, op2

/-! ## BlockOperandMPtr.readBack! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_operationMPtr_writeNumBlockOperands (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readBack!, OperationMPtr.writeNumBlockOperands, bo, op2

/-! ## BlockOperandMPtr.readOwner! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_operationMPtr_writeNumBlockOperands (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readOwner!, OperationMPtr.writeNumBlockOperands, bo, op2

/-! ## BlockOperandMPtr.readValue! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_operationMPtr_writeNumBlockOperands (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readValue!, OperationMPtr.writeNumBlockOperands, bo, op2

/-! ## BlockOperandMPtr.readNextUse! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_operationMPtr_writeNumRegions (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readNextUse!, OperationMPtr.writeNumRegions, bo, op2

/-! ## BlockOperandMPtr.readBack! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_operationMPtr_writeNumRegions (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readBack!, OperationMPtr.writeNumRegions, bo, op2

/-! ## BlockOperandMPtr.readOwner! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_operationMPtr_writeNumRegions (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readOwner!, OperationMPtr.writeNumRegions, bo, op2

/-! ## BlockOperandMPtr.readValue! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_operationMPtr_writeNumRegions (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readValue!, OperationMPtr.writeNumRegions, bo, op2

/-! ## BlockOperandMPtr.readNextUse! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_operationMPtr_writeNumOperands (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readNextUse!, OperationMPtr.writeNumOperands, bo, op2

/-! ## BlockOperandMPtr.readBack! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_operationMPtr_writeNumOperands (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readBack!, OperationMPtr.writeNumOperands, bo, op2

/-! ## BlockOperandMPtr.readOwner! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_operationMPtr_writeNumOperands (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readOwner!, OperationMPtr.writeNumOperands, bo, op2

/-! ## BlockOperandMPtr.readValue! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_operationMPtr_writeNumOperands (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readValue!, OperationMPtr.writeNumOperands, bo, op2

/-! ## BlockOperandMPtr.readNextUse! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_operationMPtr_writeAttrs (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readNextUse!, OperationMPtr.writeAttrs, bo, op2

/-! ## BlockOperandMPtr.readBack! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_operationMPtr_writeAttrs (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readBack!, OperationMPtr.writeAttrs, bo, op2

/-! ## BlockOperandMPtr.readOwner! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_operationMPtr_writeAttrs (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readOwner!, OperationMPtr.writeAttrs, bo, op2

/-! ## BlockOperandMPtr.readValue! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_operationMPtr_writeAttrs (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readValue!, OperationMPtr.writeAttrs, bo, op2

/-! ## BlockOperandMPtr.readNextUse! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_operationMPtr_writeOpType (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readNextUse!, OperationMPtr.writeOpType, bo, op2

/-! ## BlockOperandMPtr.readBack! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_operationMPtr_writeOpType (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readBack!, OperationMPtr.writeOpType, bo, op2

/-! ## BlockOperandMPtr.readOwner! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_operationMPtr_writeOpType (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readOwner!, OperationMPtr.writeOpType, bo, op2

/-! ## BlockOperandMPtr.readValue! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_operationMPtr_writeOpType (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readValue!, OperationMPtr.writeOpType, bo, op2

/-! ## BlockOperandMPtr.readNextUse! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_operationMPtr_writePrev (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readNextUse!, OperationMPtr.writePrev, bo, op2

/-! ## BlockOperandMPtr.readBack! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_operationMPtr_writePrev (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readBack!, OperationMPtr.writePrev, bo, op2

/-! ## BlockOperandMPtr.readOwner! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_operationMPtr_writePrev (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readOwner!, OperationMPtr.writePrev, bo, op2

/-! ## BlockOperandMPtr.readValue! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_operationMPtr_writePrev (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readValue!, OperationMPtr.writePrev, bo, op2

/-! ## BlockOperandMPtr.readNextUse! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_operationMPtr_writeParent (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readNextUse!, OperationMPtr.writeParent, bo, op2

/-! ## BlockOperandMPtr.readBack! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_operationMPtr_writeParent (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readBack!, OperationMPtr.writeParent, bo, op2

/-! ## BlockOperandMPtr.readOwner! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_operationMPtr_writeParent (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readOwner!, OperationMPtr.writeParent, bo, op2

/-! ## BlockOperandMPtr.readValue! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_operationMPtr_writeParent (bo : Veir.BlockOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opScalar readValue!, OperationMPtr.writeParent, bo, op2

/-! ## BlockOperandMPtr.readNextUse! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_opResultMPtr_writeType (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readNextUse!, OpResultMPtr.writeType, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_opResultMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readNextUse!, OpResultMPtr.writeFirstUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_opResultMPtr_writeIndex (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readNextUse!, OpResultMPtr.writeIndex, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_opResultMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readNextUse!, OpResultMPtr.writeOwner, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_opResultMPtr_writeType (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readBack!, OpResultMPtr.writeType, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_opResultMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readBack!, OpResultMPtr.writeFirstUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_opResultMPtr_writeIndex (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readBack!, OpResultMPtr.writeIndex, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_opResultMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readBack!, OpResultMPtr.writeOwner, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_opResultMPtr_writeType (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readOwner!, OpResultMPtr.writeType, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_opResultMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readOwner!, OpResultMPtr.writeFirstUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_opResultMPtr_writeIndex (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readOwner!, OpResultMPtr.writeIndex, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_opResultMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readOwner!, OpResultMPtr.writeOwner, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_opResultMPtr_writeType (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readValue!, OpResultMPtr.writeType, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_opResultMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OpResultMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readValue!, OpResultMPtr.writeFirstUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_opResultMPtr_writeIndex (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OpResultMPtr.writeIndex ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readValue!, OpResultMPtr.writeIndex, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_opResultMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OpResultMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opResult readValue!, OpResultMPtr.writeOwner, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_opOperandMPtr_writeNextUse (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readNextUse!, OpOperandMPtr.writeNextUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_opOperandMPtr_writeBack (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readNextUse!, OpOperandMPtr.writeBack, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_opOperandMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readNextUse!, OpOperandMPtr.writeOwner, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_opOperandMPtr_writeValue (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readNextUse!, OpOperandMPtr.writeValue, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_opOperandMPtr_writeNextUse (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readBack!, OpOperandMPtr.writeNextUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_opOperandMPtr_writeBack (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readBack!, OpOperandMPtr.writeBack, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_opOperandMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readBack!, OpOperandMPtr.writeOwner, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_opOperandMPtr_writeValue (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readBack!, OpOperandMPtr.writeValue, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_opOperandMPtr_writeNextUse (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readOwner!, OpOperandMPtr.writeNextUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_opOperandMPtr_writeBack (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readOwner!, OpOperandMPtr.writeBack, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_opOperandMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readOwner!, OpOperandMPtr.writeOwner, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_opOperandMPtr_writeValue (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readOwner!, OpOperandMPtr.writeValue, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_opOperandMPtr_writeNextUse (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readValue!, OpOperandMPtr.writeNextUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_opOperandMPtr_writeBack (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readValue!, OpOperandMPtr.writeBack, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_opOperandMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readValue!, OpOperandMPtr.writeOwner, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_opOperandMPtr_writeValue (bo : Veir.BlockOperandPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_opOperand readValue!, OpOperandMPtr.writeValue, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockArgumentMPtr_writeType (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readNextUse!, BlockArgumentMPtr.writeType, bo, w2

/-! ## BlockOperandMPtr.readNextUse! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockArgumentMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readNextUse!, BlockArgumentMPtr.writeFirstUse, bo, w2

/-! ## BlockOperandMPtr.readNextUse! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockArgumentMPtr_writeIndex (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readNextUse!, BlockArgumentMPtr.writeIndex, bo, w2

/-! ## BlockOperandMPtr.readNextUse! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockArgumentMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readNextUse!, BlockArgumentMPtr.writeOwner, bo, w2

/-! ## BlockOperandMPtr.readBack! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockArgumentMPtr_writeType (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readBack!, BlockArgumentMPtr.writeType, bo, w2

/-! ## BlockOperandMPtr.readBack! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockArgumentMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readBack!, BlockArgumentMPtr.writeFirstUse, bo, w2

/-! ## BlockOperandMPtr.readBack! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockArgumentMPtr_writeIndex (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readBack!, BlockArgumentMPtr.writeIndex, bo, w2

/-! ## BlockOperandMPtr.readBack! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockArgumentMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readBack!, BlockArgumentMPtr.writeOwner, bo, w2

/-! ## BlockOperandMPtr.readOwner! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockArgumentMPtr_writeType (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readOwner!, BlockArgumentMPtr.writeType, bo, w2

/-! ## BlockOperandMPtr.readOwner! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockArgumentMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readOwner!, BlockArgumentMPtr.writeFirstUse, bo, w2

/-! ## BlockOperandMPtr.readOwner! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockArgumentMPtr_writeIndex (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readOwner!, BlockArgumentMPtr.writeIndex, bo, w2

/-! ## BlockOperandMPtr.readOwner! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockArgumentMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readOwner!, BlockArgumentMPtr.writeOwner, bo, w2

/-! ## BlockOperandMPtr.readValue! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockArgumentMPtr_writeType (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readValue!, BlockArgumentMPtr.writeType, bo, w2

/-! ## BlockOperandMPtr.readValue! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockArgumentMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readValue!, BlockArgumentMPtr.writeFirstUse, bo, w2

/-! ## BlockOperandMPtr.readValue! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockArgumentMPtr_writeIndex (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readValue!, BlockArgumentMPtr.writeIndex, bo, w2

/-! ## BlockOperandMPtr.readValue! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockArgumentMPtr_writeOwner (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_blockArg readValue!, BlockArgumentMPtr.writeOwner, bo, w2

/-! ## BlockOperandMPtr.readNextUse! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readNextUse!, BlockMPtr.writeFirstUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockMPtr_writePrev (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readNextUse!, BlockMPtr.writePrev, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockMPtr_writeNext (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readNextUse!, BlockMPtr.writeNext, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockMPtr_writeParent (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readNextUse!, BlockMPtr.writeParent, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockMPtr_writeFirstOp (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readNextUse!, BlockMPtr.writeFirstOp, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockMPtr_writeLastOp (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readNextUse!, BlockMPtr.writeLastOp, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_blockMPtr_writeNumArguments (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readNextUse!, BlockMPtr.writeNumArguments, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readBack!, BlockMPtr.writeFirstUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockMPtr_writePrev (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readBack!, BlockMPtr.writePrev, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockMPtr_writeNext (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readBack!, BlockMPtr.writeNext, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockMPtr_writeParent (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readBack!, BlockMPtr.writeParent, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockMPtr_writeFirstOp (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readBack!, BlockMPtr.writeFirstOp, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockMPtr_writeLastOp (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readBack!, BlockMPtr.writeLastOp, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readBack! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_blockMPtr_writeNumArguments (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readBack!, BlockMPtr.writeNumArguments, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readOwner!, BlockMPtr.writeFirstUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockMPtr_writePrev (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readOwner!, BlockMPtr.writePrev, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockMPtr_writeNext (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readOwner!, BlockMPtr.writeNext, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockMPtr_writeParent (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readOwner!, BlockMPtr.writeParent, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockMPtr_writeFirstOp (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readOwner!, BlockMPtr.writeFirstOp, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockMPtr_writeLastOp (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readOwner!, BlockMPtr.writeLastOp, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readOwner! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_blockMPtr_writeNumArguments (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readOwner!, BlockMPtr.writeNumArguments, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readValue!, BlockMPtr.writeFirstUse, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockMPtr_writePrev (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readValue!, BlockMPtr.writePrev, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockMPtr_writeNext (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readValue!, BlockMPtr.writeNext, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockMPtr_writeParent (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readValue!, BlockMPtr.writeParent, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockMPtr_writeFirstOp (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readValue!, BlockMPtr.writeFirstOp, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockMPtr_writeLastOp (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readValue!, BlockMPtr.writeLastOp, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readValue! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_blockMPtr_writeNumArguments (bo : Veir.BlockOperandPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_block readValue!, BlockMPtr.writeNumArguments, bo, w2, w2Ib

/-! ## BlockOperandMPtr.readNextUse! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_regionMPtr_writeFirstBlock (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readNextUse!, RegionMPtr.writeFirstBlock, bo, w2

/-! ## BlockOperandMPtr.readNextUse! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_regionMPtr_writeLastBlock (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readNextUse!, RegionMPtr.writeLastBlock, bo, w2

/-! ## BlockOperandMPtr.readNextUse! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_regionMPtr_writeParent (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readNextUse!, RegionMPtr.writeParent, bo, w2

/-! ## BlockOperandMPtr.readBack! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_regionMPtr_writeFirstBlock (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readBack!, RegionMPtr.writeFirstBlock, bo, w2

/-! ## BlockOperandMPtr.readBack! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_regionMPtr_writeLastBlock (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readBack!, RegionMPtr.writeLastBlock, bo, w2

/-! ## BlockOperandMPtr.readBack! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_regionMPtr_writeParent (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readBack!, RegionMPtr.writeParent, bo, w2

/-! ## BlockOperandMPtr.readOwner! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_regionMPtr_writeFirstBlock (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readOwner!, RegionMPtr.writeFirstBlock, bo, w2

/-! ## BlockOperandMPtr.readOwner! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_regionMPtr_writeLastBlock (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readOwner!, RegionMPtr.writeLastBlock, bo, w2

/-! ## BlockOperandMPtr.readOwner! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_regionMPtr_writeParent (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readOwner!, RegionMPtr.writeParent, bo, w2

/-! ## BlockOperandMPtr.readValue! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_regionMPtr_writeFirstBlock (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readValue!, RegionMPtr.writeFirstBlock, bo, w2

/-! ## BlockOperandMPtr.readValue! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_regionMPtr_writeLastBlock (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readValue!, RegionMPtr.writeLastBlock, bo, w2

/-! ## BlockOperandMPtr.readValue! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_regionMPtr_writeParent (bo : Veir.BlockOperandPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (boIb : bo.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  rw_bo_region readValue!, RegionMPtr.writeParent, bo, w2

/-! ## BlockOperandMPtr.readNextUse! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_valueImplMPtr_writeType (bo : Veir.BlockOperandPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readNextUse!, ValueImplMPtr.writeType, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNextUse!, ValueImplMPtr.writeType, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readBack! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_valueImplMPtr_writeType (bo : Veir.BlockOperandPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readBack!, ValueImplMPtr.writeType, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readBack!, ValueImplMPtr.writeType, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readOwner! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_valueImplMPtr_writeType (bo : Veir.BlockOperandPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeType, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeType, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readValue! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_valueImplMPtr_writeType (bo : Veir.BlockOperandPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (boIb : bo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readValue!, ValueImplMPtr.writeType, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readValue!, ValueImplMPtr.writeType, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readNextUse! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_valueImplMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readNextUse!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNextUse!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readBack! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_valueImplMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readBack!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readBack!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readOwner! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_valueImplMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readValue! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_valueImplMPtr_writeFirstUse (bo : Veir.BlockOperandPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readValue!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readValue!, ValueImplMPtr.writeFirstUse, layout_grind,
      BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readNextUse! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readNextUse!_opOperandPtrMPtr_write (bo : Veir.BlockOperandPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readNextUse! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readNextUse! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    have : opr.index < (opr.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readNextUse!, OpOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readNextUse!, OpOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNextUse!, OpOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readBack! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readBack!_opOperandPtrMPtr_write (bo : Veir.BlockOperandPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readBack! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readBack! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    have : opr.index < (opr.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readBack!, OpOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readBack!, OpOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readBack!, OpOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readOwner! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readOwner!_opOperandPtrMPtr_write (bo : Veir.BlockOperandPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readOwner! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readOwner! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    have : opr.index < (opr.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## BlockOperandMPtr.readValue! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem BlockOperandMPtr.readValue!_opOperandPtrMPtr_write (bo : Veir.BlockOperandPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (boIb : bo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.BlockOperandMPtr.readValue! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (bo.toM ctx.spec) =
    Buffed.BlockOperandMPtr.readValue! ctx.buf (bo.toM ctx.spec) := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
  have : bo.index < (bo.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation bo.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    have : opr.index < (opr.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readValue!, OpOperandPtrMPtr.write, layout_grind,
      BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
      OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation bo.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readValue!, OpOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation bo.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readValue!, OpOperandPtrMPtr.write, layout_grind,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
