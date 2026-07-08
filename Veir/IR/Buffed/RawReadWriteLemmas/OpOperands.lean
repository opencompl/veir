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

@[local ext, local grind ext]
theorem _root_.Veir.OpOperandPtr.ext (x y : OpOperandPtr) : x.op = y.op → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

/-! ## OpOperandMPtr.readNextUse! -/

@[layout_grind =]
theorem OpOperandMPtr.readNextUse!_opOperandMPtr_writeNextUse (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OpOperandMPtr.writeNextUse ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    if oo = ptr.spec then val.impl else Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readNextUse!, OpOperandMPtr.writeNextUse, oo, ptr

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_opOperandMPtr_writeBack (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OpOperandMPtr.writeBack ctx.buf ptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readNextUse!, OpOperandMPtr.writeBack, oo, ptr

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_opOperandMPtr_writeOwner (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OpOperandMPtr.writeOwner ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readNextUse!, OpOperandMPtr.writeOwner, oo, ptr

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_opOperandMPtr_writeValue (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OpOperandMPtr.writeValue ctx.buf ptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readNextUse!, OpOperandMPtr.writeValue, oo, ptr

/-! ## OpOperandMPtr.readBack! -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_opOperandMPtr_writeNextUse (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OpOperandMPtr.writeNextUse ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readBack!, OpOperandMPtr.writeNextUse, oo, ptr

@[layout_grind =]
theorem OpOperandMPtr.readBack!_opOperandMPtr_writeBack (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OpOperandMPtr.writeBack ctx.buf ptr.impl val h) (oo.toM ctx.spec) =
    if oo = ptr.spec then val else Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readBack!, OpOperandMPtr.writeBack, oo, ptr

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_opOperandMPtr_writeOwner (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OpOperandMPtr.writeOwner ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readBack!, OpOperandMPtr.writeOwner, oo, ptr

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_opOperandMPtr_writeValue (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OpOperandMPtr.writeValue ctx.buf ptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readBack!, OpOperandMPtr.writeValue, oo, ptr

/-! ## OpOperandMPtr.readOwner! -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_opOperandMPtr_writeNextUse (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OpOperandMPtr.writeNextUse ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readOwner!, OpOperandMPtr.writeNextUse, oo, ptr

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_opOperandMPtr_writeBack (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OpOperandMPtr.writeBack ctx.buf ptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readOwner!, OpOperandMPtr.writeBack, oo, ptr

@[layout_grind =]
theorem OpOperandMPtr.readOwner!_opOperandMPtr_writeOwner (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OpOperandMPtr.writeOwner ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    if oo = ptr.spec then val.impl else Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readOwner!, OpOperandMPtr.writeOwner, oo, ptr

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_opOperandMPtr_writeValue (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OpOperandMPtr.writeValue ctx.buf ptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readOwner!, OpOperandMPtr.writeValue, oo, ptr

/-! ## OpOperandMPtr.readValue! -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_opOperandMPtr_writeNextUse (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OpOperandMPtr.writeNextUse ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readValue!, OpOperandMPtr.writeNextUse, oo, ptr

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_opOperandMPtr_writeBack (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OpOperandMPtr.writeBack ctx.buf ptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readValue!, OpOperandMPtr.writeBack, oo, ptr

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_opOperandMPtr_writeOwner (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OpOperandMPtr.writeOwner ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readValue!, OpOperandMPtr.writeOwner, oo, ptr

@[layout_grind =]
theorem OpOperandMPtr.readValue!_opOperandMPtr_writeValue (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OpOperandMPtr.writeValue ctx.buf ptr.impl val h) (oo.toM ctx.spec) =
    if oo = ptr.spec then val else Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_oo readValue!, OpOperandMPtr.writeValue, oo, ptr

/-! ## OpOperandMPtr.readNextUse! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockOperandPtrMPtr_write (oo : Veir.OpOperandPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readNextUse!, BlockOperandPtrMPtr.write, layout_grind,
          OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
          BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
          IsIncludedI, IsDisjointI, Operation.ReprIndices]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readNextUse!, BlockOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]


/-! ## OpOperandMPtr.readBack! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockOperandPtrMPtr_write (oo : Veir.OpOperandPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readBack!, BlockOperandPtrMPtr.write, layout_grind,
        OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
        IsIncludedI, IsDisjointI, Operation.ReprIndices]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readBack!, BlockOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readOwner! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockOperandPtrMPtr_write (oo : Veir.OpOperandPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readOwner!, BlockOperandPtrMPtr.write, layout_grind,
        OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
        IsIncludedI, IsDisjointI, Operation.ReprIndices]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readOwner!, BlockOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readValue! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockOperandPtrMPtr_write (oo : Veir.OpOperandPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readValue!, BlockOperandPtrMPtr.write, layout_grind,
        OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
        BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
        IsIncludedI, IsDisjointI, Operation.ReprIndices]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readValue!, BlockOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readNextUse! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_operationMPtr_writeNext (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readNextUse!, OperationMPtr.writeNext, oo, op2

/-! ## OpOperandMPtr.readBack! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_operationMPtr_writeNext (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readBack!, OperationMPtr.writeNext, oo, op2

/-! ## OpOperandMPtr.readOwner! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_operationMPtr_writeNext (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readOwner!, OperationMPtr.writeNext, oo, op2

/-! ## OpOperandMPtr.readValue! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_operationMPtr_writeNext (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readValue!, OperationMPtr.writeNext, oo, op2

/-! ## OpOperandMPtr.readNextUse! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_operationMPtr_writeNumResults (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readNextUse!, OperationMPtr.writeNumResults, oo, op2

/-! ## OpOperandMPtr.readBack! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_operationMPtr_writeNumResults (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readBack!, OperationMPtr.writeNumResults, oo, op2

/-! ## OpOperandMPtr.readOwner! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_operationMPtr_writeNumResults (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readOwner!, OperationMPtr.writeNumResults, oo, op2

/-! ## OpOperandMPtr.readValue! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_operationMPtr_writeNumResults (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readValue!, OperationMPtr.writeNumResults, oo, op2

/-! ## OpOperandMPtr.readNextUse! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_operationMPtr_writeNumBlockOperands (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readNextUse!, OperationMPtr.writeNumBlockOperands, oo, op2

/-! ## OpOperandMPtr.readBack! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_operationMPtr_writeNumBlockOperands (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readBack!, OperationMPtr.writeNumBlockOperands, oo, op2

/-! ## OpOperandMPtr.readOwner! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_operationMPtr_writeNumBlockOperands (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readOwner!, OperationMPtr.writeNumBlockOperands, oo, op2

/-! ## OpOperandMPtr.readValue! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_operationMPtr_writeNumBlockOperands (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readValue!, OperationMPtr.writeNumBlockOperands, oo, op2

/-! ## OpOperandMPtr.readNextUse! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_operationMPtr_writeNumRegions (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readNextUse!, OperationMPtr.writeNumRegions, oo, op2

/-! ## OpOperandMPtr.readBack! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_operationMPtr_writeNumRegions (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readBack!, OperationMPtr.writeNumRegions, oo, op2

/-! ## OpOperandMPtr.readOwner! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_operationMPtr_writeNumRegions (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readOwner!, OperationMPtr.writeNumRegions, oo, op2

/-! ## OpOperandMPtr.readValue! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_operationMPtr_writeNumRegions (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readValue!, OperationMPtr.writeNumRegions, oo, op2

/-! ## OpOperandMPtr.readNextUse! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_operationMPtr_writeNumOperands (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readNextUse!, OperationMPtr.writeNumOperands, oo, op2

/-! ## OpOperandMPtr.readBack! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_operationMPtr_writeNumOperands (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readBack!, OperationMPtr.writeNumOperands, oo, op2

/-! ## OpOperandMPtr.readOwner! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_operationMPtr_writeNumOperands (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readOwner!, OperationMPtr.writeNumOperands, oo, op2

/-! ## OpOperandMPtr.readValue! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_operationMPtr_writeNumOperands (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readValue!, OperationMPtr.writeNumOperands, oo, op2

/-! ## OpOperandMPtr.readNextUse! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_operationMPtr_writeAttrs (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readNextUse!, OperationMPtr.writeAttrs, oo, op2

/-! ## OpOperandMPtr.readBack! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_operationMPtr_writeAttrs (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readBack!, OperationMPtr.writeAttrs, oo, op2

/-! ## OpOperandMPtr.readOwner! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_operationMPtr_writeAttrs (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readOwner!, OperationMPtr.writeAttrs, oo, op2

/-! ## OpOperandMPtr.readValue! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_operationMPtr_writeAttrs (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readValue!, OperationMPtr.writeAttrs, oo, op2

/-! ## OpOperandMPtr.readNextUse! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_operationMPtr_writeOpType (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readNextUse!, OperationMPtr.writeOpType, oo, op2

/-! ## OpOperandMPtr.readBack! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_operationMPtr_writeOpType (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readBack!, OperationMPtr.writeOpType, oo, op2

/-! ## OpOperandMPtr.readOwner! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_operationMPtr_writeOpType (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readOwner!, OperationMPtr.writeOpType, oo, op2

/-! ## OpOperandMPtr.readValue! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_operationMPtr_writeOpType (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readValue!, OperationMPtr.writeOpType, oo, op2

/-! ## OpOperandMPtr.readNextUse! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_operationMPtr_writePrev (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readNextUse!, OperationMPtr.writePrev, oo, op2

/-! ## OpOperandMPtr.readBack! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_operationMPtr_writePrev (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readBack!, OperationMPtr.writePrev, oo, op2

/-! ## OpOperandMPtr.readOwner! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_operationMPtr_writePrev (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readOwner!, OperationMPtr.writePrev, oo, op2

/-! ## OpOperandMPtr.readValue! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_operationMPtr_writePrev (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readValue!, OperationMPtr.writePrev, oo, op2

/-! ## OpOperandMPtr.readNextUse! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_operationMPtr_writeParent (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readNextUse!, OperationMPtr.writeParent, oo, op2

/-! ## OpOperandMPtr.readBack! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_operationMPtr_writeParent (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readBack!, OperationMPtr.writeParent, oo, op2

/-! ## OpOperandMPtr.readOwner! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_operationMPtr_writeParent (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readOwner!, OperationMPtr.writeParent, oo, op2

/-! ## OpOperandMPtr.readValue! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_operationMPtr_writeParent (oo : Veir.OpOperandPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opScalar readValue!, OperationMPtr.writeParent, oo, op2

/-! ## OpOperandMPtr.readNextUse! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeFirstUse ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readNextUse!, BlockMPtr.writeFirstUse, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockMPtr_writePrev (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockMPtr.writePrev ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readNextUse!, BlockMPtr.writePrev, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockMPtr_writeNext (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeNext ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readNextUse!, BlockMPtr.writeNext, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockMPtr_writeParent (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeParent ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readNextUse!, BlockMPtr.writeParent, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockMPtr_writeFirstOp (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeFirstOp ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readNextUse!, BlockMPtr.writeFirstOp, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockMPtr_writeLastOp (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeLastOp ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readNextUse!, BlockMPtr.writeLastOp, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockMPtr_writeNumArguments (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockMPtr.writeNumArguments ctx.buf bl2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readNextUse!, BlockMPtr.writeNumArguments, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readBack! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockMPtr.writeFirstUse ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readBack!, BlockMPtr.writeFirstUse, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readBack! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockMPtr_writePrev (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockMPtr.writePrev ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readBack!, BlockMPtr.writePrev, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readBack! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockMPtr_writeNext (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockMPtr.writeNext ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readBack!, BlockMPtr.writeNext, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readBack! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockMPtr_writeParent (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockMPtr.writeParent ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readBack!, BlockMPtr.writeParent, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readBack! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockMPtr_writeFirstOp (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockMPtr.writeFirstOp ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readBack!, BlockMPtr.writeFirstOp, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readBack! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockMPtr_writeLastOp (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockMPtr.writeLastOp ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readBack!, BlockMPtr.writeLastOp, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readBack! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockMPtr_writeNumArguments (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockMPtr.writeNumArguments ctx.buf bl2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readBack!, BlockMPtr.writeNumArguments, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readOwner! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockMPtr.writeFirstUse ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readOwner!, BlockMPtr.writeFirstUse, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readOwner! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockMPtr_writePrev (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockMPtr.writePrev ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readOwner!, BlockMPtr.writePrev, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readOwner! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockMPtr_writeNext (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockMPtr.writeNext ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readOwner!, BlockMPtr.writeNext, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readOwner! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockMPtr_writeParent (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockMPtr.writeParent ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readOwner!, BlockMPtr.writeParent, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readOwner! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockMPtr_writeFirstOp (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockMPtr.writeFirstOp ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readOwner!, BlockMPtr.writeFirstOp, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readOwner! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockMPtr_writeLastOp (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockMPtr.writeLastOp ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readOwner!, BlockMPtr.writeLastOp, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readOwner! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockMPtr_writeNumArguments (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockMPtr.writeNumArguments ctx.buf bl2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readOwner!, BlockMPtr.writeNumArguments, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readValue! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockMPtr.writeFirstUse ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readValue!, BlockMPtr.writeFirstUse, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readValue! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockMPtr_writePrev (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockMPtr.writePrev ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readValue!, BlockMPtr.writePrev, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readValue! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockMPtr_writeNext (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockMPtr.writeNext ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readValue!, BlockMPtr.writeNext, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readValue! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockMPtr_writeParent (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockMPtr.writeParent ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readValue!, BlockMPtr.writeParent, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readValue! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockMPtr_writeFirstOp (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockMPtr.writeFirstOp ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readValue!, BlockMPtr.writeFirstOp, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readValue! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockMPtr_writeLastOp (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockMPtr.writeLastOp ctx.buf bl2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readValue!, BlockMPtr.writeLastOp, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readValue! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockMPtr_writeNumArguments (oo : Veir.OpOperandPtr) (bl2 : Sim.BlockPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (bl2Ib : bl2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockMPtr.writeNumArguments ctx.buf bl2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_block readValue!, BlockMPtr.writeNumArguments, oo, bl2, bl2Ib

/-! ## OpOperandMPtr.readNextUse! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_regionMPtr_writeFirstBlock (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.RegionMPtr.writeFirstBlock ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readNextUse!, RegionMPtr.writeFirstBlock, oo, rg2

/-! ## OpOperandMPtr.readNextUse! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_regionMPtr_writeLastBlock (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.RegionMPtr.writeLastBlock ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readNextUse!, RegionMPtr.writeLastBlock, oo, rg2

/-! ## OpOperandMPtr.readNextUse! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_regionMPtr_writeParent (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.RegionMPtr.writeParent ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readNextUse!, RegionMPtr.writeParent, oo, rg2

/-! ## OpOperandMPtr.readBack! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_regionMPtr_writeFirstBlock (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.RegionMPtr.writeFirstBlock ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readBack!, RegionMPtr.writeFirstBlock, oo, rg2

/-! ## OpOperandMPtr.readBack! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_regionMPtr_writeLastBlock (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.RegionMPtr.writeLastBlock ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readBack!, RegionMPtr.writeLastBlock, oo, rg2

/-! ## OpOperandMPtr.readBack! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_regionMPtr_writeParent (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.RegionMPtr.writeParent ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readBack!, RegionMPtr.writeParent, oo, rg2

/-! ## OpOperandMPtr.readOwner! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_regionMPtr_writeFirstBlock (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.RegionMPtr.writeFirstBlock ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readOwner!, RegionMPtr.writeFirstBlock, oo, rg2

/-! ## OpOperandMPtr.readOwner! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_regionMPtr_writeLastBlock (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.RegionMPtr.writeLastBlock ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readOwner!, RegionMPtr.writeLastBlock, oo, rg2

/-! ## OpOperandMPtr.readOwner! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_regionMPtr_writeParent (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.RegionMPtr.writeParent ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readOwner!, RegionMPtr.writeParent, oo, rg2

/-! ## OpOperandMPtr.readValue! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_regionMPtr_writeFirstBlock (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.RegionMPtr.writeFirstBlock ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readValue!, RegionMPtr.writeFirstBlock, oo, rg2

/-! ## OpOperandMPtr.readValue! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_regionMPtr_writeLastBlock (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.RegionMPtr.writeLastBlock ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readValue!, RegionMPtr.writeLastBlock, oo, rg2

/-! ## OpOperandMPtr.readValue! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_regionMPtr_writeParent (oo : Veir.OpOperandPtr) (rg2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (ooIb : oo.InBounds ctx.spec) (rg2Ib : rg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.RegionMPtr.writeParent ctx.buf rg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_region readValue!, RegionMPtr.writeParent, oo, rg2

/-! ## OpOperandMPtr.readNextUse! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockArgumentMPtr_writeType (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readNextUse!, BlockArgumentMPtr.writeType, oo, arg2

/-! ## OpOperandMPtr.readNextUse! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockArgumentMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readNextUse!, BlockArgumentMPtr.writeFirstUse, oo, arg2

/-! ## OpOperandMPtr.readNextUse! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockArgumentMPtr_writeIndex (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readNextUse!, BlockArgumentMPtr.writeIndex, oo, arg2

/-! ## OpOperandMPtr.readNextUse! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockArgumentMPtr_writeOwner (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readNextUse!, BlockArgumentMPtr.writeOwner, oo, arg2

/-! ## OpOperandMPtr.readBack! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockArgumentMPtr_writeType (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readBack!, BlockArgumentMPtr.writeType, oo, arg2

/-! ## OpOperandMPtr.readBack! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockArgumentMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readBack!, BlockArgumentMPtr.writeFirstUse, oo, arg2

/-! ## OpOperandMPtr.readBack! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockArgumentMPtr_writeIndex (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readBack!, BlockArgumentMPtr.writeIndex, oo, arg2

/-! ## OpOperandMPtr.readBack! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockArgumentMPtr_writeOwner (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readBack!, BlockArgumentMPtr.writeOwner, oo, arg2

/-! ## OpOperandMPtr.readOwner! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockArgumentMPtr_writeType (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readOwner!, BlockArgumentMPtr.writeType, oo, arg2

/-! ## OpOperandMPtr.readOwner! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockArgumentMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readOwner!, BlockArgumentMPtr.writeFirstUse, oo, arg2

/-! ## OpOperandMPtr.readOwner! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockArgumentMPtr_writeIndex (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readOwner!, BlockArgumentMPtr.writeIndex, oo, arg2

/-! ## OpOperandMPtr.readOwner! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockArgumentMPtr_writeOwner (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readOwner!, BlockArgumentMPtr.writeOwner, oo, arg2

/-! ## OpOperandMPtr.readValue! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockArgumentMPtr_writeType (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockArgumentMPtr.writeType ctx.buf arg2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readValue!, BlockArgumentMPtr.writeType, oo, arg2

/-! ## OpOperandMPtr.readValue! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockArgumentMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf arg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readValue!, BlockArgumentMPtr.writeFirstUse, oo, arg2

/-! ## OpOperandMPtr.readValue! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockArgumentMPtr_writeIndex (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf arg2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readValue!, BlockArgumentMPtr.writeIndex, oo, arg2

/-! ## OpOperandMPtr.readValue! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockArgumentMPtr_writeOwner (oo : Veir.OpOperandPtr) (arg2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (ooIb : oo.InBounds ctx.spec) (arg2Ib : arg2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf arg2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockArg readValue!, BlockArgumentMPtr.writeOwner, oo, arg2

/-! ## OpOperandMPtr.readNextUse! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_opResultMPtr_writeType (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OpResultMPtr.writeType ctx.buf res2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readNextUse!, OpResultMPtr.writeType, oo, res2, res2Ib

/-! ## OpOperandMPtr.readNextUse! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_opResultMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readNextUse!, OpResultMPtr.writeFirstUse, oo, res2, res2Ib

/-! ## OpOperandMPtr.readNextUse! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_opResultMPtr_writeIndex (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OpResultMPtr.writeIndex ctx.buf res2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readNextUse!, OpResultMPtr.writeIndex, oo, res2, res2Ib

/-! ## OpOperandMPtr.readNextUse! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_opResultMPtr_writeOwner (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OpResultMPtr.writeOwner ctx.buf res2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readNextUse!, OpResultMPtr.writeOwner, oo, res2, res2Ib

/-! ## OpOperandMPtr.readBack! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_opResultMPtr_writeType (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OpResultMPtr.writeType ctx.buf res2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readBack!, OpResultMPtr.writeType, oo, res2, res2Ib

/-! ## OpOperandMPtr.readBack! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_opResultMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readBack!, OpResultMPtr.writeFirstUse, oo, res2, res2Ib

/-! ## OpOperandMPtr.readBack! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_opResultMPtr_writeIndex (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OpResultMPtr.writeIndex ctx.buf res2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readBack!, OpResultMPtr.writeIndex, oo, res2, res2Ib

/-! ## OpOperandMPtr.readBack! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_opResultMPtr_writeOwner (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OpResultMPtr.writeOwner ctx.buf res2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readBack!, OpResultMPtr.writeOwner, oo, res2, res2Ib

/-! ## OpOperandMPtr.readOwner! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_opResultMPtr_writeType (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OpResultMPtr.writeType ctx.buf res2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readOwner!, OpResultMPtr.writeType, oo, res2, res2Ib

/-! ## OpOperandMPtr.readOwner! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_opResultMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readOwner!, OpResultMPtr.writeFirstUse, oo, res2, res2Ib

/-! ## OpOperandMPtr.readOwner! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_opResultMPtr_writeIndex (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OpResultMPtr.writeIndex ctx.buf res2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readOwner!, OpResultMPtr.writeIndex, oo, res2, res2Ib

/-! ## OpOperandMPtr.readOwner! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_opResultMPtr_writeOwner (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OpResultMPtr.writeOwner ctx.buf res2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readOwner!, OpResultMPtr.writeOwner, oo, res2, res2Ib

/-! ## OpOperandMPtr.readValue! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_opResultMPtr_writeType (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OpResultMPtr.writeType ctx.buf res2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readValue!, OpResultMPtr.writeType, oo, res2, res2Ib

/-! ## OpOperandMPtr.readValue! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_opResultMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OpResultMPtr.writeFirstUse ctx.buf res2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readValue!, OpResultMPtr.writeFirstUse, oo, res2, res2Ib

/-! ## OpOperandMPtr.readValue! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_opResultMPtr_writeIndex (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OpResultMPtr.writeIndex ctx.buf res2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readValue!, OpResultMPtr.writeIndex, oo, res2, res2Ib

/-! ## OpOperandMPtr.readValue! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_opResultMPtr_writeOwner (oo : Veir.OpOperandPtr) (res2 : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (res2Ib : res2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OpResultMPtr.writeOwner ctx.buf res2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_opResult readValue!, OpResultMPtr.writeOwner, oo, res2, res2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockOperandMPtr_writeNextUse (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readNextUse!, BlockOperandMPtr.writeNextUse, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockOperandMPtr_writeBack (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockOperandMPtr.writeBack ctx.buf bo2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readNextUse!, BlockOperandMPtr.writeBack, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockOperandMPtr_writeOwner (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockOperandMPtr.writeOwner ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readNextUse!, BlockOperandMPtr.writeOwner, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readNextUse! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_blockOperandMPtr_writeValue (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.BlockOperandMPtr.writeValue ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readNextUse!, BlockOperandMPtr.writeValue, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readBack! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockOperandMPtr_writeNextUse (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readBack!, BlockOperandMPtr.writeNextUse, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readBack! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockOperandMPtr_writeBack (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockOperandMPtr.writeBack ctx.buf bo2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readBack!, BlockOperandMPtr.writeBack, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readBack! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockOperandMPtr_writeOwner (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockOperandMPtr.writeOwner ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readBack!, BlockOperandMPtr.writeOwner, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readBack! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_blockOperandMPtr_writeValue (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.BlockOperandMPtr.writeValue ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readBack!, BlockOperandMPtr.writeValue, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readOwner! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockOperandMPtr_writeNextUse (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readOwner!, BlockOperandMPtr.writeNextUse, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readOwner! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockOperandMPtr_writeBack (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockOperandMPtr.writeBack ctx.buf bo2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readOwner!, BlockOperandMPtr.writeBack, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readOwner! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockOperandMPtr_writeOwner (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockOperandMPtr.writeOwner ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readOwner!, BlockOperandMPtr.writeOwner, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readOwner! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_blockOperandMPtr_writeValue (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.BlockOperandMPtr.writeValue ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readOwner!, BlockOperandMPtr.writeValue, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readValue! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockOperandMPtr_writeNextUse (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readValue!, BlockOperandMPtr.writeNextUse, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readValue! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockOperandMPtr_writeBack (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockOperandMPtr.writeBack ctx.buf bo2.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readValue!, BlockOperandMPtr.writeBack, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readValue! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockOperandMPtr_writeOwner (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockOperandMPtr.writeOwner ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readValue!, BlockOperandMPtr.writeOwner, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readValue! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_blockOperandMPtr_writeValue (oo : Veir.OpOperandPtr) (bo2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (ooIb : oo.InBounds ctx.spec) (bo2Ib : bo2.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.BlockOperandMPtr.writeValue ctx.buf bo2.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  rw_oo_blockOperand readValue!, BlockOperandMPtr.writeValue, oo, bo2, bo2Ib

/-! ## OpOperandMPtr.readNextUse! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_valueImplMPtr_writeType (oo : Veir.OpOperandPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readNextUse!, ValueImplMPtr.writeType, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNextUse!, ValueImplMPtr.writeType, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readBack! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_valueImplMPtr_writeType (oo : Veir.OpOperandPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readBack!, ValueImplMPtr.writeType, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readBack!, ValueImplMPtr.writeType, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readOwner! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_valueImplMPtr_writeType (oo : Veir.OpOperandPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeType, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeType, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readValue! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_valueImplMPtr_writeType (oo : Veir.OpOperandPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (ooIb : oo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readValue!, ValueImplMPtr.writeType, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readValue!, ValueImplMPtr.writeType, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readNextUse! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readNextUse!_valueImplMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readNextUse!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readNextUse!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readBack! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_valueImplMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readBack!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readBack!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readOwner! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_valueImplMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readValue! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_valueImplMPtr_writeFirstUse (oo : Veir.OpOperandPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : vptr.spec with res | arg
  · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hsim := @Sim.OpResultPtr.after_lt_ctx
    grind (splits := 20) [readValue!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readValue!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]


/-! ## OpOperandMPtr.readNextUse! after OpOperandPtrMPtr.write -/

@[layout_grind =]
theorem OpOperandMPtr.readNextUse!_opOperandPtrMPtr_write (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readNextUse! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    if ptr.spec = .operandNextUse oo then val.impl
    else Buffed.OpOperandMPtr.readNextUse! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have : opr.index < (opr.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    by_cases ptr.spec = .operandNextUse oo
    · grind (splits := 20) [readNextUse!, OpOperandPtrMPtr.write, layout_grind,
        OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
        Operation.ReprIndices, IsIncludedI, IsDisjointI]
    · have : oo ≠ opr := by grind
      grind (splits := 20) [readNextUse!, OpOperandPtrMPtr.write, layout_grind,
        OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
        Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readNextUse!, OpOperandPtrMPtr.write, layout_grind,
        OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readNextUse!, OpOperandPtrMPtr.write, layout_grind,
        OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readBack! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readBack!_opOperandPtrMPtr_write (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readBack! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readBack! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have : opr.index < (opr.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readBack!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readBack!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readBack!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readOwner! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readOwner!_opOperandPtrMPtr_write (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readOwner! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readOwner! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have : opr.index < (opr.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpOperandMPtr.readValue! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpOperandMPtr.readValue!_opOperandPtrMPtr_write (oo : Veir.OpOperandPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (ooIb : oo.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpOperandMPtr.readValue! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (oo.toM ctx.spec) =
    Buffed.OpOperandMPtr.readValue! ctx.buf (oo.toM ctx.spec) := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) oo (by grind)
  have : oo.index < (oo.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  · have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation oo.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have : opr.index < (opr.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
    grind (splits := 20) [readValue!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      Operation.ReprIndices, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res | arg
    · have hdisj := ctx.sim.disjoint_allocs (.operation res.op) (.operation oo.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
      have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
      have hsim := @Sim.OpResultPtr.after_lt_ctx
      grind (splits := 20) [readValue!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    · have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation oo.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readValue!, OpOperandPtrMPtr.write, layout_grind,
      OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]


end read_write

end Veir.Buffed
