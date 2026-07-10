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
theorem _root_.Veir.OpResultPtr.ext (x y : OpResultPtr) : x.op = y.op → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

/-! ## OpResultMPtr.readType! -/

@[layout_grind =]
theorem OpResultMPtr.readType!_opResultMPtr_writeType (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpResultMPtr.writeType ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    if res = ptr.spec then val else Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readType!, OpResultMPtr.writeType, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readType!, OpResultMPtr.writeFirstUse, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opResultMPtr_writeIndex (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpResultMPtr.writeIndex ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readType!, OpResultMPtr.writeIndex, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readType!, OpResultMPtr.writeOwner, res, ptr

/-! ## OpResultMPtr.readFirstUse! -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_opResultMPtr_writeType (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpResultMPtr.writeType ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readFirstUse!, OpResultMPtr.writeType, res, ptr

@[layout_grind =]
theorem OpResultMPtr.readFirstUse!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    if res = ptr.spec then val.impl else Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readFirstUse!, OpResultMPtr.writeFirstUse, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_opResultMPtr_writeIndex (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpResultMPtr.writeIndex ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readFirstUse!, OpResultMPtr.writeIndex, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readFirstUse!, OpResultMPtr.writeOwner, res, ptr

/-! ## OpResultMPtr.readIndex! -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opResultMPtr_writeType (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpResultMPtr.writeType ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readIndex!, OpResultMPtr.writeType, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readIndex!, OpResultMPtr.writeFirstUse, res, ptr

@[layout_grind =]
theorem OpResultMPtr.readIndex!_opResultMPtr_writeIndex (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpResultMPtr.writeIndex ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    if res = ptr.spec then val else Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readIndex!, OpResultMPtr.writeIndex, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readIndex!, OpResultMPtr.writeOwner, res, ptr

/-! ## OpResultMPtr.readOwner! -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_opResultMPtr_writeType (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpResultMPtr.writeType ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readOwner!, OpResultMPtr.writeType, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readOwner!, OpResultMPtr.writeFirstUse, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_opResultMPtr_writeIndex (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpResultMPtr.writeIndex ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readOwner!, OpResultMPtr.writeIndex, res, ptr

@[layout_grind =]
theorem OpResultMPtr.readOwner!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    if res = ptr.spec then val.impl else Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readOwner!, OpResultMPtr.writeOwner, res, ptr

/-! ## OpResultMPtr.readType! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation res.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    grind (splits := 20) [readType!, BlockOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat,
        IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation res.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readType!, BlockOperandPtrMPtr.write, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readFirstUse! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation res.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat,
        IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation res.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readFirstUse!, BlockOperandPtrMPtr.write, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readIndex! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation res.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    grind (splits := 20) [readIndex!, BlockOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat,
        IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation res.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readIndex!, BlockOperandPtrMPtr.write, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readOwner! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation res.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    grind (splits := 20) [readOwner!, BlockOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat,
        IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation res.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readOwner!, BlockOperandPtrMPtr.write, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]


/-! ## OpResultMPtr.readType! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_operationMPtr_writeNext (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readType!, OperationMPtr.writeNext, res, op2

/-! ## OpResultMPtr.readFirstUse! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_operationMPtr_writeNext (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readFirstUse!, OperationMPtr.writeNext, res, op2

/-! ## OpResultMPtr.readIndex! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_operationMPtr_writeNext (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readIndex!, OperationMPtr.writeNext, res, op2

/-! ## OpResultMPtr.readOwner! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_operationMPtr_writeNext (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readOwner!, OperationMPtr.writeNext, res, op2

/-! ## OpResultMPtr.readType! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_operationMPtr_writeNumResults (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readType!, OperationMPtr.writeNumResults, res, op2

/-! ## OpResultMPtr.readFirstUse! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_operationMPtr_writeNumResults (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readFirstUse!, OperationMPtr.writeNumResults, res, op2

/-! ## OpResultMPtr.readIndex! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_operationMPtr_writeNumResults (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readIndex!, OperationMPtr.writeNumResults, res, op2

/-! ## OpResultMPtr.readOwner! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_operationMPtr_writeNumResults (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readOwner!, OperationMPtr.writeNumResults, res, op2

/-! ## OpResultMPtr.readType! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_operationMPtr_writeNumBlockOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readType!, OperationMPtr.writeNumBlockOperands, res, op2

/-! ## OpResultMPtr.readFirstUse! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_operationMPtr_writeNumBlockOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readFirstUse!, OperationMPtr.writeNumBlockOperands, res, op2

/-! ## OpResultMPtr.readIndex! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_operationMPtr_writeNumBlockOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readIndex!, OperationMPtr.writeNumBlockOperands, res, op2

/-! ## OpResultMPtr.readOwner! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_operationMPtr_writeNumBlockOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readOwner!, OperationMPtr.writeNumBlockOperands, res, op2

/-! ## OpResultMPtr.readType! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_operationMPtr_writeNumRegions (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readType!, OperationMPtr.writeNumRegions, res, op2

/-! ## OpResultMPtr.readFirstUse! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_operationMPtr_writeNumRegions (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readFirstUse!, OperationMPtr.writeNumRegions, res, op2

/-! ## OpResultMPtr.readIndex! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_operationMPtr_writeNumRegions (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readIndex!, OperationMPtr.writeNumRegions, res, op2

/-! ## OpResultMPtr.readOwner! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_operationMPtr_writeNumRegions (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readOwner!, OperationMPtr.writeNumRegions, res, op2

/-! ## OpResultMPtr.readType! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_operationMPtr_writeNumOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readType!, OperationMPtr.writeNumOperands, res, op2

/-! ## OpResultMPtr.readFirstUse! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_operationMPtr_writeNumOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readFirstUse!, OperationMPtr.writeNumOperands, res, op2

/-! ## OpResultMPtr.readIndex! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_operationMPtr_writeNumOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readIndex!, OperationMPtr.writeNumOperands, res, op2

/-! ## OpResultMPtr.readOwner! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_operationMPtr_writeNumOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readOwner!, OperationMPtr.writeNumOperands, res, op2

/-! ## OpResultMPtr.readType! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_operationMPtr_writeAttrs (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readType!, OperationMPtr.writeAttrs, res, op2

/-! ## OpResultMPtr.readFirstUse! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_operationMPtr_writeAttrs (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readFirstUse!, OperationMPtr.writeAttrs, res, op2

/-! ## OpResultMPtr.readIndex! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_operationMPtr_writeAttrs (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readIndex!, OperationMPtr.writeAttrs, res, op2

/-! ## OpResultMPtr.readOwner! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_operationMPtr_writeAttrs (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readOwner!, OperationMPtr.writeAttrs, res, op2

/-! ## OpResultMPtr.readType! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_operationMPtr_writeOpType (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readType!, OperationMPtr.writeOpType, res, op2

/-! ## OpResultMPtr.readFirstUse! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_operationMPtr_writeOpType (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readFirstUse!, OperationMPtr.writeOpType, res, op2

/-! ## OpResultMPtr.readIndex! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_operationMPtr_writeOpType (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readIndex!, OperationMPtr.writeOpType, res, op2

/-! ## OpResultMPtr.readOwner! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_operationMPtr_writeOpType (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readOwner!, OperationMPtr.writeOpType, res, op2

/-! ## OpResultMPtr.readType! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_operationMPtr_writePrev (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readType!, OperationMPtr.writePrev, res, op2

/-! ## OpResultMPtr.readFirstUse! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_operationMPtr_writePrev (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readFirstUse!, OperationMPtr.writePrev, res, op2

/-! ## OpResultMPtr.readIndex! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_operationMPtr_writePrev (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readIndex!, OperationMPtr.writePrev, res, op2

/-! ## OpResultMPtr.readOwner! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_operationMPtr_writePrev (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readOwner!, OperationMPtr.writePrev, res, op2

/-! ## OpResultMPtr.readType! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_operationMPtr_writeParent (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readType!, OperationMPtr.writeParent, res, op2

/-! ## OpResultMPtr.readFirstUse! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_operationMPtr_writeParent (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readFirstUse!, OperationMPtr.writeParent, res, op2

/-! ## OpResultMPtr.readIndex! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_operationMPtr_writeParent (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readIndex!, OperationMPtr.writeParent, res, op2

/-! ## OpResultMPtr.readOwner! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_operationMPtr_writeParent (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readOwner!, OperationMPtr.writeParent, res, op2

/-! ## OpResultMPtr.readType! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readType!, BlockMPtr.writeFirstUse, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockMPtr_writePrev (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readType!, BlockMPtr.writePrev, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockMPtr_writeNext (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readType!, BlockMPtr.writeNext, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readType!, BlockMPtr.writeParent, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockMPtr_writeFirstOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readType!, BlockMPtr.writeFirstOp, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockMPtr_writeLastOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readType!, BlockMPtr.writeLastOp, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockMPtr_writeNumArguments (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readType!, BlockMPtr.writeNumArguments, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readFirstUse!, BlockMPtr.writeFirstUse, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockMPtr_writePrev (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readFirstUse!, BlockMPtr.writePrev, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockMPtr_writeNext (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readFirstUse!, BlockMPtr.writeNext, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readFirstUse!, BlockMPtr.writeParent, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockMPtr_writeFirstOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readFirstUse!, BlockMPtr.writeFirstOp, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockMPtr_writeLastOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readFirstUse!, BlockMPtr.writeLastOp, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockMPtr_writeNumArguments (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readFirstUse!, BlockMPtr.writeNumArguments, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readIndex!, BlockMPtr.writeFirstUse, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockMPtr_writePrev (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readIndex!, BlockMPtr.writePrev, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockMPtr_writeNext (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readIndex!, BlockMPtr.writeNext, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readIndex!, BlockMPtr.writeParent, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockMPtr_writeFirstOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readIndex!, BlockMPtr.writeFirstOp, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockMPtr_writeLastOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readIndex!, BlockMPtr.writeLastOp, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockMPtr_writeNumArguments (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readIndex!, BlockMPtr.writeNumArguments, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readOwner!, BlockMPtr.writeFirstUse, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockMPtr_writePrev (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readOwner!, BlockMPtr.writePrev, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockMPtr_writeNext (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readOwner!, BlockMPtr.writeNext, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readOwner!, BlockMPtr.writeParent, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockMPtr_writeFirstOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readOwner!, BlockMPtr.writeFirstOp, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockMPtr_writeLastOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readOwner!, BlockMPtr.writeLastOp, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockMPtr_writeNumArguments (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readOwner!, BlockMPtr.writeNumArguments, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_regionMPtr_writeFirstBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readType!, RegionMPtr.writeFirstBlock, res, w2

/-! ## OpResultMPtr.readType! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_regionMPtr_writeLastBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readType!, RegionMPtr.writeLastBlock, res, w2

/-! ## OpResultMPtr.readType! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_regionMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readType!, RegionMPtr.writeParent, res, w2

/-! ## OpResultMPtr.readFirstUse! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_regionMPtr_writeFirstBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readFirstUse!, RegionMPtr.writeFirstBlock, res, w2

/-! ## OpResultMPtr.readFirstUse! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_regionMPtr_writeLastBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readFirstUse!, RegionMPtr.writeLastBlock, res, w2

/-! ## OpResultMPtr.readFirstUse! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_regionMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readFirstUse!, RegionMPtr.writeParent, res, w2

/-! ## OpResultMPtr.readIndex! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_regionMPtr_writeFirstBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readIndex!, RegionMPtr.writeFirstBlock, res, w2

/-! ## OpResultMPtr.readIndex! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_regionMPtr_writeLastBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readIndex!, RegionMPtr.writeLastBlock, res, w2

/-! ## OpResultMPtr.readIndex! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_regionMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readIndex!, RegionMPtr.writeParent, res, w2

/-! ## OpResultMPtr.readOwner! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_regionMPtr_writeFirstBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readOwner!, RegionMPtr.writeFirstBlock, res, w2

/-! ## OpResultMPtr.readOwner! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_regionMPtr_writeLastBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readOwner!, RegionMPtr.writeLastBlock, res, w2

/-! ## OpResultMPtr.readOwner! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_regionMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readOwner!, RegionMPtr.writeParent, res, w2

/-! ## OpResultMPtr.readType! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockArgumentMPtr_writeType (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readType!, BlockArgumentMPtr.writeType, res, w2

/-! ## OpResultMPtr.readType! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockArgumentMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readType!, BlockArgumentMPtr.writeFirstUse, res, w2

/-! ## OpResultMPtr.readType! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockArgumentMPtr_writeIndex (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readType!, BlockArgumentMPtr.writeIndex, res, w2

/-! ## OpResultMPtr.readType! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockArgumentMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readType!, BlockArgumentMPtr.writeOwner, res, w2

/-! ## OpResultMPtr.readFirstUse! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockArgumentMPtr_writeType (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readFirstUse!, BlockArgumentMPtr.writeType, res, w2

/-! ## OpResultMPtr.readFirstUse! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockArgumentMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readFirstUse!, BlockArgumentMPtr.writeFirstUse, res, w2

/-! ## OpResultMPtr.readFirstUse! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockArgumentMPtr_writeIndex (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readFirstUse!, BlockArgumentMPtr.writeIndex, res, w2

/-! ## OpResultMPtr.readFirstUse! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockArgumentMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readFirstUse!, BlockArgumentMPtr.writeOwner, res, w2

/-! ## OpResultMPtr.readIndex! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockArgumentMPtr_writeType (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readIndex!, BlockArgumentMPtr.writeType, res, w2

/-! ## OpResultMPtr.readIndex! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockArgumentMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readIndex!, BlockArgumentMPtr.writeFirstUse, res, w2

/-! ## OpResultMPtr.readIndex! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockArgumentMPtr_writeIndex (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readIndex!, BlockArgumentMPtr.writeIndex, res, w2

/-! ## OpResultMPtr.readIndex! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockArgumentMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readIndex!, BlockArgumentMPtr.writeOwner, res, w2

/-! ## OpResultMPtr.readOwner! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockArgumentMPtr_writeType (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readOwner!, BlockArgumentMPtr.writeType, res, w2

/-! ## OpResultMPtr.readOwner! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockArgumentMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readOwner!, BlockArgumentMPtr.writeFirstUse, res, w2

/-! ## OpResultMPtr.readOwner! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockArgumentMPtr_writeIndex (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readOwner!, BlockArgumentMPtr.writeIndex, res, w2

/-! ## OpResultMPtr.readOwner! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockArgumentMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readOwner!, BlockArgumentMPtr.writeOwner, res, w2

/-! ## OpResultMPtr.readType! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readType!, OpOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readType!, OpOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readType!, OpOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readType!, OpOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_opOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readFirstUse!, OpOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_opOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readFirstUse!, OpOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_opOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readFirstUse!, OpOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_opOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readFirstUse!, OpOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readIndex!, OpOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readIndex!, OpOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readIndex!, OpOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readIndex!, OpOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_opOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readOwner!, OpOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_opOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readOwner!, OpOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_opOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readOwner!, OpOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_opOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readOwner!, OpOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readType!, BlockOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readType!, BlockOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readType!, BlockOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_blockOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readType!, BlockOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readFirstUse!, BlockOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readFirstUse!, BlockOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readFirstUse!, BlockOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readFirstUse! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_blockOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readFirstUse!, BlockOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readIndex!, BlockOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readIndex!, BlockOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readIndex!, BlockOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readIndex! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_blockOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readIndex!, BlockOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readOwner!, BlockOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readOwner!, BlockOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readOwner!, BlockOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readOwner! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_blockOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readOwner!, BlockOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readType! after ValueImplMPtr.writeType -/

@[layout_grind =]
theorem OpResultMPtr.readType!_valueImplMPtr_writeType (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (res.toM ctx.spec) =
    if vptr.spec = .opResult res then val
    else Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    by_cases vptr.spec = .opResult res
    ·
      grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind,
          OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
          ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    · have : res ≠ res2 := by grind
      grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind,
          OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
          ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readType!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readFirstUse! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_valueImplMPtr_writeType (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readIndex! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_valueImplMPtr_writeType (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    grind (splits := 20) [readIndex!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readIndex!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readOwner! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_valueImplMPtr_writeType (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readType! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_valueImplMPtr_writeFirstUse (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    grind (splits := 20) [readType!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readType!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readFirstUse! after ValueImplMPtr.writeFirstUse -/

@[layout_grind =]
theorem OpResultMPtr.readFirstUse!_valueImplMPtr_writeFirstUse (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (res.toM ctx.spec) =
    if vptr.spec = .opResult res then val.impl
    else Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    by_cases vptr.spec = .opResult res
    ·
      grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind,
          OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
          ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    · have : res ≠ res2 := by grind
      grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind,
          OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
          ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readFirstUse!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readIndex! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_valueImplMPtr_writeFirstUse (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    grind (splits := 20) [readIndex!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readIndex!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readOwner! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_valueImplMPtr_writeFirstUse (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readOwner!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readType! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res2 | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
      have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
      have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
      have hri := ctx.sim.repr.operations_indices res.op (by grind)
      grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readType!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readFirstUse! after OpOperandPtrMPtr.write -/

@[layout_grind =]
theorem OpResultMPtr.readFirstUse!_opOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    if ptr.spec = .valueFirstUse (.opResult res) then val.impl
    else Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res2 | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
      have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
      have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
      have hri := ctx.sim.repr.operations_indices res.op (by grind)
      by_cases ptr.spec = .valueFirstUse (.opResult res)
      ·
        grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
            OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
            ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
      · have : res ≠ res2 := by grind
        grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
            OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
            ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readFirstUse!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readIndex! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readIndex!, OpOperandPtrMPtr.write, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res2 | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
      have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
      have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
      have hri := ctx.sim.repr.operations_indices res.op (by grind)
      grind (splits := 20) [readIndex!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readIndex!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readOwner! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_opOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res2 | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
      have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
      have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
      have hri := ctx.sim.repr.operations_indices res.op (by grind)
      grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readOwner!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]


/-! # readKind! interaction lemmas (ValueImpl kind field, offset 0) -/

/-! ## OpResultMPtr.readKind! after OpResultMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opResultMPtr_writeType (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpResultMPtr.writeType ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readKind!, OpResultMPtr.writeType, res, ptr

/-! ## OpResultMPtr.readKind! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readKind!, OpResultMPtr.writeFirstUse, res, ptr

/-! ## OpResultMPtr.readKind! after OpResultMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opResultMPtr_writeIndex (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpResultMPtr.writeIndex ctx.buf ptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readKind!, OpResultMPtr.writeIndex, res, ptr

/-! ## OpResultMPtr.readKind! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readKind!, OpResultMPtr.writeOwner, res, ptr

/-! ## OpResultMPtr.readKind! after BlockOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.BlockOperandPtrPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  rcases hcase : ptr.spec with bo | bl
  · have hdisj := ctx.sim.disjoint_allocs (.operation bo.op) (.operation res.op) (by grind) (by grind)
    have hincl := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) bo (by grind)
    have hbo := ctx.sim.in_bounds (.operation bo.op) (by grind)
    grind (splits := 20) [readKind!, BlockOperandPtrMPtr.write, layout_grind,
        OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat,
        IsIncludedI, IsDisjointI]
  · have hdisj := ctx.sim.disjoint_allocs (.block bl) (.operation res.op) (by grind) (by grind)
    have hincl := BlockPtr.range_ideal (ctx := ctx.spec) (by grind) (bl := bl) (by grind)
    grind (splits := 20) [readKind!, BlockOperandPtrMPtr.write, layout_grind,
      OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
      IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readKind! after OperationMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_operationMPtr_writeNext (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readKind!, OperationMPtr.writeNext, res, op2

/-! ## OpResultMPtr.readKind! after OperationMPtr.writeNumResults -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_operationMPtr_writeNumResults (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OperationMPtr.writeNumResults ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readKind!, OperationMPtr.writeNumResults, res, op2

/-! ## OpResultMPtr.readKind! after OperationMPtr.writeNumBlockOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_operationMPtr_writeNumBlockOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OperationMPtr.writeNumBlockOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readKind!, OperationMPtr.writeNumBlockOperands, res, op2

/-! ## OpResultMPtr.readKind! after OperationMPtr.writeNumRegions -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_operationMPtr_writeNumRegions (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OperationMPtr.writeNumRegions ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readKind!, OperationMPtr.writeNumRegions, res, op2

/-! ## OpResultMPtr.readKind! after OperationMPtr.writeNumOperands -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_operationMPtr_writeNumOperands (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OperationMPtr.writeNumOperands ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readKind!, OperationMPtr.writeNumOperands, res, op2

/-! ## OpResultMPtr.readKind! after OperationMPtr.writeAttrs -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_operationMPtr_writeAttrs (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OperationMPtr.writeAttrs ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readKind!, OperationMPtr.writeAttrs, res, op2

/-! ## OpResultMPtr.readKind! after OperationMPtr.writeOpType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_operationMPtr_writeOpType (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : UInt32) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OperationMPtr.writeOpType ctx.buf op2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readKind!, OperationMPtr.writeOpType, res, op2

/-! ## OpResultMPtr.readKind! after OperationMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_operationMPtr_writePrev (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OperationMPtr.writePrev ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readKind!, OperationMPtr.writePrev, res, op2

/-! ## OpResultMPtr.readKind! after OperationMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_operationMPtr_writeParent (res : Veir.OpResultPtr) (op2 : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OperationMPtr.writeParent ctx.buf op2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opScalar readKind!, OperationMPtr.writeParent, res, op2

/-! ## OpResultMPtr.readKind! after BlockMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readKind!, BlockMPtr.writeFirstUse, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockMPtr.writePrev -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockMPtr_writePrev (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockMPtr.writePrev ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readKind!, BlockMPtr.writePrev, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockMPtr.writeNext -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockMPtr_writeNext (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockMPtr.writeNext ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readKind!, BlockMPtr.writeNext, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionRegionPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readKind!, BlockMPtr.writeParent, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockMPtr.writeFirstOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockMPtr_writeFirstOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockMPtr.writeFirstOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readKind!, BlockMPtr.writeFirstOp, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockMPtr.writeLastOp -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockMPtr_writeLastOp (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockMPtr.writeLastOp ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readKind!, BlockMPtr.writeLastOp, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockMPtr.writeNumArguments -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockMPtr_writeNumArguments (res : Veir.OpResultPtr) (w2 : Sim.BlockPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockMPtr.writeNumArguments ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_block readKind!, BlockMPtr.writeNumArguments, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after RegionMPtr.writeFirstBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_regionMPtr_writeFirstBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.RegionMPtr.writeFirstBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readKind!, RegionMPtr.writeFirstBlock, res, w2

/-! ## OpResultMPtr.readKind! after RegionMPtr.writeLastBlock -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_regionMPtr_writeLastBlock (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionBlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.RegionMPtr.writeLastBlock ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readKind!, RegionMPtr.writeLastBlock, res, w2

/-! ## OpResultMPtr.readKind! after RegionMPtr.writeParent -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_regionMPtr_writeParent (res : Veir.OpResultPtr) (w2 : Sim.RegionPtr)
    (val : Sim.OptionOperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.RegionMPtr.writeParent ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_region readKind!, RegionMPtr.writeParent, res, w2

/-! ## OpResultMPtr.readKind! after BlockArgumentMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockArgumentMPtr_writeType (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockArgumentMPtr.writeType ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readKind!, BlockArgumentMPtr.writeType, res, w2

/-! ## OpResultMPtr.readKind! after BlockArgumentMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockArgumentMPtr_writeFirstUse (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readKind!, BlockArgumentMPtr.writeFirstUse, res, w2

/-! ## OpResultMPtr.readKind! after BlockArgumentMPtr.writeIndex -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockArgumentMPtr_writeIndex (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockArgumentMPtr.writeIndex ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readKind!, BlockArgumentMPtr.writeIndex, res, w2

/-! ## OpResultMPtr.readKind! after BlockArgumentMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockArgumentMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockArgumentPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockArgumentMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockArg readKind!, BlockArgumentMPtr.writeOwner, res, w2

/-! ## OpResultMPtr.readKind! after OpOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readKind!, OpOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after OpOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readKind!, OpOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after OpOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readKind!, OpOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after OpOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.OpOperandPtr)
    (val : Sim.ValuePtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_opOperand readKind!, OpOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockOperandMPtr.writeNextUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockOperandMPtr_writeNextUse (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OptionBlockOperandPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockOperandMPtr.writeNextUse ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readKind!, BlockOperandMPtr.writeNextUse, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockOperandMPtr.writeBack -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockOperandMPtr_writeBack (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockOperandMPtr.writeBack ctx.buf w2.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readKind!, BlockOperandMPtr.writeBack, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockOperandMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockOperandMPtr_writeOwner (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockOperandMPtr.writeOwner ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readKind!, BlockOperandMPtr.writeOwner, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after BlockOperandMPtr.writeValue -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_blockOperandMPtr_writeValue (res : Veir.OpResultPtr) (w2 : Sim.BlockOperandPtr)
    (val : Sim.BlockPtr) h (resIb : res.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.BlockOperandMPtr.writeValue ctx.buf w2.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_blockOperand readKind!, BlockOperandMPtr.writeValue, res, w2, w2Ib

/-! ## OpResultMPtr.readKind! after ValueImplMPtr.writeType -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_valueImplMPtr_writeType (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : UInt64) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.ValueImplMPtr.writeType ctx.buf vptr.impl val h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    grind (splits := 20) [readKind!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readKind!, ValueImplMPtr.writeType, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readKind! after ValueImplMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_valueImplMPtr_writeFirstUse (res : Veir.OpResultPtr) (vptr : Sim.ValuePtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (vptrIb : vptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.ValueImplMPtr.writeFirstUse ctx.buf vptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.ValuePtr.toFlat_eq_impl_toNat vptrIb
  have hib := vptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : vptr.spec with res2 | arg
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
    have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
    have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
    have hri := ctx.sim.repr.operations_indices res.op (by grind)
    grind (splits := 20) [readKind!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
      ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
  ·
    have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
    have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
    have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
    grind (splits := 20) [readKind!, ValueImplMPtr.writeFirstUse, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## OpResultMPtr.readKind! after OpOperandPtrMPtr.write -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opOperandPtrMPtr_write (res : Veir.OpResultPtr) (ptr : Sim.OpOperandPtrPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  have := @Sim.OpResultPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hbridge := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ptrIb
  have hib := ptrIb.ib
  have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
  have hres := ctx.sim.in_bounds (.operation res.op) (by grind)
  have : res.index < (res.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
  rcases hcase : ptr.spec with opr | v
  ·
    have hdisj := ctx.sim.disjoint_allocs (.operation opr.op) (.operation res.op) (by grind) (by grind)
    have hincl := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) opr (by grind)
    have hopr := ctx.sim.in_bounds (.operation opr.op) (by grind)
    have := @Sim.OpOperandPtr.after_lt_ctx
    grind (splits := 20) [readKind!, OpOperandPtrMPtr.write, layout_grind,
      OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
      OpOperandPtr.range, OpOperandPtr.toFlat,
      ValuePtr.toFlat, IsIncludedI, IsDisjointI]
  · rcases hvcase : v with res2 | arg
    ·
      have hdisj := ctx.sim.disjoint_allocs (.operation res2.op) (.operation res.op) (by grind) (by grind)
      have hincl := OpResultPtr.range_included_op_range (ctx := ctx) res2 (by grind)
      have hres2 := ctx.sim.in_bounds (.operation res2.op) (by grind)
      have : res2.index < (res2.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
      have hri := ctx.sim.repr.operations_indices res.op (by grind)
      grind (splits := 20) [readKind!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
        ValuePtr.toFlat, Operation.ReprIndices, IsIncludedI, IsDisjointI]
    ·
      have hdisj := ctx.sim.disjoint_allocs (.block arg.block) (.operation res.op) (by grind) (by grind)
      have hincl := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) arg (by grind)
      have harg := ctx.sim.in_bounds (.block arg.block) (by grind)
      grind (splits := 20) [readKind!, OpOperandPtrMPtr.write, layout_grind,
        OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat,
        BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
        ValuePtr.toFlat, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
