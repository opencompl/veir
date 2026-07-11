module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs
public import Veir.IR.Buffed.RawReadWriteLemmas.Tactics

public section

namespace Veir.Buffed

section read_write

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] {ctx : Sim.IRContext OpInfo}

/-! ## OperationMPtr.readPrev! -/

@[layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (prev : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl prev.impl h) op.toM =
    if op = ptr.spec then prev.impl else Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  rw_op_opScalar readPrev!, writePrev, op, ptr

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (next : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl next.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  rw_op_opScalar readPrev!, writeNext, op, ptr

@[layout_simp, layout_grind =]
theorem OperationMPtr.readPrev!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readPrev! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readPrev! ctx.buf op.toM := by
  rw_op_opScalar readPrev!, writeParent, op, ptr

/-! ## OperationMPtr.readNext! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  rw_op_opScalar readNext!, writePrev, op, ptr

@[layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    if op = ptr.spec then val.impl else Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  rw_op_opScalar readNext!, writeNext, op, ptr

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNext!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNext! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readNext! ctx.buf op.toM := by
  rw_op_opScalar readNext!, writeParent, op, ptr

/-! ## OperationMPtr.readParent! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  rw_op_opScalar readParent!, writePrev, op, ptr

@[layout_simp, layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  rw_op_opScalar readParent!, writeNext, op, ptr

@[layout_grind =]
theorem OperationMPtr.readParent!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readParent! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    if op = ptr.spec then val.impl else Buffed.OperationMPtr.readParent! ctx.buf op.toM := by
  rw_op_opScalar readParent!, writeParent, op, ptr

/-! ## OperationMPtr.readOpType! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  rw_op_opScalar readOpType!, writePrev, op, ptr

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  rw_op_opScalar readOpType!, writeNext, op, ptr

@[layout_simp, layout_grind =]
theorem OperationMPtr.readOpType!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readOpType! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
  rw_op_opScalar readOpType!, writeParent, op, ptr

/-! ## OperationMPtr.readAttrs! -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writePrev (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writePrev ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  rw_op_opScalar readAttrs!, writePrev, op, ptr

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeNext (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeNext ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  rw_op_opScalar readAttrs!, writeNext, op, ptr

@[layout_simp, layout_grind =]
theorem OperationMPtr.readAttrs!_operationMPtr_writeParent (op : Veir.OperationPtr) (ptr : Sim.OperationPtr)
    (val : Sim.OptionBlockPtr) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readAttrs! (Buffed.OperationMPtr.writeParent ctx.buf ptr.impl val.impl h) op.toM =
    Buffed.OperationMPtr.readAttrs! ctx.buf op.toM := by
  rw_op_opScalar readAttrs!, writeParent, op, ptr

end read_write

end Veir.Buffed
