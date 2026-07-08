module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs
import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs

public section

namespace Veir.Buffed

section read_write

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] {ctx : Sim.IRContext OpInfo}

theorem Sim.OperationPtr.after_lt_ctx (op : Veir.OperationPtr) (opIb : op.InBounds ctx.spec) :
    op.id + Buffed.Operation.Offsets.afterInt op ctx.spec ≤ ctx.buf.mem.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.operation op) (by grind)
  simp_all [OperationPtr.range, layout_simp]
  grind [= Buffed.Operation.Offsets.after_ideal]

/-! ## readNthResult! after Block writer (op ⊥ block; offset uses only readNumResults, disjoint) -/

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

/-! ## readNthResult! after OpResult writer (op-sub; offset uses readNumResults, disjoint from results content) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthResult!_opResultMPtr_writeType (op : Veir.OperationPtr) (w2 : Sim.OpResultPtr) (idx : UInt64)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (w2Ib : w2.InBounds ctx) :
    Buffed.OperationMPtr.readNthResult! (Buffed.OpResultMPtr.writeType ctx.buf w2.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthResult! ctx.buf op.toM idx := by
  simp only [readNthResult!, computeResultOffset!, computeResultsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have := @Sim.OpResultPtr.after_lt_ctx
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have := ctx.sim.encoding_op op (by grind) |>.numResults
  have hw := ctx.sim.in_bounds (.operation w2.spec.op) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.operation w2.spec.op) (by grind) (by grind)
  have hinclw := OpResultPtr.range_included_op_range (ctx := ctx) w2.spec (by grind)
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumResults!, OpResultMPtr.writeType, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]

/-! ## readNthRegion! after operationMPtr.writeNext (buffer deref; offset uses numBlockOperands+numOperands+opType) -/

@[layout_simp, layout_grind =]
theorem OperationMPtr.readNthRegion!_operationMPtr_writeNext (op : Veir.OperationPtr) (op2 : Sim.OperationPtr) (idx : UInt64)
    (val : Sim.OptionOperationPtr) h (opIb : op.InBounds ctx.spec) (op2Ib : op2.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writeNext ctx.buf op2.impl val.impl h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!, computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
  have := @Sim.OperationPtr.after_lt_ctx
  have : ctx.buf.mem.size < 2^63 - 1 := by grind
  have hop2 := ctx.sim.in_bounds (.operation op2.spec) (by grind)
  have hdisj := ctx.sim.disjoint_allocs (.operation op) (.operation op2.spec) (by grind) (by grind)
  have hn1 := ctx.sim.encoding_op op (by grind) |>.numBlockOperands
  have hn2 := ctx.sim.encoding_op op (by grind) |>.numOperands
  have hn3 := ctx.sim.encoding_op op (by grind) |>.opType
  have := ctx.sim.in_bounds (.operation op) (by grind)
  grind (splits := 20) [readNumBlockOperands!, readNumOperands!, readOpType!, OperationMPtr.writeNext, layout_grind,
    OperationPtr.toM, OperationPtr.range, OperationPtr.toFlat, IsIncludedI, IsDisjointI]

end read_write

end Veir.Buffed
