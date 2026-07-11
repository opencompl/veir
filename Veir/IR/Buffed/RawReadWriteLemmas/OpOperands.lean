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
