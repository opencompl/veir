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
theorem _root_.Veir.OpResultPtr.ext (x y : OpResultPtr) : x.op = y.op → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

/-! ## OpResultMPtr.readType! -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readType!, OpResultMPtr.writeFirstUse, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readType!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readType! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readType! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readType!, OpResultMPtr.writeOwner, res, ptr

/-! ## OpResultMPtr.readFirstUse! -/

@[layout_grind =]
theorem OpResultMPtr.readFirstUse!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    if res = ptr.spec then val.impl else Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readFirstUse!, OpResultMPtr.writeFirstUse, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readFirstUse!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readFirstUse! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readFirstUse! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readFirstUse!, OpResultMPtr.writeOwner, res, ptr

/-! ## OpResultMPtr.readIndex! -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readIndex!, OpResultMPtr.writeFirstUse, res, ptr

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readIndex!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readIndex! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readIndex! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readIndex!, OpResultMPtr.writeOwner, res, ptr

/-! ## OpResultMPtr.readOwner! -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readOwner!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readOwner!, OpResultMPtr.writeFirstUse, res, ptr

@[layout_grind =]
theorem OpResultMPtr.readOwner!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readOwner! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    if res = ptr.spec then val.impl else Buffed.OpResultMPtr.readOwner! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readOwner!, OpResultMPtr.writeOwner, res, ptr

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

/-! ## OpResultMPtr.readKind! after OpResultMPtr.writeFirstUse -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opResultMPtr_writeFirstUse (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OptionOpOperandPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readKind!, OpResultMPtr.writeFirstUse, res, ptr

/-! ## OpResultMPtr.readKind! after OpResultMPtr.writeOwner -/

@[layout_simp, layout_grind =]
theorem OpResultMPtr.readKind!_opResultMPtr_writeOwner (res : Veir.OpResultPtr) (ptr : Sim.OpResultPtr)
    (val : Sim.OperationPtr) h (resIb : res.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OpResultMPtr.readKind! (Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl val.impl h) (res.toM ctx.spec) =
    Buffed.OpResultMPtr.readKind! ctx.buf (res.toM ctx.spec) := by
  rw_or_or readKind!, OpResultMPtr.writeOwner, res, ptr

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
