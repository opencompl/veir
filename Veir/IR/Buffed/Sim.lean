module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.SimDefs
public import Veir.IR.Buffed.Layout
public import Veir.Prelude
public import Veir.IR.LayoutUnchanged
public meta import Veir.IR.Buffed.Meta
public meta import Veir.IR.Repr

import Veir.IR.Buffed.Meta
import all Veir.IR.Buffed.SimDefs
import all Veir.IR.Buffed.RawAccessors

open Veir.Buffed

set_option linter.unusedSectionVars false

public section

namespace Veir

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]

/-! ## Misc. defs on Sim Pointers  -/

@[grind, inline]
def Sim.OptionOperationPtr.none : Sim.OptionOperationPtr :=
  { impl := .none, spec := .none }

@[grind] -- TODO: finer grained grind strategy
structure Sim.OperationPtr.InBounds (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim
  ib : ptr.spec.InBounds ctx.spec

theorem Sim.OperationPtr.after_lt_ctx {ctx : Sim.IRContext OpInfo} (op : Veir.OperationPtr) (opIb : op.InBounds ctx.spec) :
    op.id + Buffed.Operation.Offsets.afterInt op ctx.spec ≤ ctx.buf.mem.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.operation op) (by grind)
  simp_all [OperationPtr.range, layout_simp]
  grind

@[grind .]
theorem Sim.OperationPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OperationPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr := by
  have := ctx.sim.repr
  grind

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionOperationPtr.InBounds (ptr : Sim.OptionOperationPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim
  ib : ptr.spec.maybe Veir.OperationPtr.InBounds ctx.spec

@[grind .]
theorem Sim.OptionOperationPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OptionOperationPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ Veir.OperationPtr.IsRepr := by
  have := ctx.sim.repr
  rcases heq : ptr.spec <;> grind

@[inline, grind]
def Sim.OperationPtr.toO (ptr : Sim.OperationPtr) : Sim.OptionOperationPtr :=
  { impl := ptr.impl, spec := some ptr.spec }

@[inline, expose, grind]
def Sim.OptionOperationPtr.toOption (ptr : Sim.OptionOperationPtr) : Option Sim.OperationPtr :=
  if ptr.impl ≠ .none then
    some { impl := ptr.impl, spec := ptr.spec.specGet! }
  else
    .none

@[inline, grind]
def OperationPtr.toSim (ptr : OperationPtr) : Sim.OperationPtr :=
  { impl := ptr.toM, spec := ptr }

@[grind .] theorem OperationPtr.toSim_sim (ptr : OperationPtr) : ptr.toSim.Sim := by grind
@[grind =] theorem OperationPtr.toSim_inBounds_iff_inBounds {ctx : Sim.IRContext OpInfo}
    (ptr : OperationPtr) : ptr.toSim.InBounds ctx ↔ ptr.InBounds ctx.spec := by grind

@[grind, inline]
def Sim.OptionBlockPtr.none : Sim.OptionBlockPtr :=
  { impl := .none, spec := .none }

@[grind] -- TODO: finer grained grind strategy
structure Sim.BlockPtr.InBounds (ptr : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim
  ib : ptr.spec.InBounds ctx.spec

theorem Sim.BlockPtr.after_lt_ctx {ctx : Sim.IRContext OpInfo} (bl : Veir.BlockPtr) (opIb : bl.InBounds ctx.spec) :
    bl.id + Buffed.Block.Offsets.afterInt bl ctx.spec ≤ ctx.buf.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.block bl) (by grind)
  simp_all [BlockPtr.range, layout_simp]
  grind

@[grind .]
theorem Sim.BlockPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.BlockPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr := by
  have := ctx.sim.repr
  grind

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionBlockPtr.InBounds (ptr : Sim.OptionBlockPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim
  ib : ptr.spec.maybe Veir.BlockPtr.InBounds ctx.spec

@[grind .]
theorem Sim.OptionBlockPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OptionBlockPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ Veir.BlockPtr.IsRepr := by
  have := ctx.sim.repr
  rcases heq : ptr.spec <;> grind

@[inline, grind]
def Sim.BlockPtr.toO (ptr : Sim.BlockPtr) : Sim.OptionBlockPtr :=
  { impl := ptr.impl, spec := some ptr.spec }

@[inline, expose, grind]
def Sim.OptionBlockPtr.toOption (ptr : Sim.OptionBlockPtr) : Option Sim.BlockPtr :=
  if ptr.impl ≠ .none then
    some { impl := ptr.impl, spec := ptr.spec.specGet! }
  else
    .none



@[grind, inline]
def BlockPtr.toSim (ptr : BlockPtr) : Sim.BlockPtr :=
  { impl := ptr.toM, spec := ptr }

@[grind .] theorem BlockPtr.toSim_sim (ptr : BlockPtr) : ptr.toSim.Sim := by grind
@[grind =] theorem BlockPtr.toSim_inBounds_iff_inBounds {ctx : Sim.IRContext OpInfo}
    (ptr : BlockPtr) : ptr.toSim.InBounds ctx ↔ ptr.InBounds ctx.spec := by grind

@[grind, inline]
def Sim.OptionRegionPtr.none : Sim.OptionRegionPtr :=
  { impl := .none, spec := .none }

@[grind] -- TODO: finer grained grind strategy
structure Sim.RegionPtr.InBounds (ptr : Sim.RegionPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim
  ib : ptr.spec.InBounds ctx.spec

@[grind .]
theorem Sim.RegionPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.RegionPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr := by
  have := ctx.sim.repr
  grind

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionRegionPtr.InBounds (ptr : Sim.OptionRegionPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim
  ib : ptr.spec.maybe Veir.RegionPtr.InBounds ctx.spec

@[grind .]
theorem Sim.OptionRegionPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OptionRegionPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ Veir.RegionPtr.IsRepr := by
  have := ctx.sim.repr
  rcases heq : ptr.spec <;> grind

@[inline, grind]
def Sim.RegionPtr.toO (ptr : Sim.RegionPtr) : Sim.OptionRegionPtr :=
  { impl := ptr.impl, spec := some ptr.spec }

@[inline, expose, grind]
def Sim.OptionRegionPtr.toOption (ptr : Sim.OptionRegionPtr) : Option Sim.RegionPtr :=
  if _ : ptr.impl ≠ .none then
    some { impl := ptr.impl, spec := ptr.spec.specGet! }
  else
    .none

@[grind, inline]
def RegionPtr.toSim (ptr : RegionPtr) : Sim.RegionPtr :=
  { impl := ptr.toM, spec := ptr }

@[grind .] theorem RegionPtr.toSim_sim (ptr : RegionPtr) : ptr.toSim.Sim := by grind
@[grind =] theorem RegionPtr.toSim_inBounds_iff_inBounds {ctx : Sim.IRContext OpInfo}
    (ptr : RegionPtr) : ptr.toSim.InBounds ctx ↔ ptr.InBounds ctx.spec := by grind

@[grind, inline]
def Sim.OptionOpResultPtr.none : Sim.OptionOpResultPtr :=
  { impl := .none, spec := .none }

@[grind] -- TODO: finer grained grind strategy
structure Sim.OpResultPtr.InBounds (ptr : Sim.OpResultPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.InBounds ctx.spec

theorem Sim.OpResultPtr.after_lt_ctx {ctx : Sim.IRContext OpInfo} (op : Veir.OpResultPtr) (opIb : op.InBounds ctx.spec) :
    op.toFlat ctx.spec + Buffed.OpResult.Offsets.afterInt ≤ ctx.buf.mem.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.operation op.op) (by grind)
  have hincl₁ := OpResultPtr.range_included_op_range (ctx := ctx) op (by grind)
  rw [OpResultPtr.toFlat_ideal (by grind) _ (by grind)]
  grind [layout_grind]

@[grind .]
theorem Sim.OpResultPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OpResultPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr ctx.spec := by
  grind [layout_grind]

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionOpResultPtr.InBounds (ptr : Sim.OptionOpResultPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.maybe Veir.OpResultPtr.InBounds ctx.spec

@[grind .]
theorem Sim.OptionOpResultPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OptionOpResultPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe Veir.OpResultPtr.IsRepr ctx.spec := by
  rcases heq : ptr.spec <;> grind [layout_grind]

@[inline, grind]
def Sim.OpResultPtr.toO (ptr : Sim.OpResultPtr) : Sim.OptionOpResultPtr :=
  { impl := ptr.impl, spec := some ptr.spec }

@[inline, expose, grind]
def Sim.OptionOpResultPtr.toOption (ptr : Sim.OptionOpResultPtr) : Option Sim.OpResultPtr :=
  if ptr.impl ≠ .none then
    some { impl := ptr.impl, spec := ptr.spec.specGet! }
  else
    .none

@[grind, inline]
def Sim.OptionBlockArgumentPtr.none : Sim.OptionBlockArgumentPtr :=
  { impl := .none, spec := .none }

@[grind] -- TODO: finer grained grind strategy
structure Sim.BlockArgumentPtr.InBounds (ptr : Sim.BlockArgumentPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim
  ib : ptr.spec.InBounds ctx.spec

theorem Sim.BlockArgumentPtr.after_lt_ctx {ctx : IRContext OpInfo} (op : Veir.BlockArgumentPtr) (opIb : op.InBounds ctx.spec) :
    op.toFlat + Buffed.BlockArgument.Offsets.afterInt ≤ ctx.buf.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.block op.block) (by grind)
  have hincl₁ := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) op (by grind)
  rw [BlockArgumentPtr.toFlat_ideal]
  simp_all only [BlockArgumentPtr.range_ideal]
  grind [layout_grind]

@[grind .]
theorem Sim.BlockArgumentPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.BlockArgumentPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr := by
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  grind [layout_grind]

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionBlockArgumentPtr.InBounds (ptr : Sim.OptionBlockArgumentPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim
  ib : ptr.spec.maybe Veir.BlockArgumentPtr.InBounds ctx.spec

@[grind .]
theorem Sim.OptionBlockArgumentPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OptionBlockArgumentPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ Veir.BlockArgumentPtr.IsRepr := by
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  have := @Sim.BlockArgumentPtr.after_lt_ctx
  rcases heq : ptr.spec <;> grind

@[inline, grind]
def Sim.BlockArgumentPtr.toO (ptr : Sim.BlockArgumentPtr) : Sim.OptionBlockArgumentPtr :=
  { impl := ptr.impl, spec := some ptr.spec }

@[inline, expose, grind]
def Sim.OptionBlockArgumentPtr.toOption (ptr : Sim.OptionBlockArgumentPtr) : Option Sim.BlockArgumentPtr :=
  if ptr.impl ≠ .none then
    some { impl := ptr.impl, spec := ptr.spec.specGet! }
  else
    .none

@[grind, inline]
def Sim.OptionOpOperandPtr.none : Sim.OptionOpOperandPtr :=
  { impl := .none, spec := .none }

@[inline, expose, grind]
def Sim.OptionOpOperandPtr.toOption (ptr : Sim.OptionOpOperandPtr) : Option Sim.OpOperandPtr :=
  if ptr.impl = .none then .none else some { impl := ptr.impl, spec := ptr.spec.specGet! }

@[grind] -- TODO: finer grained grind strategy
structure Sim.OpOperandPtr.InBounds (ptr : Sim.OpOperandPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.InBounds ctx.spec

theorem Sim.OpOperandPtr.after_lt_ctx {ctx : Sim.IRContext OpInfo} (op : Veir.OpOperandPtr) (opIb : op.InBounds ctx.spec) :
    op.toFlat ctx.spec + Buffed.OpOperand.Offsets.afterInt ≤ ctx.buf.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.operation op.op) (by grind)
  have hincl₁ := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) op (by grind)
  rw [OpOperandPtr.toFlat_ideal (by grind) _ (by grind)]
  grind [layout_grind]

@[grind .]
theorem Sim.OpOperandPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OpOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr ctx.spec := by
  have := @Sim.OpOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  grind [layout_grind]

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionOpOperandPtr.InBounds (ptr : Sim.OptionOpOperandPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.maybe Veir.OpOperandPtr.InBounds ctx.spec

@[grind .]
theorem Sim.OptionOpOperandPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OptionOpOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe Veir.OpOperandPtr.IsRepr ctx.spec := by
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  have := @Sim.OpOperandPtr.after_lt_ctx
  rcases heq : ptr.spec <;> grind

@[inline, grind]
def Sim.OpOperandPtr.toO (ptr : Sim.OpOperandPtr) : Sim.OptionOpOperandPtr :=
  { impl := ptr.impl, spec := some ptr.spec }

@[grind, inline]
def Sim.OptionBlockOperandPtr.none : Sim.OptionBlockOperandPtr :=
  { impl := .none, spec := .none }

@[grind] -- TODO: finer grained grind strategy
structure Sim.BlockOperandPtr.InBounds (ptr : Sim.BlockOperandPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.InBounds ctx.spec

theorem Sim.BlockOperandPtr.after_lt_ctx {ctx : Sim.IRContext OpInfo} (op : Veir.BlockOperandPtr) (opIb : op.InBounds ctx.spec) :
    op.toFlat ctx.spec + Buffed.BlockOperand.Offsets.afterInt ≤ ctx.buf.size := by
  have ⟨_, h⟩ := ctx.sim.in_bounds (.operation op.op) (by grind)
  have hincl₁ := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) op (by grind)
  rw [BlockOperandPtr.toFlat_ideal (by grind) _ (by grind)]
  grind [layout_grind]

@[grind .]
theorem Sim.BlockOperandPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.BlockOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr ctx.spec := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  grind [layout_grind]

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionBlockOperandPtr.InBounds (ptr : Sim.OptionBlockOperandPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.maybe Veir.BlockOperandPtr.InBounds ctx.spec

@[grind .]
theorem Sim.OptionBlockOperandPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OptionBlockOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe Veir.BlockOperandPtr.IsRepr ctx.spec := by
  have := @Sim.BlockOperandPtr.after_lt_ctx
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  rcases heq : ptr.spec <;> grind

@[inline, grind]
def Sim.BlockOperandPtr.toO (ptr : Sim.BlockOperandPtr) : Sim.OptionBlockOperandPtr :=
  { impl := ptr.impl, spec := some ptr.spec }

@[inline, expose, grind]
def Sim.OptionBlockOperandPtr.toOption (ptr : Sim.OptionBlockOperandPtr) : Option Sim.BlockOperandPtr :=
  if ptr.impl ≠ .none then
    some { impl := ptr.impl, spec := ptr.spec.specGet! }
  else
    .none

@[grind, inline]
def Sim.OptionValuePtr.none : Sim.OptionValuePtr :=
  { impl := .none, spec := .none }

@[inline]
def Sim.ValuePtr.fromOpResultPtr (ptr : Sim.OpResultPtr) : Sim.ValuePtr :=
  { impl := ptr.impl, spec := .opResult ptr.spec }

@[inline]
def Sim.ValuePtr.fromBlockArgumentPtr (ptr : Sim.BlockArgumentPtr) : Sim.ValuePtr :=
  { impl := ptr.impl, spec := .blockArgument ptr.spec }

@[grind] -- TODO: finer grained grind strategy
structure Sim.ValuePtr.InBounds (ptr : Sim.ValuePtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.InBounds ctx.spec

theorem Sim.ValuePtr.after_lt_ctx {ctx : Sim.IRContext OpInfo} (op : Veir.ValuePtr) (opIb : op.InBounds ctx.spec) :
    op.toFlat ctx.spec + Buffed.BlockOperand.Offsets.afterInt ≤ ctx.buf.size := by
  rcases op with res | bl
  · have ⟨_, h⟩ := ctx.sim.in_bounds (.operation res.op) (by grind)
    have hincl₁ := OpResultPtr.range_included_op_range (ctx := ctx) res (by grind)
    have := OpResultPtr.toFlat_ideal (ctx := ctx.spec) (by grind) res (by grind)
    grind [layout_grind]
  · have ⟨_, h⟩ := ctx.sim.in_bounds (.block bl.block) (by grind)
    have hincl₁ := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) bl (by grind)
    have := BlockArgumentPtr.toFlat_ideal bl
    grind [layout_grind]

@[grind .]
theorem Sim.ValuePtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.ValuePtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr ctx.spec := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  rcases heq : ptr.spec <;> grind

@[grind] -- TODO: finer grained grind strategy
structure Sim.OptionValuePtr.InBounds (ptr : Sim.OptionValuePtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.maybe Veir.ValuePtr.InBounds ctx.spec

@[grind .]
theorem Sim.OptionValuePtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OptionValuePtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe Veir.ValuePtr.IsRepr ctx.spec := by
  have := @Sim.ValuePtr.after_lt_ctx
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  rcases heq : ptr.spec <;> grind

@[inline, grind]
def Sim.ValuePtr.toO (ptr : Sim.ValuePtr) : Sim.OptionValuePtr :=
  { impl := ptr.impl, spec := some ptr.spec }

@[inline, expose, grind]
def Sim.OptionValuePtr.toOption (ptr : Sim.OptionValuePtr) : Option Sim.ValuePtr :=
  if ptr.impl ≠ .none then
    some { impl := ptr.impl, spec := ptr.spec.specGet! }
  else
    .none

@[grind] -- TODO: finer grained grind strategy
structure Sim.OpOperandPtrPtr.InBounds (ptr : Sim.OpOperandPtrPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.InBounds ctx.spec

theorem Sim.OpOperandPtrPtr.after_lt_ctx {ctx : Sim.IRContext OpInfo} (op : Veir.OpOperandPtrPtr) (opIb : op.InBounds ctx.spec) :
    op.toFlat ctx.spec + Buffed.ptrSize.toNat ≤ ctx.buf.size := by
  rcases op with oper | val
  · have := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper (by grind)
    grind [layout_grind]
  · have := Sim.ValuePtr.after_lt_ctx (ctx := ctx) val (by grind)
    grind [layout_grind]

@[grind .]
theorem Sim.OpOperandPtrPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.OpOperandPtrPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr ctx.spec := by
  have := @Sim.OpOperandPtrPtr.after_lt_ctx
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  grind [layout_grind]

@[grind] -- TODO: finer grained grind strategy
structure Sim.BlockOperandPtrPtr.InBounds (ptr : Sim.BlockOperandPtrPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.InBounds ctx.spec

theorem Sim.BlockOperandPtrPtr.after_lt_ctx {ctx : Sim.IRContext OpInfo} (op : Veir.BlockOperandPtrPtr) (opIb : op.InBounds ctx.spec) :
    op.toFlat ctx.spec + Buffed.ptrSize.toNat ≤ ctx.buf.size := by
  rcases op with oper | bl
  · have := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) oper (by grind)
    grind [layout_grind]
  · have := Sim.BlockPtr.after_lt_ctx (ctx := ctx) bl (by grind)
    grind [layout_grind]

@[grind .]
theorem Sim.BlockOperandPtrPtr.isRepr_of_inBounds {ctx : IRContext OpInfo} {ptr : Sim.BlockOperandPtrPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.IsRepr ctx.spec := by
  have := @Sim.BlockOperandPtrPtr.after_lt_ctx
  have : ctx.buf.mem.size ≤ 2^63 - 1 := by grind
  grind [layout_grind]

@[grind] -- TODO: finer grained grind strategy
structure Sim.GenericPtr.InBounds (ptr : Sim.GenericPtr) (ctx : Sim.IRContext OpInfo) where
  sim : ptr.Sim ctx.inner
  ib : ptr.spec.InBounds ctx.spec

namespace Sim.GenericPtr
variable {ctx : IRContext OpInfo}

@[simp, generic_ptr_grind _=_] theorem iff_block (ptr : BlockPtr) : (fromBlock ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
theorem iff_block_spec (ptr : GenericPtr) (h : ptr.spec = .block ptr') : ptr.InBounds ctx ↔ (BlockPtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
@[simp, generic_ptr_grind _=_] theorem iff_operation (ptr : OperationPtr) : (fromOperation ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
 theorem iff_operation_spec (ptr : GenericPtr) (h : ptr.spec = .operation ptr') : ptr.InBounds ctx ↔ (OperationPtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
@[simp, generic_ptr_grind _=_] theorem iff_result (ptr : OpResultPtr) : (fromOpResult ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
 theorem iff_result_spec (ptr : GenericPtr) (h : ptr.spec = .opResult ptr') : ptr.InBounds ctx ↔ (OpResultPtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
@[simp, generic_ptr_grind _=_] theorem iff_opOperand (ptr : OpOperandPtr) : (fromOpOperand ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
theorem iff_opOperand_spec (ptr : GenericPtr) (h : ptr.spec = .opOperand ptr') : ptr.InBounds ctx ↔ (OpOperandPtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
@[simp, generic_ptr_grind _=_] theorem iff_blockOperand (ptr : BlockOperandPtr) : (fromBlockOperand ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
 theorem iff_blockOperand_spec (ptr : GenericPtr) (h : ptr.spec = .blockOperand ptr') : ptr.InBounds ctx ↔ (BlockOperandPtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
@[simp, generic_ptr_grind _=_] theorem iff_blockOperandPtr (ptr : BlockOperandPtrPtr) : (fromBlockOperandPtr ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
 theorem iff_blockOperandPtr_spec (ptr : GenericPtr) (h : ptr.spec = .blockOperandPtr ptr') : ptr.InBounds ctx ↔ (BlockOperandPtrPtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
@[simp, generic_ptr_grind _=_] theorem iff_blockArgument (ptr : BlockArgumentPtr) : (fromBlockArgument ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
theorem iff_blockArgument_spec (ptr : GenericPtr) (h : ptr.spec = .blockArgument ptr') : ptr.InBounds ctx ↔ (BlockArgumentPtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
@[simp, generic_ptr_grind _=_] theorem iff_region (ptr : RegionPtr) : (fromRegion ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
theorem iff_region_spec (ptr : GenericPtr) (h : ptr.spec = .region ptr') : ptr.InBounds ctx ↔ (RegionPtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
@[simp, generic_ptr_grind _=_] theorem iff_value (ptr : ValuePtr) : (fromValue ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
theorem iff_value_spec (ptr : GenericPtr) (h : ptr.spec = .value ptr') : ptr.InBounds ctx ↔ (ValuePtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
@[simp, generic_ptr_grind _=_] theorem iff_opOperandPtr (ptr : OpOperandPtrPtr) : (fromOpOperandPtr ptr).InBounds ctx ↔ ptr.InBounds ctx := by grind [GenericPtr.toM]
theorem iff_opOperandPtr_spec (ptr : GenericPtr) (h : ptr.spec = .opOperandPtr ptr') : ptr.InBounds ctx ↔ (OpOperandPtrPtr.mk ptr.impl ptr').InBounds ctx := by grind [GenericPtr.toM]
end Sim.GenericPtr

@[inline]
def Sim.OpOperandPtr.getOpOperandPtrPtr (ptr : Sim.OpOperandPtr) : Sim.OpOperandPtrPtr :=
  ⟨ptr.impl + OpOperand.Offsets.nextUse.toUInt64,
   .operandNextUse ptr.spec⟩

@[inline]
def Sim.BlockOperandPtr.getBlockOperandPtrPtr (ptr : Sim.BlockOperandPtr) : Sim.BlockOperandPtrPtr :=
  ⟨ptr.impl + OpOperand.Offsets.nextUse.toUInt64,
   .blockOperandNextUse ptr.spec⟩

@[inline]
def Sim.ValuePtr.getOpOperandPtrPtr (ptr : Sim.ValuePtr) : Sim.OpOperandPtrPtr :=
  ⟨ptr.impl + ValueImpl.Offsets.firstUse.toUInt64,
   match ptr.spec with
   | .opResult res => .valueFirstUse res
   | .blockArgument arg => .valueFirstUse arg⟩

@[inline]
def Sim.BlockPtr.getBlockOperandPtrPtr (ptr : Sim.BlockPtr) : Sim.BlockOperandPtrPtr :=
  ⟨ptr.impl + Block.Offsets.firstUse.toUInt64, .blockFirstUse ptr.spec⟩

/-! ## Preservation of `toFlat` when the layout is preserved. -/

@[grind .]
theorem OpResultPtr.toFlat_layoutPreserved {ctx ctx' : IRContext OpInfo} {ptr : OpResultPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toFlat ctx' = ptr.toFlat ctx := by
  unfold OpResultPtr.toFlat Operation.Offsets.results Operation.Sizes.results
  grind [IRContext.LayoutPreserved, OperationPtr.LayoutPreserved]

@[grind .]
theorem OpOperandPtr.toFlat_layoutPreserved {ctx ctx' : IRContext OpInfo} {ptr : OpOperandPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toFlat ctx' = ptr.toFlat ctx := by
  unfold OpOperandPtr.toFlat Operation.Offsets.operands Operation.Sizes.properties
  grind [IRContext.LayoutPreserved, OperationPtr.LayoutPreserved]

set_option maxHeartbeats 2000000 in
@[grind .]
theorem BlockOperandPtr.toFlat_layoutPreserved {ctx ctx' : IRContext OpInfo} {ptr : BlockOperandPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toFlat ctx' = ptr.toFlat ctx := by
  unfold BlockOperandPtr.toFlat Operation.Offsets.blockOperands Operation.Sizes.operands
  grind [IRContext.LayoutPreserved, OperationPtr.LayoutPreserved]

@[grind .]
theorem ValuePtr.toFlat_layoutPreserved {ctx ctx' : IRContext OpInfo} {ptr : ValuePtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toFlat ctx' = ptr.toFlat ctx := by
  grind [cases ValuePtr, ValuePtr.toFlat]

@[grind .]
theorem OpOperandPtrPtr.toFlat_layoutPreserved {ctx ctx' : IRContext OpInfo} {ptr : OpOperandPtrPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toFlat ctx' = ptr.toFlat ctx := by
  grind [cases OpOperandPtrPtr, OpOperandPtrPtr.toFlat]

@[grind ·]
theorem BlockOperandPtrPtr.toFlat_layoutPreserved {ctx ctx' : IRContext OpInfo} {ptr : BlockOperandPtrPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toFlat ctx' = ptr.toFlat ctx := by
  grind [cases BlockOperandPtrPtr, BlockOperandPtrPtr.toFlat]

/-! ## Preservation of `Sim` when the layout is preserved. -/

@[grind .]
theorem Sim.OperationPtr.sim_preserved {ctx : Sim.IRContext OpInfo} {ptr : Sim.OperationPtr} :
    ptr.InBounds ctx → ptr.Sim := by
  grind

@[grind .]
theorem Sim.BlockPtr.sim_preserved {ctx : Sim.IRContext OpInfo} {ptr : Sim.BlockPtr} :
    ptr.InBounds ctx → ptr.Sim := by
  grind

@[grind .]
theorem Sim.RegionPtr.sim_preserved {ctx : Sim.IRContext OpInfo} {ptr : Sim.BlockPtr} :
    ptr.InBounds ctx → ptr.Sim := by
  grind

@[grind .]
theorem Sim.BlockArgumentPtr.sim_preserved {ctx : Sim.IRContext OpInfo} {ptr : Sim.BlockArgumentPtr} :
    ptr.InBounds ctx → ptr.Sim := by
  grind

@[grind .]
theorem Sim.OptionOperationPtr.sim_preserved {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOperationPtr} :
    ptr.InBounds ctx → ptr.Sim := by
  grind

@[grind .]
theorem Sim.OptionBlockPtr.sim_preserved {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockPtr} :
    ptr.InBounds ctx → ptr.Sim := by
  grind

@[grind .]
theorem Sim.OptionRegionPtr.sim_preserved {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionRegionPtr} :
    ptr.InBounds ctx → ptr.Sim := by
  grind

@[grind .]
theorem Sim.OptionBlockArgumentPtr.sim_preserved {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockArgumentPtr} :
    ptr.InBounds ctx → ptr.Sim := by
  grind

@[grind! .]
theorem Sim.OpResultPtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.OpResultPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  grind [Sim.OpResultPtr.Sim, Veir.OpResultPtr.toM]

@[grind! .]
theorem Sim.OpOperandPtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.OpOperandPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  grind [Sim.OpOperandPtr.Sim, Veir.OpOperandPtr.toM]

@[grind! .]
theorem Sim.BlockOperandPtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.BlockOperandPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  grind [Sim.BlockOperandPtr.Sim, Veir.BlockOperandPtr.toM]

@[grind! .]
theorem Sim.ValuePtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.ValuePtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  grind [Sim.ValuePtr.Sim, Veir.ValuePtr.toM]

@[grind! .]
theorem Sim.OpOperandPtrPtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.OpOperandPtrPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  grind [Sim.OpOperandPtrPtr.Sim, Veir.OpOperandPtrPtr.toM]

@[grind! .]
theorem Sim.BlockOperandPtrPtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.BlockOperandPtrPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  grind [Sim.BlockOperandPtrPtr.Sim, Veir.BlockOperandPtrPtr.toM]

@[grind! .]
theorem Sim.OptionOpResultPtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.OptionOpResultPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  obtain ⟨impl, spec⟩ := ptr
  cases spec <;>
    grind [Sim.OptionOpResultPtr.Sim, Veir.OpResultPtr.toO, Veir.OpResultPtr.toM, Option.maybe_def]

@[grind! .]
theorem Sim.OptionOpOperandPtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.OptionOpOperandPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  obtain ⟨impl, spec⟩ := ptr
  cases spec <;>
    grind [Sim.OptionOpOperandPtr.Sim, Veir.OpOperandPtr.toO, Veir.OpOperandPtr.toM, Option.maybe_def]

@[grind! .]
theorem Sim.OptionBlockOperandPtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockOperandPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  obtain ⟨impl, spec⟩ := ptr
  cases spec <;>
    grind [Sim.OptionBlockOperandPtr.Sim, Veir.BlockOperandPtr.toO, Veir.BlockOperandPtr.toM, Option.maybe_def]

@[grind! .]
theorem Sim.OptionValuePtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.OptionValuePtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  obtain ⟨impl, spec⟩ := ptr
  cases spec <;>
    grind [Sim.OptionValuePtr.Sim, Veir.ValuePtr.toO, Veir.ValuePtr.toM, Option.maybe_def]

@[layout_grind .]
theorem BlockOperandPtr.layoutPreserved_same_toM {ctx ctx' : Veir.IRContext OpInfo} {ptr : Veir.BlockOperandPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toM ctx' = ptr.toM ctx := by
  grind [BlockOperandPtr.toM]

@[layout_grind .]
theorem OpResultPtr.layoutPreserved_same_toM {ctx ctx' : Veir.IRContext OpInfo} {ptr : Veir.OpResultPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toM ctx' = ptr.toM ctx := by
  grind [OpResultPtr.toM]

@[layout_grind .]
theorem OpOperandPtr.layoutPreserved_same_toM {ctx ctx' : Veir.IRContext OpInfo} {ptr : Veir.OpOperandPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toM ctx' = ptr.toM ctx := by
  grind [OpOperandPtr.toM]

@[layout_grind .]
theorem BlockOperandPtrPtr.layoutPreserved_same_toM {ctx ctx' : Veir.IRContext OpInfo} {ptr : Veir.BlockOperandPtrPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toM ctx' = ptr.toM ctx := by
  grind [BlockOperandPtrPtr.toM]

@[layout_grind .]
theorem ValuePtr.layoutPreserved_same_toM {ctx ctx' : Veir.IRContext OpInfo} {ptr : Veir.ValuePtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toM ctx' = ptr.toM ctx := by
  grind [ValuePtr.toM]

@[layout_grind .]
theorem OpOperandPtrPtr.layoutPreserved_same_toM {ctx ctx' : Veir.IRContext OpInfo} {ptr : Veir.OpOperandPtrPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toM ctx' = ptr.toM ctx := by
  grind [OpOperandPtrPtr.toM]

@[layout_grind .]
theorem GenericPtr.layoutPreserved_same_toM {ctx ctx' : Veir.IRContext OpInfo} {ptr : Veir.GenericPtr} :
    ctx.LayoutPreserved ctx' →
    ptr.InBounds ctx →
    ptr.toM ctx' = ptr.toM ctx := by
  cases ptr <;> simp [GenericPtr.toM]
  · grind [OpResultPtr.toM]
  · grind [OpOperandPtr.toM]
  · grind [BlockOperandPtr.toM]
  · grind [BlockOperandPtrPtr.toM]
  · grind [ValuePtr.toM]
  · grind [OpOperandPtrPtr.toM]

@[layout_grind .]
theorem OpResultPtr.layoutPreserved_same_toO {ctx ctx' : Veir.IRContext OpInfo} {ptr : Option Veir.OpResultPtr} :
    ctx.LayoutPreserved ctx' →
    (∀ p, ptr = some p → p.InBounds ctx) →
    OpResultPtr.toO ptr ctx' = OpResultPtr.toO ptr ctx := by
  cases ptr <;> grind [layout_grind]

@[layout_grind .]
theorem OpOperandPtr.layoutPreserved_same_toO {ctx ctx' : Veir.IRContext OpInfo} {ptr : Option Veir.OpOperandPtr} :
    ctx.LayoutPreserved ctx' →
    (∀ p, ptr = some p → p.InBounds ctx) →
    OpOperandPtr.toO ptr ctx' = OpOperandPtr.toO ptr ctx := by
  cases ptr <;> grind [layout_grind]

@[layout_grind .]
theorem BlockOperandPtr.layoutPreserved_same_toO {ctx ctx' : Veir.IRContext OpInfo} {ptr : Option Veir.BlockOperandPtr} :
    ctx.LayoutPreserved ctx' →
    (∀ p, ptr = some p → p.InBounds ctx) →
    BlockOperandPtr.toO ptr ctx' = BlockOperandPtr.toO ptr ctx := by
  cases ptr <;> grind [layout_grind]

@[layout_grind .]
theorem ValuePtr.layoutPreserved_same_toO {ctx ctx' : Veir.IRContext OpInfo} {ptr : Option Veir.ValuePtr} :
    ctx.LayoutPreserved ctx' →
    (∀ p, ptr = some p → p.InBounds ctx) →
    ValuePtr.toO ptr ctx' = ValuePtr.toO ptr ctx := by
  cases ptr <;> grind [layout_grind]

@[layout_grind .]
theorem Sim.GenericPtr.layoutPreserved_same_toM_inner {ctx ctx' : Sim.IRContext OpInfo} {ptr : Veir.GenericPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx.spec →
    ptr.toM ctx'.inner.spec = ptr.toM ctx.inner.spec := by
  cases ptr <;> grind [layout_grind]

@[layout_grind! .]
theorem Sim.GenericPtr.sim_layoutPreserved {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.GenericPtr} :
    ctx.spec.LayoutPreserved ctx'.spec →
    ptr.InBounds ctx →
    ptr.Sim ctx'.inner := by
  grind [layout_grind]

@[grind .]
theorem Sim.GenericPtr.sim_layoutUnchanged {ctx ctx' : Sim.IRContext OpInfo} {ptr : Sim.GenericPtr} :
    ptr.InBounds ctx' →
    ctx.spec.LayoutUnchanged ctx'.spec →
    ptr.Sim ctx.inner := by
  grind [layout_grind]

/-! ## Lemmas about Option*Ptr and Sim -/

/-! ### Operations -/

@[grind .]
theorem Sim.OperationPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OperationPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.OperationPtr.toM] at sim
  have : ptr.spec.IsRepr := by grind only [isRepr_of_inBounds]
  grind

@[grind .]
theorem Sim.OptionOperationPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOperationPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ (·.toFlat = ptr.impl.toNat) := by
  have sim := ib.sim
  simp [Sim, Veir.OperationPtr.toO, Veir.OperationPtr.toM] at sim
  have repr := Sim.OptionOperationPtr.isRepr_of_inBounds ib
  grind

@[grind.]
theorem Sim.OptionOperationPtr.impl_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOperationPtr} (ib : ptr.InBounds ctx) :
    ptr.impl = .none ↔ ptr.spec = .none := by
  have : ptr.spec.maybe₁ OperationPtr.IsRepr := by grind
  have sim := ib.sim
  simp [Sim.OptionOperationPtr.Sim, Veir.OperationPtr.toO, Veir.OperationPtr.toM] at sim
  grind

@[grind .]
theorem Sim.OptionOperationPtr.toOption_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOperationPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = .none ↔ ptr.spec = .none := by grind

@[grind .]
theorem Sim.OptionOperationPtr.toOption_some {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOperationPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = some ptr' → ptr.spec = some ptr'.spec := by
  grind

@[grind .]
theorem Sim.OperationPtr.sim_of_optionPtr_sim (optr : Sim.OptionOperationPtr) ptr :
    optr.toOption = some ptr → optr.Sim → ptr.Sim := by
  simp_all only [OptionOperationPtr.Sim, Veir.OperationPtr.toO]
  grind

@[grind .]
theorem Sim.OptionOperationPtr.toO_sim_of_sim (ptr : Sim.OperationPtr) :
    ptr.Sim → ptr.toO.Sim := by
  simp_all only [OptionOperationPtr.Sim, Sim.OperationPtr.toO, Veir.OperationPtr.toO]
  grind

/-! ### Blocks -/

@[grind .]
theorem Sim.BlockPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.BlockPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.BlockPtr.toM] at sim
  have : ptr.spec.IsRepr := by grind only [isRepr_of_inBounds]
  grind

@[grind .]
theorem Sim.OptionBlockPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ (·.toFlat = ptr.impl.toNat) := by
  have sim := ib.sim
  simp [Sim, Veir.BlockPtr.toO, Veir.BlockPtr.toM] at sim
  have repr := Sim.OptionBlockPtr.isRepr_of_inBounds ib
  grind

@[grind.]
theorem Sim.OptionBlockPtr.impl_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockPtr} (ib : ptr.InBounds ctx) :
    ptr.impl = .none ↔ ptr.spec = .none := by
  have : ptr.spec.maybe₁ BlockPtr.IsRepr := by grind
  have sim := ib.sim
  simp [Sim.OptionBlockPtr.Sim, Veir.BlockPtr.toO, Veir.BlockPtr.toM] at sim
  grind

@[grind .]
theorem Sim.OptionBlockPtr.toOption_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = .none ↔ ptr.spec = .none := by grind

@[grind .]
theorem Sim.OptionBlockPtr.toOption_some {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = some ptr' → ptr.spec = some ptr'.spec := by
  grind

@[grind .]
theorem Sim.BlockPtr.sim_of_optionPtr_sim (optr : Sim.OptionBlockPtr) ptr :
    optr.toOption = some ptr → optr.Sim → ptr.Sim := by
  simp_all only [OptionBlockPtr.Sim, Veir.BlockPtr.toO]
  grind

@[grind .]
theorem Sim.OptionBlockPtr.toO_sim_of_sim (ptr : Sim.BlockPtr) :
    ptr.Sim → ptr.toO.Sim := by
  simp_all only [OptionBlockPtr.Sim, Sim.BlockPtr.toO, Veir.BlockPtr.toO]
  grind

@[grind .]
theorem Sim.BlockPtr.getOpOperandPtrPtr_sim_of_sim {ctx : Sim.IRContext OpInfo} (block : BlockPtr) (ib : block.InBounds ctx) :
    block.getBlockOperandPtrPtr.Sim ctx.inner := by
  rcases ib with ⟨sim, ib⟩ -- need `ib` to know that there is no overflow!
  unfold getBlockOperandPtrPtr BlockOperandPtrPtr.Sim
  rw [← sim]
  suffices _ : block.spec.toFlat + Block.Offsets.firstUse.toInt.toNat < 2^64 by
    exact UInt64.left_eq_add.mpr rfl
  have := ctx.sim.in_bounds (.block block.spec) (by grind)
  grind [layout_grind]

/-! ### Regions -/

@[grind .]
theorem Sim.RegionPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.RegionPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.RegionPtr.toM] at sim
  have : ptr.spec.IsRepr := by grind only [isRepr_of_inBounds]
  grind

@[grind .]
theorem Sim.OptionRegionPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionRegionPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ (·.toFlat = ptr.impl.toNat) := by
  have sim := ib.sim
  simp [Sim, Veir.RegionPtr.toO, Veir.RegionPtr.toM] at sim
  have repr := Sim.OptionRegionPtr.isRepr_of_inBounds ib
  grind

@[grind.]
theorem Sim.OptionRegionPtr.impl_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionRegionPtr} (ib : ptr.InBounds ctx) :
    ptr.impl = .none ↔ ptr.spec = .none := by
  have : ptr.spec.maybe₁ RegionPtr.IsRepr := by grind
  have sim := ib.sim
  simp [Sim.OptionRegionPtr.Sim, Veir.RegionPtr.toO, Veir.RegionPtr.toM] at sim
  grind

@[grind .]
theorem Sim.OptionRegionPtr.toOption_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionRegionPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = .none ↔ ptr.spec = .none := by grind

@[grind .]
theorem Sim.OptionRegionPtr.toOption_some {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionRegionPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = some ptr' → ptr.spec = some ptr'.spec := by
  grind

@[grind .]
theorem Sim.RegionPtr.sim_of_optionPtr_sim (optr : Sim.OptionRegionPtr) ptr :
    optr.toOption = some ptr → optr.Sim → ptr.Sim := by
  simp_all only [OptionRegionPtr.Sim, Veir.RegionPtr.toO]
  grind

@[grind .]
theorem Sim.OptionRegionPtr.toO_sim_of_sim (ptr : Sim.RegionPtr) :
    ptr.Sim → ptr.toO.Sim := by
  simp_all only [OptionRegionPtr.Sim, Sim.RegionPtr.toO, Veir.RegionPtr.toO]
  grind

/-! ### Op results -/

@[grind .]
theorem Sim.OpResultPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OpResultPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat ctx.spec = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.OpResultPtr.toM] at sim
  have : ptr.spec.IsRepr ctx.spec := by grind only [isRepr_of_inBounds]
  grind

#print axioms Sim.OpResultPtr.toFlat_eq_impl_toNat

@[grind .]
theorem Sim.OptionOpResultPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOpResultPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ (·.toFlat ctx.spec = ptr.impl.toNat) := by
  have sim := ib.sim
  have : ptr.spec.maybe Veir.OpResultPtr.IsRepr ctx.spec := by grind
  simp [Sim, Veir.OpResultPtr.toO, Veir.OpResultPtr.toM] at sim
  grind

@[grind.]
theorem Sim.OptionOpResultPtr.impl_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOpResultPtr} (ib : ptr.InBounds ctx) :
    ptr.impl = .none ↔ ptr.spec = .none := by
  have : ptr.spec.maybe OpResultPtr.IsRepr ctx.spec := by grind only [isRepr_of_inBounds]
  have : ptr.spec.maybe₁ (OpResultPtr.IsRepr · ctx.spec) := by grind [Option.maybe_def, Option.maybe₁_def]
  have sim := ib.sim
  simp [Sim.OptionOpResultPtr.Sim, Veir.OpResultPtr.toO, Veir.OpResultPtr.toM] at sim
  grind

@[grind .]
theorem Sim.OptionOpResultPtr.toOption_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOpResultPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = .none ↔ ptr.spec = .none := by grind

@[grind .]
theorem Sim.OptionOpResultPtr.toOption_some {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOpResultPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = some ptr' → ptr.spec = some ptr'.spec := by
  grind

@[grind .]
theorem Sim.OpResultPtr.sim_of_optionPtr_sim {ctx : Sim.IRContext OpInfo} (optr : Sim.OptionOpResultPtr) ptr :
    optr.toOption = some ptr → optr.Sim ctx.inner → ptr.Sim ctx.inner := by
  simp_all only [OptionOpResultPtr.Sim, Veir.OpResultPtr.toO]
  grind

@[grind .]
theorem Sim.OptionOpResultPtr.toO_sim_of_sim {ctx : Sim.IRContext OpInfo} (ptr : Sim.OpResultPtr) :
    ptr.Sim ctx.inner → ptr.toO.Sim ctx.inner := by
  simp_all only [OptionOpResultPtr.Sim, Sim.OpResultPtr.toO, Veir.OpResultPtr.toO]
  grind

/-! ### Block arguments -/

@[grind .]
theorem Sim.BlockArgumentPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.BlockArgumentPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.BlockArgumentPtr.toM] at sim
  have : ptr.spec.IsRepr := by grind
  grind

@[grind .]
theorem Sim.OptionBlockArgumentPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockArgumentPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ (·.toFlat = ptr.impl.toNat) := by
  have sim := ib.sim
  have : ptr.spec.maybe₁ Veir.BlockArgumentPtr.IsRepr := by grind
  simp [Sim, Veir.BlockArgumentPtr.toO, Veir.BlockArgumentPtr.toM] at sim
  grind

@[grind.]
theorem Sim.OptionBlockArgumentPtr.impl_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockArgumentPtr} (ib : ptr.InBounds ctx) :
    ptr.impl = .none ↔ ptr.spec = .none := by
  have : ptr.spec.maybe₁ BlockArgumentPtr.IsRepr := by grind
  have sim := ib.sim
  simp [Sim.OptionBlockArgumentPtr.Sim, Veir.BlockArgumentPtr.toO, Veir.BlockArgumentPtr.toM] at sim
  grind

@[grind .]
theorem Sim.OptionBlockArgumentPtr.toOption_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockArgumentPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = .none ↔ ptr.spec = .none := by grind

@[grind .]
theorem Sim.OptionBlockArgumentPtr.toOption_some {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockArgumentPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = some ptr' → ptr.spec = some ptr'.spec := by
  grind

@[grind .]
theorem Sim.BlockArgumentPtr.sim_of_optionPtr_sim (optr : Sim.OptionBlockArgumentPtr) ptr :
    optr.toOption = some ptr → optr.Sim → ptr.Sim := by
  simp_all only [OptionBlockArgumentPtr.Sim, Veir.BlockArgumentPtr.toO]
  grind

@[grind .]
theorem Sim.OptionBlockArgumentPtr.toO_sim_of_sim (ptr : Sim.BlockArgumentPtr) :
    ptr.Sim → ptr.toO.Sim := by
  simp_all only [OptionBlockArgumentPtr.Sim, Sim.BlockArgumentPtr.toO, Veir.BlockArgumentPtr.toO]
  grind

/-! ### Op operands -/

@[grind .]
theorem Sim.OpOperandPtr.sim_of_optionPtr_sim  {ctx : Sim.IRContext OpInfo} (optr : Sim.OptionOpOperandPtr) ptr :
    optr.toOption = some ptr → optr.Sim ctx.inner → ptr.Sim ctx.inner := by
  simp_all only [OptionOpOperandPtr.Sim, Veir.OpOperandPtr.toO]
  grind

@[grind .]
theorem Sim.OptionOpOperandPtr.toO_sim_of_sim {ctx : Sim.IRContext OpInfo} (ptr : Sim.OpOperandPtr) :
    ptr.Sim ctx.inner → ptr.toO.Sim ctx.inner := by
  simp_all only [OptionOpOperandPtr.Sim, Sim.OpOperandPtr.toO, Veir.OpOperandPtr.toO]
  grind

@[grind .]
theorem Sim.OpOperandPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OpOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat ctx.spec = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.OpOperandPtr.toM] at sim
  have : ptr.spec.IsRepr ctx.spec := by grind
  grind

@[grind .]
theorem Sim.OptionOpOperandPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOpOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ (·.toFlat ctx.spec = ptr.impl.toNat) := by
  have sim := ib.sim
  have : ptr.spec.maybe Veir.OpOperandPtr.IsRepr ctx.spec := by grind
  simp [Sim, Veir.OpOperandPtr.toO, Veir.OpOperandPtr.toM] at sim
  grind

@[grind .]
theorem Sim.OptionOpOperandPtr.impl_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOpOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.impl = .none ↔ ptr.spec = .none := by
  have : ptr.spec.maybe OpOperandPtr.IsRepr ctx.spec := by grind
  have : ptr.spec.maybe₁ (OpOperandPtr.IsRepr · ctx.spec) := by grind [Option.maybe_def, Option.maybe₁_def]
  have sim := ib.sim
  simp [Sim.OptionOpOperandPtr.Sim, Veir.OpOperandPtr.toO, Veir.OpOperandPtr.toM] at sim
  grind

@[grind .]
theorem Sim.OptionOpOperandPtr.toOption_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOpOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = .none ↔ ptr.spec = .none := by grind

@[grind .]
theorem Sim.OptionOpOperandPtr.toOption_some {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionOpOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = some ptr' → ptr.spec = some ptr'.spec := by
  grind

/-! ### Block operands -/

@[grind .]
theorem Sim.BlockOperandPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.BlockOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat ctx.spec = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.BlockOperandPtr.toM] at sim
  have : ptr.spec.IsRepr ctx.spec := by grind
  grind

@[grind .]
theorem Sim.OptionBlockOperandPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ (·.toFlat ctx.spec = ptr.impl.toNat) := by
  have sim := ib.sim
  have : ptr.spec.maybe Veir.BlockOperandPtr.IsRepr ctx.spec := by grind
  simp [Sim, Veir.BlockOperandPtr.toO, Veir.BlockOperandPtr.toM] at sim
  grind

@[grind.]
theorem Sim.OptionBlockOperandPtr.impl_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.impl = .none ↔ ptr.spec = .none := by
  have : ptr.spec.maybe BlockOperandPtr.IsRepr ctx.spec := by grind
  have : ptr.spec.maybe₁ (BlockOperandPtr.IsRepr · ctx.spec) := by grind [Option.maybe_def, Option.maybe₁_def]
  have sim := ib.sim
  simp [Sim.OptionBlockOperandPtr.Sim, Veir.BlockOperandPtr.toO, Veir.BlockOperandPtr.toM] at sim
  grind

@[grind .]
theorem Sim.OptionBlockOperandPtr.toOption_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = .none ↔ ptr.spec = .none := by grind

@[grind .]
theorem Sim.OptionBlockOperandPtr.toOption_some {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionBlockOperandPtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = some ptr' → ptr.spec = some ptr'.spec := by
  grind

@[grind .]
theorem Sim.BlockOperandPtr.sim_of_optionPtr_sim {ctx : Sim.IRContext OpInfo} (optr : Sim.OptionBlockOperandPtr) ptr :
    optr.toOption = some ptr → optr.Sim ctx.inner → ptr.Sim ctx.inner := by
  simp_all only [OptionBlockOperandPtr.Sim, Veir.BlockOperandPtr.toO]
  grind

@[grind .]
theorem Sim.OptionBlockOperandPtr.toO_sim_of_sim {ctx : Sim.IRContext OpInfo} (ptr : Sim.BlockOperandPtr) :
    ptr.Sim ctx.inner → ptr.toO.Sim ctx.inner := by
  simp_all only [OptionBlockOperandPtr.Sim, Sim.BlockOperandPtr.toO, Veir.BlockOperandPtr.toO]
  grind

/-! ### Values -/

@[grind .]
theorem Sim.ValuePtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.ValuePtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat ctx.spec = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.ValuePtr.toM] at sim
  have : ptr.spec.IsRepr ctx.spec := by grind
  grind

@[grind .]
theorem Sim.OptionValuePtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionValuePtr} (ib : ptr.InBounds ctx) :
    ptr.spec.maybe₁ (·.toFlat ctx.spec = ptr.impl.toNat) := by
  have sim := ib.sim
  have : ptr.spec.maybe Veir.ValuePtr.IsRepr ctx.spec := by grind
  simp [Sim, Veir.ValuePtr.toO, Veir.ValuePtr.toM] at sim
  grind

@[grind.]
theorem Sim.OptionValuePtr.impl_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionValuePtr} (ib : ptr.InBounds ctx) :
    ptr.impl = .none ↔ ptr.spec = .none := by
  have : ptr.spec.maybe ValuePtr.IsRepr ctx.spec := by grind
  have : ptr.spec.maybe₁ (ValuePtr.IsRepr · ctx.spec) := by grind [Option.maybe_def, Option.maybe₁_def]
  have sim := ib.sim
  simp [Sim.OptionValuePtr.Sim, Veir.ValuePtr.toO, Veir.ValuePtr.toM] at sim
  grind

@[grind .]
theorem Sim.OptionValuePtr.toOption_none_iff_spec_none {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionValuePtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = .none ↔ ptr.spec = .none := by grind

@[grind .]
theorem Sim.OptionValuePtr.toOption_some {ctx : Sim.IRContext OpInfo} {ptr : Sim.OptionValuePtr} (ib : ptr.InBounds ctx) :
    ptr.toOption = some ptr' → ptr.spec = some ptr'.spec := by
  grind

@[grind .]
theorem Sim.ValuePtr.sim_of_optionPtr_sim {ctx : Sim.IRContext OpInfo} (optr : Sim.OptionValuePtr) ptr :
    optr.toOption = some ptr → optr.Sim ctx.inner → ptr.Sim ctx.inner := by
  simp_all only [OptionValuePtr.Sim, Veir.ValuePtr.toO]
  grind

@[grind .]
theorem Sim.OptionValuePtr.toO_sim_of_sim {ctx : Sim.IRContext OpInfo} (ptr : Sim.ValuePtr) :
    ptr.Sim ctx.inner → ptr.toO.Sim ctx.inner := by
  simp_all only [OptionValuePtr.Sim, Sim.ValuePtr.toO, Veir.ValuePtr.toO]
  grind

@[grind .]
theorem Sim.ValuePtr.getOpOperandPtrPtr_sim_of_sim {ctx : Sim.IRContext OpInfo} (value : ValuePtr) (ib : value.InBounds ctx) :
    value.getOpOperandPtrPtr.Sim ctx.inner := by
  rcases ib with ⟨sim, ib⟩ -- need `ib` to know that there is no overflow!
  unfold Sim at sim
  unfold getOpOperandPtrPtr OpOperandPtrPtr.Sim
  rw [← sim]
  clear sim
  simp
  rcases heq : value.spec with ptr | ptr
  · simp_all
    unfold OpOperandPtrPtr.toM OpOperandPtrPtr.toFlat ValuePtr.toFlat -- OpResultPtr.toFlat
    have : ValueImpl.Offsets.firstUse.toInt.toNat.toUInt64 = ValueImpl.Offsets.firstUse.toUInt64 := by rfl
    suffices h : ptr.toFlat ctx.inner.spec + ValueImpl.Offsets.firstUse.toInt.toNat < 2^64 by
      rw [← this]
      exact UInt64.ofNat_add (ptr.toFlat ctx.inner.spec) ValueImpl.Offsets.firstUse.toInt.toNat
    have := @Sim.OpResultPtr.after_lt_ctx
    grind [layout_grind]
  · simp_all
    unfold OpOperandPtrPtr.toM OpOperandPtrPtr.toFlat ValuePtr.toFlat -- OpResultPtr.toFlat
    have := Sim.BlockArgumentPtr.after_lt_ctx (ctx := ctx) ptr (by grind)
    have : ctx.buf.mem.size < 2^63 := by grind
    suffices h : ptr.toFlat + ValueImpl.Offsets.firstUse.toInt.toNat < 2^64 by
      have : ValueImpl.Offsets.firstUse.toInt.toNat.toUInt64 = ValueImpl.Offsets.firstUse.toUInt64 := rfl
      rw [← this]
      exact UInt64.ofNat_add ptr.toFlat ValueImpl.Offsets.firstUse.toInt.toNat
    grind [layout_grind]


/-! ### Op operand pointers -/

@[grind .]
theorem Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.OpOperandPtrPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat ctx.spec = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.OpOperandPtrPtr.toM] at sim
  have : ptr.spec.IsRepr ctx.spec := by grind
  grind

@[grind .]
theorem Sim.OpOperandPtr.getOpOperandPtrPtr_sim_of_sim {ctx : Sim.IRContext OpInfo} (oper : OpOperandPtr) (ib : oper.InBounds ctx) :
    oper.getOpOperandPtrPtr.Sim ctx.inner := by
  rcases ib with ⟨sim, ib⟩ -- need `ib` to know that there is no overflow!
  unfold Sim at sim
  unfold getOpOperandPtrPtr OpOperandPtrPtr.Sim
  rw [← sim]
  clear sim
  unfold OpOperandPtrPtr.toM OpOperandPtrPtr.toFlat OpOperandPtr.toM
  dsimp
  suffices h : oper.spec.toFlat ctx.inner.spec + OpOperand.Offsets.nextUse.toInt.toNat  < 2^64 by
    exact UInt64.left_eq_add.mpr rfl
  have := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper.spec (by grind)
  have : ctx.buf.mem.size < 2^63 := by grind
  grind [layout_grind]


/-! ### Block operand pointers -/

@[grind .]
theorem Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat {ctx : Sim.IRContext OpInfo} {ptr : Sim.BlockOperandPtrPtr} (ib : ptr.InBounds ctx) :
    ptr.spec.toFlat ctx.spec = ptr.impl.toNat  := by
  have sim := ib.sim
  simp [Sim, Veir.BlockOperandPtrPtr.toM] at sim
  have : ptr.spec.IsRepr ctx.spec := by grind
  grind

@[grind .]
theorem Sim.BlockOperandPtr.getOpOperandPtrPtr_sim_of_sim {ctx : Sim.IRContext OpInfo} (oper : BlockOperandPtr) (ib : oper.InBounds ctx) :
    oper.getBlockOperandPtrPtr.Sim ctx.inner := by
  rcases ib with ⟨sim, ib⟩ -- need `ib` to know that there is no overflow!
  unfold Sim at sim
  unfold getBlockOperandPtrPtr BlockOperandPtrPtr.Sim
  rw [← sim]
  clear sim
  unfold BlockOperandPtrPtr.toM BlockOperandPtrPtr.toFlat BlockOperandPtr.toM
  dsimp
  suffices h : oper.spec.toFlat ctx.inner.spec + OpOperand.Offsets.nextUse.toInt.toNat  < 2^64 by
    exact UInt64.left_eq_add.mpr rfl
  have := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) oper.spec (by grind)
  have : ctx.buf.mem.size < 2^63 := by grind
  grind [layout_grind]

@[layout_grind =]
theorem OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt (ctx : Sim.IRContext OpInfo) (op : OperationPtr) (opIb : op.InBounds ctx.spec) (hidx : idx.toNat < countCard) :
    (op.toM.computeRegionsOffset! ctx.buf + ptrSize * idx).toInt = Operation.Offsets.regionsInt op ctx.spec + ptrSizeNat * idx.toNat := by
  have := @Operation.propertySize_lt
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have : (ptrSize * idx).toNat < 2^40 := by grind only [UInt64.toNat_mul]
  have := ctx.sim.repr.operations_indices op opIb |>.operands
  have := ctx.sim.repr.operations_indices op opIb |>.blockOperands
  have := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op (by grind)
  have : (OperationMPtr.computeRegionsOffset! ctx.buf op.toM).toInt = Operation.Offsets.regionsInt op ctx.spec := by
    rw [show op.toM = op.toSim.impl by grind]
    grind [layout_grind, OperationPtr.computeRegionsOffset!_ideal]
  rw [Int64.add_toInt_lt'] <;> grind only [UInt64.toNat_mul]


@[layout_simp, layout_grind =]
theorem Buffed.OperationMPtr.readNthRegion!_operationMPtr_writeNumResults {ctx : Sim.IRContext OpInfo} (op : Veir.OperationPtr) (ptr : Sim.OperationPtr) (idx : UInt64)
    (hidx : idx.toNat < (op.get! ctx.spec).capRegions)
    (val : UInt64) h (opIb : op.InBounds ctx.spec) (ptrIb : ptr.InBounds ctx) :
    Buffed.OperationMPtr.readNthRegion! (Buffed.OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM idx =
    Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx := by
  simp only [readNthRegion!, computeRegionOffset!]
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have := @Sim.OperationPtr.after_lt_ctx
  have hoff : (OperationMPtr.computeRegionsOffset! (OperationMPtr.writeNumResults ctx.buf ptr.impl val h) op.toM)
      = OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [computeRegionsOffset!, computeBlockOperandsOffset!, computeOperandsOffset!]
    grind (splits := 20) [readOpType!, readNumOperands!, readNumBlockOperands!, writeNumResults, layout_grind]
  rw [hoff]
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op opIb
  have disj := ctx.sim.disjoint_allocs (.operation ptr.spec) (.operation op)
  have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
  grind (splits := 20) [writeNumResults, layout_grind, OperationPtr.toM, IsDisjoint]

end Veir
