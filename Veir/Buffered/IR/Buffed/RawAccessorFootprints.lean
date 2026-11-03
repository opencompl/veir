module

public import Veir.Buffered.IR.Buffed.RawAccessors
public import Veir.Buffered.IR.Buffed.Sim
public import Veir.Buffered.IR.Buffed.SimDefs
public import Veir.Buffered.IR.Buffed.RawAccessorFootprintsGen

/-!
# Footprint lemmas for the raw accessors

Every raw accessor reads or writes a small interval of the buffer whose bounds are linear
arithmetic expressions (`base.toNat + literal offset`) once the mixed `UInt64 + Int64`
address arithmetic is known not to wrap. The lemmas in this file discharge that wrap-free
reasoning once, so that the `readX!`-after-`writeY` product lemmas reduce to disjointness
of two linear intervals.
-/

set_option linter.unusedSectionVars false

public section



namespace Veir.Buffered

open Veir.Buffered.Buffed

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

/-! ## Addresses of top-level pointers, in the linear fragment -/

theorem OperationPtr.toM_toNat {ctx : IRContext OpInfo} (repr : ctx.IsRepr)
    (op : OperationPtr) (ib : op.InBounds ctx) : op.toM.toNat = op.id := by
  have := repr.operations op ib
  grind [OperationPtr.toM, OperationPtr.toFlat, OperationPtr.IsRepr]

theorem BlockPtr.toM_toNat {ctx : IRContext OpInfo} (repr : ctx.IsRepr)
    (bl : BlockPtr) (ib : bl.InBounds ctx) : bl.toM.toNat = bl.id := by
  have := repr.blocks bl ib
  grind [BlockPtr.toM, BlockPtr.toFlat, BlockPtr.IsRepr]

theorem RegionPtr.toM_toNat {ctx : IRContext OpInfo} (repr : ctx.IsRepr)
    (rg : RegionPtr) (ib : rg.InBounds ctx) : rg.toM.toNat = rg.id := by
  have := repr.regions rg ib
  grind [RegionPtr.toM, RegionPtr.toFlat, RegionPtr.IsRepr]

/-! ## Hoisted context facts -/

namespace Sim

variable {ctx : Sim.IRContext OpInfo}

theorem IRContext.mem_size_lt (ctx : Sim.IRContext OpInfo) :
    (ctx.buf.mem.size : Int) < Int64.maxValue.toInt := by
  have := ctx.buf.mem.fits_in_memory
  grind

/-! ## Allocation ranges of top-level pointers, in the linear fragment -/

theorem OperationPtr.range_linear (op : Veir.Buffered.OperationPtr) (ib : op.InBounds ctx.spec) :
    0 ≤ (op.id : Int) + Buffed.Operation.Offsets.resultsInt op ctx.spec ∧
    (op.id : Int) + Buffed.Operation.Offsets.afterInt op ctx.spec ≤ ctx.buf.mem.size := by
  have := ctx.sim.in_bounds (.operation op) (by grind)
  have := ctx.sim.repr.operations op ib
  have := ctx.sim.repr.operations_indices op ib
  grind [Veir.Buffered.OperationPtr.range, Veir.Buffered.OperationPtr.toFlat, IsIncludedIN,
    Buffed.Operation.Offsets.results_ideal]

theorem BlockPtr.range_linear (bl : Veir.Buffered.BlockPtr) (ib : bl.InBounds ctx.spec) :
    0 ≤ (bl.id : Int) ∧
    (bl.id : Int) + Buffed.Block.Offsets.afterInt bl ctx.spec ≤ ctx.buf.mem.size := by
  have := ctx.sim.in_bounds (.block bl) (by grind)
  have := ctx.sim.repr.blocks bl ib
  have := ctx.sim.repr.blocks_indices bl ib
  grind [Veir.Buffered.BlockPtr.range, Veir.Buffered.BlockPtr.toFlat, IsIncludedIN]

theorem RegionPtr.range_linear (rg : Veir.Buffered.RegionPtr) (ib : rg.InBounds ctx.spec) :
    0 ≤ (rg.id : Int) ∧
    (rg.id : Int) + Buffed.Region.Offsets.afterInt ≤ ctx.buf.mem.size := by
  have := ctx.sim.in_bounds (.region rg) (by grind)
  grind [Veir.Buffered.RegionPtr.range, Veir.Buffered.RegionPtr.toFlat, IsIncludedIN]

/-! ## A sub-struct pointer in bounds has its parent in bounds -/

theorem OpResultPtr.op_inBounds {res : Veir.Buffered.OpResultPtr} (ib : res.InBounds ctx.spec) :
    res.op.InBounds ctx.spec := by grind [Veir.Buffered.OpResultPtr.inBounds_def]

theorem OpOperandPtr.op_inBounds {opr : Veir.Buffered.OpOperandPtr} (ib : opr.InBounds ctx.spec) :
    opr.op.InBounds ctx.spec := by grind [Veir.Buffered.OpOperandPtr.inBounds_def]

theorem BlockOperandPtr.op_inBounds {opr : Veir.Buffered.BlockOperandPtr} (ib : opr.InBounds ctx.spec) :
    opr.op.InBounds ctx.spec := by grind [Veir.Buffered.BlockOperandPtr.inBounds_def]

theorem BlockArgumentPtr.block_inBounds {arg : Veir.Buffered.BlockArgumentPtr} (ib : arg.InBounds ctx.spec) :
    arg.block.InBounds ctx.spec := by grind [Veir.Buffered.BlockArgumentPtr.inBounds_def]

/-! ## Addresses of sub-struct pointers, in the linear fragment -/

theorem OpResultPtr.toM_toNat (res : Veir.Buffered.OpResultPtr) (ib : res.InBounds ctx.spec) :
    (res.toM ctx.spec).toNat = res.toFlatNat ctx.spec := by
  have := Sim.OpResultPtr.after_lt_ctx res ib
  have := IRContext.mem_size_lt ctx
  have := Veir.Buffered.OpResultPtr.toFlat_ideal ctx.sim.repr res ib
  grind [Veir.Buffered.OpResultPtr.toM]

theorem OpOperandPtr.toM_toNat (opr : Veir.Buffered.OpOperandPtr) (ib : opr.InBounds ctx.spec) :
    (opr.toM ctx.spec).toNat = opr.toFlatNat ctx.spec := by
  have := Sim.OpOperandPtr.after_lt_ctx opr ib
  have := IRContext.mem_size_lt ctx
  have := Veir.Buffered.OpOperandPtr.toFlat_ideal ctx.sim.repr opr ib
  grind [Veir.Buffered.OpOperandPtr.toM]

theorem BlockOperandPtr.toM_toNat (opr : Veir.Buffered.BlockOperandPtr) (ib : opr.InBounds ctx.spec) :
    (opr.toM ctx.spec).toNat = opr.toFlatNat ctx.spec := by
  have := Sim.BlockOperandPtr.after_lt_ctx opr ib
  have := IRContext.mem_size_lt ctx
  have := Veir.Buffered.BlockOperandPtr.toFlat_ideal ctx.sim.repr opr ib
  grind [Veir.Buffered.BlockOperandPtr.toM]

theorem BlockArgumentPtr.toM_toNat (arg : Veir.Buffered.BlockArgumentPtr) (ib : arg.InBounds ctx.spec) :
    arg.toM.toNat = arg.toFlatNat := by
  have := Sim.BlockArgumentPtr.after_lt_ctx arg ib
  have := IRContext.mem_size_lt ctx
  have := Veir.Buffered.BlockArgumentPtr.toFlat_ideal arg
  grind [Veir.Buffered.BlockArgumentPtr.toM]

/-! ## Allocation ranges of sub-struct pointers included in their parent's, `rangeInt` form -/

theorem OpResultPtr.rangeInt_included (res : Veir.Buffered.OpResultPtr) (ib : res.InBounds ctx.spec) :
    IsIncludedI (res.rangeInt ctx.spec) (res.op.rangeInt ctx.spec) := by
  have := Veir.Buffered.OpResultPtr.range_included_op_range (ctx := ctx) res ib
  have hop : res.op.InBounds ctx.spec := by grind
  rw [Veir.Buffered.OpResultPtr.range_ideal ctx.sim.repr ib, Veir.Buffered.OperationPtr.range_ideal ctx.sim.repr hop] at this
  exact this

theorem OpOperandPtr.rangeInt_included (opr : Veir.Buffered.OpOperandPtr) (ib : opr.InBounds ctx.spec) :
    IsIncludedI (opr.rangeInt ctx.spec) (opr.op.rangeInt ctx.spec) := by
  have := Veir.Buffered.OpOperandPtr.range_included_op_range (ctx := ctx.spec) ctx.sim.repr opr ib
  have hop : opr.op.InBounds ctx.spec := by grind
  rw [Veir.Buffered.OpOperandPtr.range_ideal ctx.sim.repr ib, Veir.Buffered.OperationPtr.range_ideal ctx.sim.repr hop] at this
  exact this

theorem BlockOperandPtr.rangeInt_included (opr : Veir.Buffered.BlockOperandPtr) (ib : opr.InBounds ctx.spec) :
    IsIncludedI (opr.rangeInt ctx.spec) (opr.op.rangeInt ctx.spec) := by
  have := Veir.Buffered.BlockOperandPtr.range_included_op_range (ctx := ctx.spec) ctx.sim.repr opr ib
  have hop : opr.op.InBounds ctx.spec := by grind
  rw [Veir.Buffered.BlockOperandPtr.range_ideal ctx.sim.repr ib, Veir.Buffered.OperationPtr.range_ideal ctx.sim.repr hop] at this
  exact this

theorem BlockArgumentPtr.rangeInt_included (arg : Veir.Buffered.BlockArgumentPtr) (ib : arg.InBounds ctx.spec) :
    IsIncludedI (arg.rangeInt) (arg.block.rangeInt ctx.spec) := by
  have := Veir.Buffered.BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) ctx.sim.repr arg ib
  have hbl : arg.block.InBounds ctx.spec := by grind
  rw [Veir.Buffered.BlockArgumentPtr.range_ideal, Veir.Buffered.BlockPtr.range_ideal ctx.sim.repr hbl] at this
  exact this

/-! ## A sub-struct slot lies inside its dedicated region of the parent's allocation.
Tighter than `rangeInt_included`: distinguishes the results/operands/blockOperands/arguments
regions, so that two slots of different kinds in the same parent are linearly disjoint. -/

theorem OpResultPtr.slot_included (res : Veir.Buffered.OpResultPtr) (ib : res.InBounds ctx.spec) :
    IsIncludedI ((res.toFlatNat ctx.spec : Int)...((res.toFlatNat ctx.spec : Int) + Buffed.OpResult.sizeNat))
      (((res.op.id : Int) + Buffed.Operation.Offsets.resultsInt res.op ctx.spec)...((res.op.id : Int))) := by
  have hop := OpResultPtr.op_inBounds ib
  have := OperationPtr.range_linear res.op hop
  have := ctx.sim.repr.operations_indices res.op hop |>.capResults
  have := Veir.Buffered.OperationPtr.getNumResults!_eq_getNumResults (ctx := ctx.spec) (op := res.op) hop
  grind [Veir.Buffered.OpResultPtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, IsIncludedI,
    Veir.Buffered.OpResultPtr.inBounds_def]

theorem OpOperandPtr.slot_included (opr : Veir.Buffered.OpOperandPtr) (ib : opr.InBounds ctx.spec) :
    IsIncludedI ((opr.toFlatNat ctx.spec : Int)...((opr.toFlatNat ctx.spec : Int) + Buffed.OpOperand.sizeNat))
      (((opr.op.id : Int) + Buffed.Operation.Offsets.operandsInt opr.op ctx.spec)...
       ((opr.op.id : Int) + Buffed.Operation.Offsets.blockOperandsInt opr.op ctx.spec)) := by
  have hop := OpOperandPtr.op_inBounds ib
  have := OperationPtr.range_linear opr.op hop
  have := ctx.sim.repr.operations_indices opr.op hop |>.capOperands
  have := Veir.Buffered.OperationPtr.getNumOperands!_eq_getNumOperands (ctx := ctx.spec) (op := opr.op) hop
  grind [Veir.Buffered.OpOperandPtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, IsIncludedI,
    Veir.Buffered.OpOperandPtr.inBounds_def]

theorem BlockOperandPtr.slot_included (opr : Veir.Buffered.BlockOperandPtr) (ib : opr.InBounds ctx.spec) :
    IsIncludedI ((opr.toFlatNat ctx.spec : Int)...((opr.toFlatNat ctx.spec : Int) + Buffed.BlockOperand.sizeNat))
      (((opr.op.id : Int) + Buffed.Operation.Offsets.blockOperandsInt opr.op ctx.spec)...
       ((opr.op.id : Int) + Buffed.Operation.Offsets.regionsInt opr.op ctx.spec)) := by
  have hop := BlockOperandPtr.op_inBounds ib
  have := OperationPtr.range_linear opr.op hop
  have := ctx.sim.repr.operations_indices opr.op hop |>.capBlockOperands
  have := Veir.Buffered.OperationPtr.getNumSuccessors!_eq_getNumSuccessors (ctx := ctx.spec) (op := opr.op) hop
  grind [Veir.Buffered.BlockOperandPtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, IsIncludedI,
    Veir.Buffered.BlockOperandPtr.inBounds_def]

theorem BlockArgumentPtr.slot_included (arg : Veir.Buffered.BlockArgumentPtr) (ib : arg.InBounds ctx.spec) :
    IsIncludedI ((arg.toFlatNat : Int)...((arg.toFlatNat : Int) + Buffed.BlockArgument.sizeNat))
      (((arg.block.id : Int) + Buffed.Block.Offsets.argumentsInt)...
       ((arg.block.id : Int) + Buffed.Block.Offsets.afterInt arg.block ctx.spec)) := by
  have hbl := BlockArgumentPtr.block_inBounds ib
  have := BlockPtr.range_linear arg.block hbl
  have := ctx.sim.repr.blocks_indices arg.block hbl |>.capArguments
  have := Veir.Buffered.BlockPtr.getNumArguments!_eq_getNumArguments (ctx := ctx.spec) (block := arg.block) hbl
  grind [Veir.Buffered.BlockArgumentPtr.toFlatNat, Veir.Buffered.BlockPtr.toFlat, IsIncludedI,
    Veir.Buffered.BlockArgumentPtr.inBounds_def]

/-! ## Disjointness of two distinct allocations, `rangeInt` form -/

theorem disjoint_operation_operation (op₁ op₂ : Veir.Buffered.OperationPtr)
    (h₁ : op₁.InBounds ctx.spec) (h₂ : op₂.InBounds ctx.spec) (hneq : op₁ ≠ op₂) :
    IsDisjointI (op₁.rangeInt ctx.spec) (op₂.rangeInt ctx.spec) := by
  have := ctx.sim.disjoint_allocs (.operation op₁) (.operation op₂) (by grind) (by grind) (by grind)
  simp only [TopLevelPtr.range] at this
  rw [Veir.Buffered.OperationPtr.range_ideal ctx.sim.repr h₁, Veir.Buffered.OperationPtr.range_ideal ctx.sim.repr h₂] at this
  exact this

theorem disjoint_operation_block (op : Veir.Buffered.OperationPtr) (bl : Veir.Buffered.BlockPtr)
    (h₁ : op.InBounds ctx.spec) (h₂ : bl.InBounds ctx.spec) :
    IsDisjointI (op.rangeInt ctx.spec) (bl.rangeInt ctx.spec) := by
  have := ctx.sim.disjoint_allocs (.operation op) (.block bl) (by grind) (by grind) (by grind)
  simp only [TopLevelPtr.range] at this
  rw [Veir.Buffered.OperationPtr.range_ideal ctx.sim.repr h₁, Veir.Buffered.BlockPtr.range_ideal ctx.sim.repr h₂] at this
  exact this

theorem disjoint_operation_region (op : Veir.Buffered.OperationPtr) (rg : Veir.Buffered.RegionPtr)
    (h₁ : op.InBounds ctx.spec) (h₂ : rg.InBounds ctx.spec) :
    IsDisjointI (op.rangeInt ctx.spec) (rg.rangeInt) := by
  have := ctx.sim.disjoint_allocs (.operation op) (.region rg) (by grind) (by grind) (by grind)
  simp only [TopLevelPtr.range] at this
  rw [Veir.Buffered.OperationPtr.range_ideal ctx.sim.repr h₁, Veir.Buffered.RegionPtr.range_ideal] at this
  exact this

theorem disjoint_block_block (bl₁ bl₂ : Veir.Buffered.BlockPtr)
    (h₁ : bl₁.InBounds ctx.spec) (h₂ : bl₂.InBounds ctx.spec) (hneq : bl₁ ≠ bl₂) :
    IsDisjointI (bl₁.rangeInt ctx.spec) (bl₂.rangeInt ctx.spec) := by
  have := ctx.sim.disjoint_allocs (.block bl₁) (.block bl₂) (by grind) (by grind) (by grind)
  simp only [TopLevelPtr.range] at this
  rw [Veir.Buffered.BlockPtr.range_ideal ctx.sim.repr h₁, Veir.Buffered.BlockPtr.range_ideal ctx.sim.repr h₂] at this
  exact this

theorem disjoint_block_operation (bl : Veir.Buffered.BlockPtr) (op : Veir.Buffered.OperationPtr)
    (h₁ : bl.InBounds ctx.spec) (h₂ : op.InBounds ctx.spec) :
    IsDisjointI (bl.rangeInt ctx.spec) (op.rangeInt ctx.spec) := by
  have := ctx.sim.disjoint_allocs (.block bl) (.operation op) (by grind) (by grind) (by grind)
  simp only [TopLevelPtr.range] at this
  rw [Veir.Buffered.BlockPtr.range_ideal ctx.sim.repr h₁, Veir.Buffered.OperationPtr.range_ideal ctx.sim.repr h₂] at this
  exact this

theorem disjoint_block_region (bl : Veir.Buffered.BlockPtr) (rg : Veir.Buffered.RegionPtr)
    (h₁ : bl.InBounds ctx.spec) (h₂ : rg.InBounds ctx.spec) :
    IsDisjointI (bl.rangeInt ctx.spec) (rg.rangeInt) := by
  have := ctx.sim.disjoint_allocs (.block bl) (.region rg) (by grind) (by grind) (by grind)
  simp only [TopLevelPtr.range] at this
  rw [Veir.Buffered.BlockPtr.range_ideal ctx.sim.repr h₁, Veir.Buffered.RegionPtr.range_ideal] at this
  exact this

theorem disjoint_region_region (rg₁ rg₂ : Veir.Buffered.RegionPtr)
    (h₁ : rg₁.InBounds ctx.spec) (h₂ : rg₂.InBounds ctx.spec) (hneq : rg₁ ≠ rg₂) :
    IsDisjointI (rg₁.rangeInt) (rg₂.rangeInt) := by
  have := ctx.sim.disjoint_allocs (.region rg₁) (.region rg₂) (by grind) (by grind) (by grind)
  simp only [TopLevelPtr.range] at this
  rw [Veir.Buffered.RegionPtr.range_ideal, Veir.Buffered.RegionPtr.range_ideal] at this
  exact this

theorem disjoint_region_operation (rg : Veir.Buffered.RegionPtr) (op : Veir.Buffered.OperationPtr)
    (h₁ : rg.InBounds ctx.spec) (h₂ : op.InBounds ctx.spec) :
    IsDisjointI (rg.rangeInt) (op.rangeInt ctx.spec) := by
  have := ctx.sim.disjoint_allocs (.region rg) (.operation op) (by grind) (by grind) (by grind)
  simp only [TopLevelPtr.range] at this
  rw [Veir.Buffered.RegionPtr.range_ideal, Veir.Buffered.OperationPtr.range_ideal ctx.sim.repr h₂] at this
  exact this

theorem disjoint_region_block (rg : Veir.Buffered.RegionPtr) (bl : Veir.Buffered.BlockPtr)
    (h₁ : rg.InBounds ctx.spec) (h₂ : bl.InBounds ctx.spec) :
    IsDisjointI (rg.rangeInt) (bl.rangeInt ctx.spec) := by
  have := ctx.sim.disjoint_allocs (.region rg) (.block bl) (by grind) (by grind) (by grind)
  simp only [TopLevelPtr.range] at this
  rw [Veir.Buffered.RegionPtr.range_ideal, Veir.Buffered.BlockPtr.range_ideal ctx.sim.repr h₂] at this
  exact this

/-! ## Sum pointers (`ValuePtr`, `OpOperandPtrPtr`, `BlockOperandPtrPtr`): implementation
address, and disjointness of their footprint from any operation header. A value or use-list
slot never overlaps the fixed header fields of any operation, even its own parent's. -/

theorem ValuePtr.impl_toNat (v : Veir.Buffered.Sim.ValuePtr) (ib : v.InBounds ctx) :
    v.impl.toNat = v.spec.toFlatNat ctx.spec := by
  have := Sim.ValuePtr.toFlat_eq_impl_toNat ib
  have := Veir.Buffered.ValuePtr.toFlat_ideal ctx.sim.repr v.spec ib.ib
  grind

theorem OpOperandPtrPtr.impl_toNat (p : Veir.Buffered.Sim.OpOperandPtrPtr) (ib : p.InBounds ctx) :
    p.impl.toNat = p.spec.toFlatNat ctx.spec := by
  have := Sim.OpOperandPtrPtr.toFlat_eq_impl_toNat ib
  have := Veir.Buffered.OpOperandPtrPtr.toFlat_ideal ctx.sim.repr p.spec ib.ib
  grind

theorem BlockOperandPtrPtr.impl_toNat (p : Veir.Buffered.Sim.BlockOperandPtrPtr) (ib : p.InBounds ctx) :
    p.impl.toNat = p.spec.toFlatNat ctx.spec := by
  have := Sim.BlockOperandPtrPtr.toFlat_eq_impl_toNat ib
  have := Veir.Buffered.BlockOperandPtrPtr.toFlat_ideal ctx.sim.repr p.spec ib.ib
  grind

theorem ValuePtr.disjoint_operation_header (v : Veir.Buffered.ValuePtr) (ib : v.InBounds ctx.spec)
    (op : Veir.Buffered.OperationPtr) (hop : op.InBounds ctx.spec) :
    IsDisjointI ((v.toFlatNat ctx.spec : Int)...((v.toFlatNat ctx.spec : Int) + Buffed.ValueImpl.sizeNat))
      ((op.id : Int)...((op.id : Int) + Buffed.Operation.Offsets.operandsInt op ctx.spec)) := by
  have hrange_o := OperationPtr.range_linear op hop
  cases v with
  | opResult res =>
    have hib : res.InBounds ctx.spec := by grind [Veir.Buffered.ValuePtr.InBounds]
    have hpib := OpResultPtr.op_inBounds hib
    have hsl := OpResultPtr.slot_included res hib
    have hrange_p := OperationPtr.range_linear res.op hpib
    have hdisj := fun hne : res.op ≠ op => disjoint_operation_operation res.op op hpib hop hne
    grind [Veir.Buffered.ValuePtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, IsIncludedI]
  | blockArgument arg =>
    have hib : arg.InBounds ctx.spec := by grind [Veir.Buffered.ValuePtr.InBounds]
    have hpib := BlockArgumentPtr.block_inBounds hib
    have hsl := BlockArgumentPtr.slot_included arg hib
    have hrange_p := BlockPtr.range_linear arg.block hpib
    have hdisj := disjoint_block_operation arg.block op hpib hop
    grind [Veir.Buffered.ValuePtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, Veir.Buffered.BlockPtr.toFlat,
      Veir.Buffered.BlockPtr.rangeInt, IsIncludedI]

theorem OpOperandPtrPtr.disjoint_operation_header (p : Veir.Buffered.OpOperandPtrPtr) (ib : p.InBounds ctx.spec)
    (op : Veir.Buffered.OperationPtr) (hop : op.InBounds ctx.spec) :
    IsDisjointI ((p.toFlatNat ctx.spec : Int)...((p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat))
      ((op.id : Int)...((op.id : Int) + Buffed.Operation.Offsets.operandsInt op ctx.spec)) := by
  have hrange_o := OperationPtr.range_linear op hop
  cases p with
  | operandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.Buffered.OpOperandPtrPtr.InBounds]
    have hpib := OpOperandPtr.op_inBounds hib
    have hsl := OpOperandPtr.slot_included opr hib
    have hrange_p := OperationPtr.range_linear opr.op hpib
    have hdisj := fun hne : opr.op ≠ op => disjoint_operation_operation opr.op op hpib hop hne
    grind [Veir.Buffered.OpOperandPtrPtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, IsIncludedI]
  | valueFirstUse v =>
    have hib : v.InBounds ctx.spec := by grind [Veir.Buffered.OpOperandPtrPtr.InBounds]
    have hdisj := ValuePtr.disjoint_operation_header v hib op hop
    grind [Veir.Buffered.OpOperandPtrPtr.toFlatNat, IsIncludedI]

theorem BlockOperandPtrPtr.disjoint_operation_header (p : Veir.Buffered.BlockOperandPtrPtr) (ib : p.InBounds ctx.spec)
    (op : Veir.Buffered.OperationPtr) (hop : op.InBounds ctx.spec) :
    IsDisjointI ((p.toFlatNat ctx.spec : Int)...((p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat))
      ((op.id : Int)...((op.id : Int) + Buffed.Operation.Offsets.operandsInt op ctx.spec)) := by
  have hrange_o := OperationPtr.range_linear op hop
  cases p with
  | blockOperandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.Buffered.BlockOperandPtrPtr.InBounds]
    have hpib := BlockOperandPtr.op_inBounds hib
    have hsl := BlockOperandPtr.slot_included opr hib
    have hrange_p := OperationPtr.range_linear opr.op hpib
    have hdisj := fun hne : opr.op ≠ op => disjoint_operation_operation opr.op op hpib hop hne
    grind [Veir.Buffered.BlockOperandPtrPtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, IsIncludedI]
  | blockFirstUse bl =>
    have hib : bl.InBounds ctx.spec := by grind [Veir.Buffered.BlockOperandPtrPtr.InBounds]
    have hrange_p := BlockPtr.range_linear bl hib
    have hdisj := disjoint_block_operation bl op hib hop
    grind [Veir.Buffered.BlockOperandPtrPtr.toFlatNat, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.BlockPtr.rangeInt, IsIncludedI]

/-- The footprint of a value's header fields fits in the buffer. -/
theorem ValuePtr.footprint_bound (v : Veir.Buffered.ValuePtr) (ib : v.InBounds ctx.spec) :
    (v.toFlatNat ctx.spec : Int) + Buffed.ValueImpl.sizeNat ≤ ctx.buf.mem.size := by
  cases v with
  | opResult res =>
    have hib : res.InBounds ctx.spec := by grind [Veir.Buffered.ValuePtr.InBounds]
    have := OpResultPtr.slot_included res hib
    have := OperationPtr.range_linear res.op (OpResultPtr.op_inBounds hib)
    grind [Veir.Buffered.ValuePtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, IsIncludedI]
  | blockArgument arg =>
    have hib : arg.InBounds ctx.spec := by grind [Veir.Buffered.ValuePtr.InBounds]
    have := BlockArgumentPtr.slot_included arg hib
    have := BlockPtr.range_linear arg.block (BlockArgumentPtr.block_inBounds hib)
    grind [Veir.Buffered.ValuePtr.toFlatNat, Veir.Buffered.BlockPtr.toFlat, IsIncludedI]

theorem OpOperandPtrPtr.footprint_bound (p : Veir.Buffered.OpOperandPtrPtr) (ib : p.InBounds ctx.spec) :
    (p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat ≤ ctx.buf.mem.size := by
  cases p with
  | operandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.Buffered.OpOperandPtrPtr.InBounds]
    have := OpOperandPtr.slot_included opr hib
    have := OperationPtr.range_linear opr.op (OpOperandPtr.op_inBounds hib)
    grind [Veir.Buffered.OpOperandPtrPtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, IsIncludedI]
  | valueFirstUse v =>
    have hib : v.InBounds ctx.spec := by grind [Veir.Buffered.OpOperandPtrPtr.InBounds]
    have := ValuePtr.footprint_bound v hib
    grind [Veir.Buffered.OpOperandPtrPtr.toFlatNat]

theorem BlockOperandPtrPtr.footprint_bound (p : Veir.Buffered.BlockOperandPtrPtr) (ib : p.InBounds ctx.spec) :
    (p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat ≤ ctx.buf.mem.size := by
  cases p with
  | blockOperandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.Buffered.BlockOperandPtrPtr.InBounds]
    have := BlockOperandPtr.slot_included opr hib
    have := OperationPtr.range_linear opr.op (BlockOperandPtr.op_inBounds hib)
    grind [Veir.Buffered.BlockOperandPtrPtr.toFlatNat, Veir.Buffered.OperationPtr.toFlat, IsIncludedI]
  | blockFirstUse bl =>
    have hib : bl.InBounds ctx.spec := by grind [Veir.Buffered.BlockOperandPtrPtr.InBounds]
    have := BlockPtr.range_linear bl hib
    grind [Veir.Buffered.BlockOperandPtrPtr.toFlatNat, Veir.Buffered.BlockPtr.toFlat]

end Sim


end Veir.Buffered
