module

import Veir.IR.Buffed.SetterMacro
public import Veir.IR.Buffed.Sim
public import Veir.IR.Basic
public import Veir.IR.WellFormed
import Veir.IR.InBounds
import Veir.IR.LayoutUnchanged
import Veir.IR.GetSet
import Veir.IR.Buffed.Meta
import Veir.IR.Buffed.RawAccessorsLemmas
import Veir.IR.Buffed.RawReadWriteLemmas
import Veir.IR.Buffed.Frames

import all Init.Util


set_option linter.unusedSectionVars false

@[expose] public section

namespace Veir

open Buffed (countCard)

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

/- Spec transformations with multiple inputs pack them into `Erased.mk` before mapping,
so the callback never captures a noncomputable `.spec` projection. -/

/- Shared bounds proofs passed to the `Buffed.*MPtr.write*` calls in the setters. -/
set_option hygiene false in
macro "prove_setLinkBoundsOp" ctx:ident ptr:ident : tactic => `(tactic|
  (have incl : IsIncludedIN (($ptr).spec.range ($ctx).spec) ($ctx).buf.mem.range := by
     grind [($ctx).sim.in_bounds (.operation ($ptr).spec)]
   have : ctx.buf.mem.size < 2^63 := by grind
   grind [layout_grind]))

set_option hygiene false in
macro "prove_setLinkBoundsBlock" ctx:ident ptr:ident : tactic => `(tactic|
  (have incl : IsIncludedIN (($ptr).spec.range ($ctx).spec) ($ctx).buf.mem.range := by
     grind [($ctx).sim.in_bounds (.block ($ptr).spec)]
   have : ctx.buf.mem.size < 2^63 := by grind
   grind [layout_grind]))

set_option hygiene false in
macro "prove_setLinkBoundsRegion" ctx:ident ptr:ident : tactic => `(tactic|
  (have incl : IsIncludedIN ($ptr).spec.range ($ctx).buf.mem.range := by
     grind [($ctx).sim.in_bounds (.region ($ptr).spec)]
   have : ctx.buf.mem.size < 2^63 := by grind
   grind [layout_grind]))

/- Bounds proof for reading the `$index`-th region *slot* of an operation (`readNthRegion`'s `h₂`): the slot lies inside the op's byte range (`nthRegion_range_included_op_range`), which in turn lies in the buffer (`sim.in_bounds`). -/
set_option hygiene false in
macro "prove_setLinkBoundsRegionSlot" ctx:ident ptr:ident index:ident : tactic => `(tactic|
  (have hcap : ($index).toNat < (($ptr).spec.get! ($ctx).spec).capRegions := by
     have := ($ctx).isRepr.operations_indices ($ptr).spec (by grind) |>.capRegions
     grind
   have hincl := OperationPtr.nthRegion_range_included_op_range $ctx ($ptr).spec $index hcap (by grind)
   have hin := ($ctx).sim.in_bounds (.operation ($ptr).spec) (by grind)
   have : ($ctx).buf.mem.size < 2^63 := by grind
   grind [layout_grind, OperationPtr.range, OperationPtr.toM, OperationPtr.toFlat,
     Buffed.OperationMPtr.computeRegionOffset, IsIncludedI, IsIncludedIN]))

/- Bounds proofs for writing the `$index`-th result/operand/block-operand slot of an operation (the `hslot` argument of `Rewriter.set{Result,Operand,BlockOperand}`), and the `$index`-th argument slot of a block (`Rewriter.setBlockArgument`'s `hslot`). -/
set_option hygiene false in
macro "prove_setLinkBoundsResultSlot" ctx:ident ptr:ident index:ident : tactic => `(tactic|
  (have hcap : ($index).toNat < (($ptr).spec.get! ($ctx).spec).capResults := by grind
   have hincl := OperationPtr.nthResult_range_included_op_range $ctx ($ptr).spec $index hcap (by grind)
   have hin := ($ctx).sim.in_bounds (.operation ($ptr).spec) (by grind)
   have : ($ctx).buf.mem.size < 2^63 := by grind
   -- Pin the nonlinear pieces grind won't derive itself: the ideal form of the base offset, `idx < 2^32` (via `ReprIndices`), and the `UInt64` multiplication in `Nat` form.
   have hoff := OperationPtr.computeResultsOffset!_ideal $ctx $ptr (by grind) (by grind)
     (by prove_setLinkBoundsOp $ctx $ptr)
   have hidxlt : ($index).toNat < 4294967296 := by
     have := ($ctx).isRepr.operations_indices ($ptr).spec (by grind) |>.capResults
     grind
   have hmul : (Buffed.OpResult.size * $index).toNat = Buffed.OpResult.sizeNat * ($index).toNat := by
     rw [UInt64.toNat_mul]
     grind
   grind [layout_grind, OperationPtr.range, OperationPtr.toM, OperationPtr.toFlat,
     Buffed.OperationMPtr.getResultPtr, Buffed.OperationMPtr.getResultPtr!,
     Buffed.OperationMPtr.computeResultOffset, Buffed.OperationMPtr.computeResultOffset!,
     IsIncludedI, IsIncludedIN]))

set_option hygiene false in
macro "prove_setLinkBoundsOperandSlot" ctx:ident ptr:ident index:ident : tactic => `(tactic|
  (have hcap : ($index).toNat < (($ptr).spec.get! ($ctx).spec).capOperands := by grind
   have hincl := OperationPtr.nthOperand_range_included_op_range $ctx ($ptr).spec $index hcap (by grind)
   have hin := ($ctx).sim.in_bounds (.operation ($ptr).spec) (by grind)
   have : ($ctx).buf.mem.size < 2^63 := by grind
   have hoff := OperationPtr.computeOperandsOffset!_ideal $ctx $ptr (by grind) (by grind)
     (by prove_setLinkBoundsOp $ctx $ptr)
   have hidxlt : ($index).toNat < 4294967296 := by
     have := ($ctx).isRepr.operations_indices ($ptr).spec (by grind) |>.capOperands
     grind
   have hmul : (Buffed.OpOperand.size * $index).toNat = Buffed.OpOperand.sizeNat * ($index).toNat := by
     rw [UInt64.toNat_mul]
     grind
   grind [layout_grind, OperationPtr.range, OperationPtr.toM, OperationPtr.toFlat,
     Buffed.OperationMPtr.computeOperandOffset, Buffed.OperationMPtr.computeOperandOffset!,
     IsIncludedI, IsIncludedIN]))

set_option hygiene false in
macro "prove_setLinkBoundsBlockOperandSlot" ctx:ident ptr:ident index:ident : tactic => `(tactic|
  (have hcap : ($index).toNat < (($ptr).spec.get! ($ctx).spec).capBlockOperands := by grind
   have hincl := OperationPtr.nthBlockOperand_range_included_op_range $ctx ($ptr).spec $index hcap (by grind)
   have hin := ($ctx).sim.in_bounds (.operation ($ptr).spec) (by grind)
   have : ($ctx).buf.mem.size < 2^63 := by grind
   have hoff := OperationPtr.computeBlockOperandsOffset!_ideal $ctx $ptr (by grind) (by grind)
     (by prove_setLinkBoundsOp $ctx $ptr)
   have hidxlt : ($index).toNat < 4294967296 := by
     have := ($ctx).isRepr.operations_indices ($ptr).spec (by grind) |>.capBlockOperands
     grind
   have hmul : (Buffed.BlockOperand.size * $index).toNat = Buffed.BlockOperand.sizeNat * ($index).toNat := by
     rw [UInt64.toNat_mul]
     grind
   grind [layout_grind, OperationPtr.range, OperationPtr.toM, OperationPtr.toFlat,
     Buffed.OperationMPtr.computeBlockOperandOffset, Buffed.OperationMPtr.computeBlockOperandOffset!,
     IsIncludedI, IsIncludedIN]))

set_option hygiene false in
macro "prove_setLinkBoundsArgumentSlot" ctx:ident ptr:ident index:ident : tactic => `(tactic|
  (have hcap : ($index).toNat < (($ptr).spec.get! ($ctx).spec).capArguments := by grind
   have hincl := BlockPtr.nthArgument_range_included_block_range $ctx ($ptr).spec $index hcap (by grind)
   have hoff := BlockPtr.computeArgumentOffset_ideal $ctx $ptr $index (by grind) hcap
   have hin := ($ctx).sim.in_bounds (.block ($ptr).spec) (by grind)
   have : ($ctx).buf.mem.size < 2^63 := by grind
   grind [layout_grind, BlockPtr.range, BlockPtr.toM, BlockPtr.toFlat,
     Buffed.BlockMPtr.getArgumentPtr, IsIncludedI, IsIncludedIN]))

set_option hygiene false in
macro "prove_setLinkBoundsValue" : tactic => `(tactic|
  (have : ctx.buf.mem.size < 2^63 := by grind
   have := @Sim.ValuePtr.after_lt_ctx
   grind [layout_grind]))

set_option hygiene false in
macro "prove_setLinkBoundsOpOperand" ctx:ident ptr:ident : tactic => `(tactic|
  (have ⟨_, _⟩ := ($ctx).sim.in_bounds (.operation ($ptr).spec.op) (by grind)
   have : ctx.buf.mem.size < 2^63 := by grind
   have hincl := OpOperandPtr.range_included_op_range (ctx := ($ctx).spec) (by grind) ($ptr).spec (by grind)
   grind [layout_grind]))

set_option hygiene false in
macro "prove_setLinkBoundsOpResult" ctx:ident ptr:ident : tactic => `(tactic|
  (have ⟨_, _⟩ := ($ctx).sim.in_bounds (.operation ($ptr).spec.op) (by grind)
   have : ctx.buf.mem.size < 2^63 := by grind
   have hincl := OpResultPtr.range_included_op_range (ctx := ($ctx)) ($ptr).spec (by grind)
   grind [layout_grind]))

set_option hygiene false in
macro "prove_setLinkBoundsBlockOperand" ctx:ident ptr:ident : tactic => `(tactic|
  (have ⟨_, _⟩ := ($ctx).sim.in_bounds (.operation ($ptr).spec.op) (by grind)
   have : ctx.buf.mem.size < 2^63 := by grind
   have hincl := BlockOperandPtr.range_included_op_range (ctx := ($ctx).spec) (by grind) ($ptr).spec (by grind)
   grind [layout_grind]))

set_option hygiene false in
macro "prove_setLinkBoundsBlockArgument" ctx:ident ptr:ident : tactic => `(tactic|
  (have ⟨_, _⟩ := ($ctx).sim.in_bounds (.block ($ptr).spec.block) (by grind)
   have hincl := BlockArgumentPtr.range_included_block_range (ctx := ($ctx).spec) (by grind) ($ptr).spec (by grind)
   have : ctx.buf.mem.size < 2^63 := by grind
   grind [layout_grind]))

/- Bounds proof for the `Buffed.*MPtr.write*` calls inside the `allocEmptyImpl` functions. -/
set_option hygiene false in
macro "prove_allocBounds" ctx₀:ident : tactic => `(tactic|
  (have hb := ($ctx₀).mem.fits_in_memory
   have hu := ($ctx₀).usize_toNat
   -- Collapse `.size` to `.mem.size` and use the `write*_size` lemmas to peel the chain of writes down to the just-allocated buffer, exposing the `hsize`/`hbsize` size facts.
   simp only [Buffed.IRBufContext.size_def] at *
   grind (instances := 4000) [UInt64.uint64_add_int64_toInt_lt, Buffed.BlockMPtr.writeNumArguments_size,
     Buffed.BlockMPtr.writeFirstUse_size, Buffed.BlockMPtr.writePrev_size, Buffed.BlockMPtr.writeNext_size,
     Buffed.BlockMPtr.writeParent_size, Buffed.BlockMPtr.writeFirstOp_size, Buffed.BlockMPtr.writeLastOp_size,
     Buffed.RegionMPtr.writeParent_size, Buffed.RegionMPtr.writeFirstBlock_size, Buffed.RegionMPtr.writeLastBlock_size,
     Buffed.OperationMPtr.writeNumResults_size, Buffed.OperationMPtr.writeNumOperands_size,
     Buffed.OperationMPtr.writeNumBlockOperands_size, Buffed.OperationMPtr.writeNumRegions_size,
     Buffed.OperationMPtr.writeParent_size, Buffed.OperationMPtr.writeNext_size, Buffed.OperationMPtr.writePrev_size]))

/- Variant of `prove_allocBounds` for `OperationPtr.allocEmptyImpl`. -/
set_option hygiene false in
macro "prove_allocBoundsOp" ctx₀:ident : tactic => `(tactic|
  (have hb := ($ctx₀).mem.fits_in_memory
   -- The caller established `hptr` (closed form of the operation pointer's address) and `hptrlt` (its `< 2^63` bound); grind unfolds the `let`-bound pointer uniformly in both the goal and these facts, so the pointer-arithmetic decomposition applies and the goal reduces to linear arithmetic over the just-allocated size (`hsize`/`hopsize`/`hprefix`).
   simp only [Buffed.IRBufContext.size_def] at *
   grind (instances := 4000) [UInt64.uint64_add_int64_toInt_lt,
     Buffed.OperationMPtr.writeNumResults_size, Buffed.OperationMPtr.writeNumOperands_size,
     Buffed.OperationMPtr.writeNumBlockOperands_size, Buffed.OperationMPtr.writeNumRegions_size,
     Buffed.OperationMPtr.writeParent_size, Buffed.OperationMPtr.writeNext_size,
     Buffed.OperationMPtr.writePrev_size, Buffed.OperationMPtr.writeOpType_size]))

/- Bounds proof for the field `write*` calls inside the raw `Rewriter.set{Result,Operand, BlockOperand}` setters. -/
set_option hygiene false in
macro "prove_setSlotBounds" ctx₀:ident : tactic => `(tactic|
  (have hb := ($ctx₀).mem.fits_in_memory
   simp only [Buffed.IRBufContext.size_def] at *
   grind [UInt64.uint64_add_int64_toInt_lt,
     Buffed.OpResultMPtr.writeType_size, Buffed.OpResultMPtr.writeFirstUse_size,
     Buffed.OpResultMPtr.writeIndex_size, Buffed.OpResultMPtr.writeOwner_size,
     Buffed.OpOperandMPtr.writeNextUse_size, Buffed.OpOperandMPtr.writeBack_size,
     Buffed.OpOperandMPtr.writeOwner_size, Buffed.OpOperandMPtr.writeValue_size,
     Buffed.BlockOperandMPtr.writeNextUse_size, Buffed.BlockOperandMPtr.writeBack_size,
     Buffed.BlockOperandMPtr.writeOwner_size, Buffed.BlockOperandMPtr.writeValue_size,
     Buffed.BlockArgumentMPtr.writeType_size, Buffed.BlockArgumentMPtr.writeFirstUse_size,
     Buffed.BlockArgumentMPtr.writeIndex_size, Buffed.BlockArgumentMPtr.writeOwner_size]))


/-! ## Debugging printers -/

@[inline]
def dumpOp (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨op.impl.debugPrint (OpInfo := OpInfo) pref ctx.buf, ctx.spec', by rw [Buffed.OperationMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOp_eq (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOp op ctx pref = ctx := by
  simp only [dumpOp]; congr 1

@[inline]
def dumpRegion (region : Sim.RegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨region.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.RegionMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpRegion_eq (region : Sim.RegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpRegion region ctx pref = ctx := by
  simp only [dumpRegion]; congr 1

@[inline]
def dumpBlock (block : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨block.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.BlockMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpBlock_eq (block : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpBlock block ctx pref = ctx := by
  simp only [dumpBlock]; congr 1

@[inline]
def dumpValue (value : Sim.ValuePtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨value.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.ValueImplMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpValue_eq (value : Sim.ValuePtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpValue value ctx pref = ctx := by
  simp only [dumpValue]; congr 1

@[inline]
def dumpOpResult (result : Sim.OpResultPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨result.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.OpResultMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOpResult_eq (result : Sim.OpResultPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOpResult result ctx pref = ctx := by
  simp only [dumpOpResult]; congr 1

@[inline]
def dumpBlockArgument (arg : Sim.BlockArgumentPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨arg.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.BlockArgumentMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpBlockArgument_eq (arg : Sim.BlockArgumentPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpBlockArgument arg ctx pref = ctx := by
  simp only [dumpBlockArgument]; congr 1

@[inline]
def dumpOpOperand (operand : Sim.OpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.OpOperandMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOpOperand_eq (operand : Sim.OpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOpOperand operand ctx pref = ctx := by
  simp only [dumpOpOperand]; congr 1

@[inline]
def dumpBlockOperand (operand : Sim.BlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.BlockOperandMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpBlockOperand_eq (operand : Sim.BlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpBlockOperand operand ctx pref = ctx := by
  simp only [dumpBlockOperand]; congr 1

/-! ### Nullable (`Option*Ptr`) dumpers — print `null` for the sentinel. -/

@[inline]
def dumpOptionOp (op : Sim.OptionOperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨op.impl.debugPrint (OpInfo := OpInfo) pref ctx.buf, ctx.spec', by rw [Buffed.OperationOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionOp_eq (op : Sim.OptionOperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionOp op ctx pref = ctx := by
  simp only [dumpOptionOp]; congr 1

@[inline]
def dumpOptionBlock (block : Sim.OptionBlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨block.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.BlockOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionBlock_eq (block : Sim.OptionBlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionBlock block ctx pref = ctx := by
  simp only [dumpOptionBlock]; congr 1

@[inline]
def dumpOptionRegion (region : Sim.OptionRegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨region.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.RegionOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionRegion_eq (region : Sim.OptionRegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionRegion region ctx pref = ctx := by
  simp only [dumpOptionRegion]; congr 1

@[inline]
def dumpOptionOpOperand (operand : Sim.OptionOpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.OpOperandOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionOpOperand_eq (operand : Sim.OptionOpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionOpOperand operand ctx pref = ctx := by
  simp only [dumpOptionOpOperand]; congr 1

@[inline]
def dumpOptionBlockOperand (operand : Sim.OptionBlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec', by rw [Buffed.BlockOperandOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionBlockOperand_eq (operand : Sim.OptionBlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionBlockOperand operand ctx pref = ctx := by
  simp only [dumpOptionBlockOperand]; congr 1


/-! ## Setters and getters -/

/-- Return a dead byte range to the arena. The two disjointness premises rule out
both dangling live allocations and double-freeing an already free range. -/
@[inline]
def Sim.IRContext.releaseRange (ctx : Sim.IRContext OpInfo) (address size : UInt64)
    (hs : 0 < size.toNat) (hb : address.toNat + size.toNat ≤ ctx.buf.mem.size)
    (hfree : ∀ s a, a ∈ ctx.buf.freeList.bucket s →
      address.toNat + size.toNat ≤ a.toNat ∨ a.toNat + s.toNat ≤ address.toNat)
    (hdead : ∀ p : TopLevelPtr, p.InBounds ctx.spec →
      (p.range ctx.spec).upper ≤ address.toNat ∨
        (address.toNat : Int) + size.toNat ≤ (p.range ctx.spec).lower) :
    Sim.IRContext OpInfo :=
  ⟨ctx.buf.release address size, ctx.spec', by
    constructor
    · exact ctx.sim.fieldsInBounds
    · exact ctx.sim.repr
    · exact ctx.sim.in_bounds
    · exact ctx.sim.disjoint_allocs
    · intro op ib
      have hm := ctx.sim.encoding_op op ib
      constructor
      · exact ⟨hm.prev, hm.next, hm.parent, hm.opType, hm.attrs,
          HasBuffedProperties.readPropertyAt_frame hm.props (Nat.le_refl _)
            (fun _ _ _ _ _ => rfl) (fun _ _ h => h)⟩
      · refine ⟨hm.numBlockOperands, ?_⟩
        intro p hp heq
        have h := hm.blockOperands p hp heq
        exact ⟨by simpa only [Buffed.IRBufContext.release, Buffed.BlockOperandMPtr.readNextUse!, Buffed.BlockOperandMPtr.readBack!, Buffed.BlockOperandMPtr.readValue!, Buffed.OpOperandMPtr.readNextUse!, Buffed.OpOperandMPtr.readBack!, Buffed.OpOperandMPtr.readValue!, Buffed.OpResultMPtr.readFirstUse!, Buffed.BlockArgumentMPtr.readFirstUse!, Buffed.BlockMPtr.readFirstUse!, Sim.OptionBlockOperandPtr.Sim_def, Sim.OptionOpOperandPtr.Sim_def] using h.nextUse,
          by simpa only [Buffed.IRBufContext.release, Buffed.BlockOperandMPtr.readNextUse!, Buffed.BlockOperandMPtr.readBack!, Buffed.BlockOperandMPtr.readValue!, Buffed.OpOperandMPtr.readNextUse!, Buffed.OpOperandMPtr.readBack!, Buffed.OpOperandMPtr.readValue!, Buffed.OpResultMPtr.readFirstUse!, Buffed.BlockArgumentMPtr.readFirstUse!, Buffed.BlockMPtr.readFirstUse!, Sim.BlockOperandPtrPtr.Sim_def, Sim.OpOperandPtrPtr.Sim_def] using h.back,
          h.owner, by simpa only [Buffed.IRBufContext.release, Buffed.BlockOperandMPtr.readNextUse!, Buffed.BlockOperandMPtr.readBack!, Buffed.BlockOperandMPtr.readValue!, Buffed.OpOperandMPtr.readNextUse!, Buffed.OpOperandMPtr.readBack!, Buffed.OpOperandMPtr.readValue!, Buffed.OpResultMPtr.readFirstUse!, Buffed.BlockArgumentMPtr.readFirstUse!, Buffed.BlockMPtr.readFirstUse!, Sim.ValuePtr.Sim_def] using h.value⟩
      · exact ⟨hm.numRegions, hm.regions⟩
      · refine ⟨hm.numOperands, ?_⟩
        intro p hp heq
        have h := hm.operands p hp heq
        exact ⟨by simpa only [Buffed.IRBufContext.release, Buffed.BlockOperandMPtr.readNextUse!, Buffed.BlockOperandMPtr.readBack!, Buffed.BlockOperandMPtr.readValue!, Buffed.OpOperandMPtr.readNextUse!, Buffed.OpOperandMPtr.readBack!, Buffed.OpOperandMPtr.readValue!, Buffed.OpResultMPtr.readFirstUse!, Buffed.BlockArgumentMPtr.readFirstUse!, Buffed.BlockMPtr.readFirstUse!, Sim.OptionBlockOperandPtr.Sim_def, Sim.OptionOpOperandPtr.Sim_def] using h.nextUse,
          by simpa only [Buffed.IRBufContext.release, Buffed.BlockOperandMPtr.readNextUse!, Buffed.BlockOperandMPtr.readBack!, Buffed.BlockOperandMPtr.readValue!, Buffed.OpOperandMPtr.readNextUse!, Buffed.OpOperandMPtr.readBack!, Buffed.OpOperandMPtr.readValue!, Buffed.OpResultMPtr.readFirstUse!, Buffed.BlockArgumentMPtr.readFirstUse!, Buffed.BlockMPtr.readFirstUse!, Sim.BlockOperandPtrPtr.Sim_def, Sim.OpOperandPtrPtr.Sim_def] using h.back,
          h.owner, by simpa only [Buffed.IRBufContext.release, Buffed.BlockOperandMPtr.readNextUse!, Buffed.BlockOperandMPtr.readBack!, Buffed.BlockOperandMPtr.readValue!, Buffed.OpOperandMPtr.readNextUse!, Buffed.OpOperandMPtr.readBack!, Buffed.OpOperandMPtr.readValue!, Buffed.OpResultMPtr.readFirstUse!, Buffed.BlockArgumentMPtr.readFirstUse!, Buffed.BlockMPtr.readFirstUse!, Sim.ValuePtr.Sim_def] using h.value⟩
      · refine ⟨hm.numResults, ?_⟩
        intro p hp heq
        have h := hm.results p hp heq
        exact ⟨h.kind, h.typee, by simpa only [Buffed.IRBufContext.release, Buffed.BlockOperandMPtr.readNextUse!, Buffed.BlockOperandMPtr.readBack!, Buffed.BlockOperandMPtr.readValue!, Buffed.OpOperandMPtr.readNextUse!, Buffed.OpOperandMPtr.readBack!, Buffed.OpOperandMPtr.readValue!, Buffed.OpResultMPtr.readFirstUse!, Buffed.BlockArgumentMPtr.readFirstUse!, Buffed.BlockMPtr.readFirstUse!, Sim.OptionOpOperandPtr.Sim_def] using h.firstUse, h.index, h.owner⟩
    · intro p hp
      have hm := ctx.sim.encoding_block p hp
      constructor
      · exact ⟨by simpa only [Buffed.IRBufContext.release, Buffed.BlockOperandMPtr.readNextUse!, Buffed.BlockOperandMPtr.readBack!, Buffed.BlockOperandMPtr.readValue!, Buffed.OpOperandMPtr.readNextUse!, Buffed.OpOperandMPtr.readBack!, Buffed.OpOperandMPtr.readValue!, Buffed.OpResultMPtr.readFirstUse!, Buffed.BlockArgumentMPtr.readFirstUse!, Buffed.BlockMPtr.readFirstUse!, Sim.OptionBlockOperandPtr.Sim_def] using hm.firstUse, hm.prev, hm.next, hm.parent, hm.firstOp, hm.lastOp⟩
      · refine ⟨hm.numArguments, ?_⟩
        intro p hp heq
        have h := hm.arguments p hp heq
        exact ⟨h.kind, h.type, by simpa only [Buffed.IRBufContext.release, Buffed.BlockOperandMPtr.readNextUse!, Buffed.BlockOperandMPtr.readBack!, Buffed.BlockOperandMPtr.readValue!, Buffed.OpOperandMPtr.readNextUse!, Buffed.OpOperandMPtr.readBack!, Buffed.OpOperandMPtr.readValue!, Buffed.OpResultMPtr.readFirstUse!, Buffed.BlockArgumentMPtr.readFirstUse!, Buffed.BlockMPtr.readFirstUse!, Sim.OptionOpOperandPtr.Sim_def] using h.firstUse, h.index, h.owner⟩
    · intro p hp
      have hm := ctx.sim.encoding_region p hp
      exact ⟨hm.firstBlock, hm.lastBlock, hm.parent⟩
    · exact ctx.sim.attr_empty
    · exact ctx.sim.free_valid.release hs hb hfree
    · intro s a hm p hp
      change a ∈ (ctx.buf.freeList.release address size).bucket s at hm
      rw [Buffed.FreeList.bucket_release] at hm
      split at hm
      · rename_i heq
        subst s
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hdead p hp
        · exact ctx.sim.free_disjoint size a hm p hp
      · exact ctx.sim.free_disjoint s a hm p hp⟩

@[inline]
def Buffed.OperationMPtr.allocationStart (ctx : Buffed.IRBufContext) (ptr : Buffed.OperationMPtr) : UInt64 :=
  ptr + ptr.computeResultsOffset! ctx

@[inline]
def Buffed.OperationMPtr.allocationEnd (ctx : Buffed.IRBufContext) (ptr : Buffed.OperationMPtr) : UInt64 :=
  (ptr + ptr.computeRegionsOffset! (OpInfo := OpInfo) ctx) +
    Buffed.ptrSize * ptr.readNumRegions! ctx

theorem Sim.OperationPtr.allocationStart_eq (ctx : Sim.IRContext OpInfo)
    (ptr : Sim.OperationPtr) (ib : ptr.InBounds ctx) :
    (Buffed.OperationMPtr.allocationStart ctx.buf ptr.impl).toNat =
      (ptr.spec.range ctx.spec).lower := by
  have hl := Sim.OperationPtr.range_linear (ctx := ctx) ptr.spec ib.ib
  have hp := Veir.OperationPtr.toM_toNat ctx.sim.repr ptr.spec ib.ib
  have heq := ib.sim.out
  have hoff := Veir.OperationPtr.computeResultsOffset!_ideal ctx ptr ib.ib ib.sim
    (by prove_setLinkBoundsOp ctx ptr)
  have hb := ctx.buf.mem.fits_in_memory
  rw [Veir.OperationPtr.range_ideal ctx.sim.repr ib.ib]
  simp only [Buffed.OperationMPtr.allocationStart, Veir.OperationPtr.rangeInt,
    Buffed.Operation.rangeInt, add_nat_range_def, Veir.OperationPtr.toFlat]
  rw [UInt64.uint64_add_int64_toNat_lt] <;> grind

theorem Sim.OperationPtr.allocationEnd_eq (ctx : Sim.IRContext OpInfo)
    (ptr : Sim.OperationPtr) (ib : ptr.InBounds ctx) :
    (Buffed.OperationMPtr.allocationEnd (OpInfo := OpInfo) ctx.buf ptr.impl).toNat =
      (ptr.spec.range ctx.spec).upper := by
  have hl := Sim.OperationPtr.range_linear (ctx := ctx) ptr.spec ib.ib
  have hp := Veir.OperationPtr.toM_toNat ctx.sim.repr ptr.spec ib.ib
  have heq := ib.sim.out
  have hoff := Veir.OperationPtr.computeRegionsOffset!_ideal ctx ptr ib.ib ib.sim
    (by prove_setLinkBoundsOp ctx ptr)
  have hc := (ctx.sim.encoding_op ptr.spec ib.ib).numRegions
  have hcap := (ctx.sim.repr.operations_indices ptr.spec ib.ib).capRegions
  have hb := ctx.buf.mem.fits_in_memory
  rw [Veir.OperationPtr.range_ideal ctx.sim.repr ib.ib]
  simp only [Buffed.OperationMPtr.allocationEnd, Veir.OperationPtr.rangeInt,
    Buffed.Operation.rangeInt, add_nat_range_def, Veir.OperationPtr.toFlat]
  have hadd : (ptr.impl + ptr.impl.computeRegionsOffset! (OpInfo := OpInfo) ctx.buf).toNat =
      (ptr.spec.id : Int) + Buffed.Operation.Offsets.regionsInt ptr.spec ctx.spec := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  rw [UInt64.toNat_add, UInt64.toNat_mul]
  simp only [Buffed.ptrSize, UInt64.toNat_ofNat] at *
  grind

private theorem IRContext.isRepr_OperationPtr_dealloc
    {ctx : IRContext OpInfo} (hctx : ctx.IsRepr)
    (op : OperationPtr) (hop : op.InBounds ctx) :
    (op.dealloc ctx hop).IsRepr := by
  grind [IRContext.IsRepr]

private theorem IRContext.layoutPreserved_OperationPtr_dealloc
    {ctx : IRContext OpInfo} (op : OperationPtr) (hop : op.InBounds ctx) :
    (op.dealloc ctx hop).LayoutPreserved ctx := by
  constructor <;> grind [OperationPtr.LayoutPreserved, BlockPtr.LayoutPreserved]

private theorem TopLevelPtr.range_OperationPtr_dealloc
    {ctx : IRContext OpInfo} (op : OperationPtr) (hop : op.InBounds ctx)
    (p : TopLevelPtr) (hp : p.InBounds (op.dealloc ctx hop)) :
    p.range (op.dealloc ctx hop) = p.range ctx := by
  have hlay := IRContext.layoutPreserved_OperationPtr_dealloc op hop
  cases p with
  | operation op =>
    exact LayoutPreserved.same_operationPtr_range op (by simpa using hp) hlay
  | block block =>
    exact LayoutPreserved.same_blockPtr_range block (by simpa using hp) hlay
  | region => rfl

private theorem OpOperandPtr.matches_OperationPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.OperationPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec ib.ib).FieldsInBounds)
    (oper : OpOperandPtr) (hib : oper.InBounds (ptr.spec.dealloc ctx.spec ib.ib)) :
    oper.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec ib.ib) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec ib.ib
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_OperationPtr_dealloc ptr.spec ib.ib
  have hib' : oper.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_op oper.op (by grind) |>.operands oper hib' rfl
  have hfib := OpOperandPtr.get_fieldsInBounds spec' oper fib hib
  have htoM := OpOperandPtr.layoutPreserved_same_toM hlay hib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds)
  have htoM_b := OpOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds
  have htoM_v := ValuePtr.layoutPreserved_same_toM hlay hfib.value_inBounds
  have hget : oper.get! spec' = oper.get! ctx.spec := by grind
  constructor
  · have := hm.nextUse
    rw [Sim.OptionOpOperandPtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readNextUse!]
  · have := hm.back
    rw [Sim.OpOperandPtrPtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readBack!]
  · have := hm.owner
    rw [Sim.OperationPtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readOwner!]
  · have := hm.value
    rw [Sim.ValuePtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readValue!]

private theorem BlockOperandPtr.matches_OperationPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.OperationPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec ib.ib).FieldsInBounds)
    (oper : BlockOperandPtr) (hib : oper.InBounds (ptr.spec.dealloc ctx.spec ib.ib)) :
    oper.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec ib.ib) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec ib.ib
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_OperationPtr_dealloc ptr.spec ib.ib
  have hib' : oper.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_op oper.op (by grind) |>.blockOperands oper hib' rfl
  have hfib := BlockOperandPtr.get_fieldsInBounds spec' oper fib hib
  have htoM := BlockOperandPtr.layoutPreserved_same_toM hlay hib
  have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds)
  have htoM_b := BlockOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds
  have hget : oper.get! spec' = oper.get! ctx.spec := by grind
  constructor
  · have := hm.nextUse
    rw [Sim.OptionBlockOperandPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readNextUse!]
  · have := hm.back
    rw [Sim.BlockOperandPtrPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readBack!]
  · have := hm.owner
    rw [Sim.OperationPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readOwner!]
  · have := hm.value
    rw [Sim.BlockPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readValue!]

private theorem OpResultPtr.matches_OperationPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.OperationPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec ib.ib).FieldsInBounds)
    (res : OpResultPtr) (hib : res.InBounds (ptr.spec.dealloc ctx.spec ib.ib)) :
    res.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec ib.ib) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec ib.ib
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_OperationPtr_dealloc ptr.spec ib.ib
  have hib' : res.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_op res.op (by grind) |>.results res hib' rfl
  have hfib := OpResultPtr.get_fieldsInBounds spec' res fib hib
  have htoM := OpResultPtr.layoutPreserved_same_toM hlay hib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
  have hget : res.get! spec' = res.get! ctx.spec := by grind
  constructor
  · have := hm.kind
    grind [Buffed.OpResultMPtr.readKind!]
  · have := hm.typee
    grind [Buffed.OpResultMPtr.readType!]
  · have := hm.firstUse
    rw [Sim.OptionOpOperandPtr.Sim_def] at this ⊢
    grind [Buffed.OpResultMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.OpResultMPtr.readIndex!]
  · have := hm.owner
    rw [Sim.OperationPtr.Sim_def] at this ⊢
    grind [Buffed.OpResultMPtr.readOwner!]

private theorem BlockArgumentPtr.matches_OperationPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.OperationPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec ib.ib).FieldsInBounds)
    (arg : BlockArgumentPtr) (hib : arg.InBounds (ptr.spec.dealloc ctx.spec ib.ib)) :
    arg.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec ib.ib) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec ib.ib
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_OperationPtr_dealloc ptr.spec ib.ib
  have hib' : arg.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_block arg.block (by grind) |>.arguments arg hib' rfl
  have hfib := BlockArgumentPtr.get_fieldsInBounds spec' arg fib hib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
  have hget : arg.get! spec' = arg.get! ctx.spec := by grind
  constructor
  · have := hm.kind
    grind [Buffed.BlockArgumentMPtr.readKind!]
  · have := hm.type
    grind [Buffed.BlockArgumentMPtr.readType!]
  · have := hm.firstUse
    rw [Sim.OptionOpOperandPtr.Sim_def] at this ⊢
    grind [Buffed.BlockArgumentMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.BlockArgumentMPtr.readIndex!]
  · have := hm.owner
    rw [Sim.BlockPtr.Sim_def] at this ⊢
    grind [Buffed.BlockArgumentMPtr.readOwner!]

@[inline]
def Sim.OperationPtr.forget (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec ib.ib).FieldsInBounds := by grind) : Sim.IRContext OpInfo :=
  ⟨ctx.buf,
   .mk (ptr.spec.dealloc ctx.spec),
   by
     constructor <;> simp only [Sim.RawIRContext.spec, Erased.out_mk]
     case fieldsInBounds => exact fib
     case repr => exact IRContext.isRepr_OperationPtr_dealloc ctx.sim.repr ptr.spec ib.ib
     case in_bounds =>
       intro p hp
       try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
       rw [TopLevelPtr.range_OperationPtr_dealloc ptr.spec ib.ib p hp]
       exact ctx.sim.in_bounds p (by grind)
     case disjoint_allocs =>
       intro p₁ p₂ hp₁ hp₂ hne
       try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
       rw [TopLevelPtr.range_OperationPtr_dealloc ptr.spec ib.ib p₁ hp₁,
         TopLevelPtr.range_OperationPtr_dealloc ptr.spec ib.ib p₂ hp₂]
       exact ctx.sim.disjoint_allocs p₁ p₂ (by grind) (by grind) hne
     case encoding_op =>
       intro op hop
       try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
       have hop' : op.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_op op hop'
       have hget : op.get! (ptr.spec.dealloc ctx.spec ib.ib) = op.get! ctx.spec := by grind
       have htype : op.getOpType! (ptr.spec.dealloc ctx.spec ib.ib) = op.getOpType! ctx.spec := by grind
       have hprops : op.getProperties! (ptr.spec.dealloc ctx.spec ib.ib)
           (op.getOpType! ctx.spec) = op.getProperties! ctx.spec (op.getOpType! ctx.spec) := by grind
       constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
         · exact hget ▸ henc.prev
         · exact hget ▸ henc.next
         · exact hget ▸ henc.parent
         · exact htype.trans henc.opType
         · change ctx.buf.attributes[(Buffed.OperationMPtr.readAttrs! ctx.buf op.toM).toNat]? =
             some (op.get! (ptr.spec.dealloc ctx.spec ib.ib)).attrs
           rw [hget]
           exact henc.attrs
         · rw [Erased.out_mk, htype, hprops]
           exact henc.props
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
         · rw [hget]
           exact henc.numBlockOperands
         · intro bo hbo _
           exact BlockOperandPtr.matches_OperationPtr_dealloc ptr ib fib bo hbo
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
         · rw [hget]
           exact henc.numRegions
         · intro idx hidx
           have hnum : op.getNumRegions! (ptr.spec.dealloc ctx.spec ib.ib) =
               op.getNumRegions! ctx.spec := by grind
           have hreg : op.getRegion! (ptr.spec.dealloc ctx.spec ib.ib) idx =
               op.getRegion! ctx.spec idx := by grind
           rw [hreg]
           exact henc.regions idx (by grind)
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
         · rw [hget]
           exact henc.numOperands
         · intro oper hoper _
           exact OpOperandPtr.matches_OperationPtr_dealloc ptr ib fib oper hoper
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
         · rw [hget]
           exact henc.numResults
         · intro res hres _
           exact OpResultPtr.matches_OperationPtr_dealloc ptr ib fib res hres
     case encoding_block =>
       intro block hblock
       try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
       have hblock' : block.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_block block hblock'
       have hget : block.get! (ptr.spec.dealloc ctx.spec ib.ib) = block.get! ctx.spec := by grind
       constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
       · have hfib := BlockPtr.get_fieldsInBounds _ block fib hblock
         have hlay := IRContext.layoutPreserved_OperationPtr_dealloc ptr.spec ib.ib
         have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay
           ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
         constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
         · have := henc.firstUse
           rw [Sim.OptionBlockOperandPtr.Sim_def] at this ⊢
           grind
         · exact hget ▸ henc.prev
         · exact hget ▸ henc.next
         · exact hget ▸ henc.parent
         · exact hget ▸ henc.firstOp
         · exact hget ▸ henc.lastOp
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
         · rw [hget]
           exact henc.numArguments
         · intro arg harg _
           exact BlockArgumentPtr.matches_OperationPtr_dealloc ptr ib fib arg harg
     case encoding_region =>
       intro region hregion
       try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
       have hregion' : region.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_region region hregion'
       have hget : region.get! (ptr.spec.dealloc ctx.spec ib.ib) = region.get! ctx.spec := by grind
       constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
       · exact hget ▸ henc.firstBlock
       · exact hget ▸ henc.lastBlock
       · exact hget ▸ henc.parent
     case attr_empty => exact ctx.sim.attr_empty
     case free_valid => exact ctx.sim.free_valid
     case free_disjoint =>
       intro size address hm p hp
       try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
       rw [TopLevelPtr.range_OperationPtr_dealloc ptr.spec ib.ib p hp]
       exact ctx.sim.free_disjoint size address hm p (by grind)⟩

/-- Remove the operation from the spec and return its entire byte allocation to
the exact-size pool. Existing pointers are unchanged. -/
@[inline]
def Sim.OperationPtr.dealloc (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec ib.ib).FieldsInBounds := by grind) : Sim.IRContext OpInfo :=
  let address := Buffed.OperationMPtr.allocationStart ctx.buf ptr.impl
  let after := Buffed.OperationMPtr.allocationEnd (OpInfo := OpInfo) ctx.buf ptr.impl
  let size := after - address
  have hstart : (address.toNat : Int) = (ptr.spec.range ctx.spec).lower :=
    Sim.OperationPtr.allocationStart_eq ctx ptr ib
  have hend : (after.toNat : Int) = (ptr.spec.range ctx.spec).upper :=
    Sim.OperationPtr.allocationEnd_eq ctx ptr ib
  have hin := ctx.sim.in_bounds (.operation ptr.spec) (by grind)
  have hpos : address.toNat < after.toNat := by
    have hr : (ptr.spec.range ctx.spec).lower < (ptr.spec.range ctx.spec).upper := by
      rw [Veir.OperationPtr.range_ideal ctx.sim.repr ib.ib]
      simp only [Veir.OperationPtr.rangeInt, Buffed.Operation.rangeInt,
        add_nat_range_def, Veir.OperationPtr.toFlat]
      grind
    omega
  have hsize : size.toNat = after.toNat - address.toNat := by
    apply UInt64.toNat_sub_of_le
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  let ctx' := Sim.OperationPtr.forget ctx ptr ib fib
  have hspec : ctx'.spec = ptr.spec.dealloc ctx.spec ib.ib := by
    simp only [ctx', forget, Sim.IRContext.spec, Erased.out_mk]
  ctx'.releaseRange address size (by omega) (by
    simp only [IsIncludedIN, ExArray.range_upper, TopLevelPtr.range, Sim.RawIRContext.spec] at hin
    change address.toNat + size.toNat ≤ ctx.buf.mem.size
    simp only [Sim.IRContext.spec] at hstart hend
    omega)
    (by
      intro s a hm
      have hd := ctx.sim.free_disjoint s a hm (.operation ptr.spec) (by grind)
      simp only [TopLevelPtr.range, Sim.RawIRContext.spec] at hd
      simp only [Sim.IRContext.spec] at hstart hend
      omega)
    (by
      intro p hp
      rw [hspec] at hp ⊢
      have hold : p.InBounds ctx.spec := by
        change p.InBounds (ptr.spec.dealloc ctx.spec ib.ib) at hp
        grind
      have hne : p ≠ .operation ptr.spec := by
        intro heq
        subst p
        change ptr.spec.InBounds (ptr.spec.dealloc ctx.spec ib.ib) at hp
        simp [Veir.OperationPtr.inBounds_def, Veir.OperationPtr.dealloc] at hp
      have hd := ctx.sim.disjoint_allocs p (.operation ptr.spec) hold ib.ib hne
      change (p.range (ptr.spec.dealloc ctx.spec ib.ib)).upper ≤ address.toNat ∨
        (address.toNat : Int) + size.toNat ≤ (p.range (ptr.spec.dealloc ctx.spec ib.ib)).lower
      rw [TopLevelPtr.range_OperationPtr_dealloc ptr.spec ib.ib p hp]
      change (p.range ctx.spec).upper ≤ (ptr.spec.range ctx.spec).lower ∨
        (ptr.spec.range ctx.spec).upper ≤ (p.range ctx.spec).lower at hd
      omega)

@[inline]
def Sim.OperationPtr.setNextOp (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNext ctx.buf next.impl (by prove_setLinkBoundsOp ctx ptr),
    (Erased.mk (ptr.spec, ctx.spec, next.spec)).map (fun (ptr, ctx, value) => ptr.setNextOp! ctx value), by
    prove_setLinkSim ctx op Buffed.OperationMPtr.writeNext operationMPtr_writeNext OperationPtr_setNextOp
      (ptr.spec.setNextOp ctx.spec next.spec (by grind)) nextIb⟩

open Classical in
noncomputable def Sim.OperationPtr.setNextOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Operation.Offsets.next).toInt + Buffed.Operation.Sizes.next.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OperationMPtr.writeNext ctx.buf ptr.impl next.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, next.spec)).map (fun (ptr, ctx, value) => ptr.setNextOp! ctx value) } then
    ⟨ptr.impl.writeNext ctx.buf next.impl h₁, (Erased.mk (ptr.spec, ctx.spec, next.spec)).map (fun (ptr, ctx, value) => ptr.setNextOp! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.setNextOp_eq_setNextOp! (ctx : IRContext OpInfo) ptr next ib nextIb :
    setNextOp ctx ptr next ib nextIb = setNextOp! ctx ptr next := by
  simp [setNextOp, setNextOp!]
  split
  · grind
  · prove_setLinkBoundsOp ctx ptr

@[inline]
def Sim.OperationPtr.getNextOp (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readNext ctx.buf (by prove_setLinkBoundsOp ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).next)⟩

@[grind .]
theorem Sim.OperationPtr.getNextOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getNextOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).next
  grind [getNextOp]

@[simp, grind =]
theorem Sim.OperationPtr.getNextOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getNextOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).next := by
  grind [getNextOp]

@[inline]
def Sim.OperationPtr.getNextOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readNext! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).next)⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNextOp_eq_getNextOp! (ctx : IRContext OpInfo) ptr ib :
    getNextOp ctx ptr ib = getNextOp! ctx ptr := by
  simp [getNextOp, getNextOp!] <;> grind

@[inline]
def Sim.OperationPtr.getOpType (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : OpInfo :=
  SerializableOpInfo.decode (ptr.impl.readOpType ctx.buf (by prove_setLinkBoundsOp ctx ptr))

@[inline]
def Sim.OperationPtr.getOpType! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : OpInfo :=
  SerializableOpInfo.decode (ptr.impl.readOpType! ctx.buf)

/-- The raw encoded op type. Comparing it against `SerializableOpInfo.encode c` avoids
decoding and the allocating `DecidableEq` call of `getOpType ctx ptr ib = c` on hot paths. -/
@[inline]
def Sim.OperationPtr.getOpTypeEncoded (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : UInt32 :=
  ptr.impl.readOpType ctx.buf (by prove_setLinkBoundsOp ctx ptr)

@[inline]
def Sim.OperationPtr.getOpTypeEncoded! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : UInt32 :=
  ptr.impl.readOpType! ctx.buf

theorem Sim.OperationPtr.getOpType_eq_of_getOpTypeEncoded_eq {ctx : Sim.IRContext OpInfo}
    {ptr : Sim.OperationPtr} {ib : ptr.InBounds ctx} {c : OpInfo}
    (h : getOpTypeEncoded ctx ptr ib = SerializableOpInfo.encode c) :
    getOpType ctx ptr ib = c := by
  simp only [getOpType, getOpTypeEncoded, Buffed.OperationMPtr.readOpType_eq_readOpType!] at h ⊢
  rw [h, SerializableOpInfo.decode_encode]

theorem Sim.OperationPtr.getOpType!_eq_of_getOpTypeEncoded!_eq {ctx : Sim.IRContext OpInfo}
    {ptr : Sim.OperationPtr} {c : OpInfo}
    (h : getOpTypeEncoded! ctx ptr = SerializableOpInfo.encode c) :
    getOpType! ctx ptr = c := by
  simp only [getOpType!, getOpTypeEncoded!] at h ⊢
  rw [h, SerializableOpInfo.decode_encode]

@[inline]
def Sim.OperationPtr.setPrevOp (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writePrev ctx.buf prev.impl (by prove_setLinkBoundsOp ctx ptr), (Erased.mk (ptr.spec, ctx.spec, prev.spec)).map (fun (ptr, ctx, value) => ptr.setPrevOp! ctx value), by
    prove_setLinkSim ctx op Buffed.OperationMPtr.writePrev operationMPtr_writePrev OperationPtr_setPrevOp
      (ptr.spec.setPrevOp ctx.spec prev.spec (by grind)) prevIb⟩

open Classical in
noncomputable def Sim.OperationPtr.setPrevOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Operation.Offsets.prev).toInt + Buffed.Operation.Sizes.prev.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OperationMPtr.writePrev ctx.buf ptr.impl prev.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, prev.spec)).map (fun (ptr, ctx, value) => ptr.setPrevOp! ctx value) } then
    ⟨ptr.impl.writePrev ctx.buf prev.impl h₁, (Erased.mk (ptr.spec, ctx.spec, prev.spec)).map (fun (ptr, ctx, value) => ptr.setPrevOp! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.setPrevOp_eq_setPrevOp! (ctx : IRContext OpInfo) ptr prev ib prevIb :
    setPrevOp ctx ptr prev ib prevIb = setPrevOp! ctx ptr prev := by
  simp [setPrevOp, setPrevOp!]
  split
  · grind
  · prove_setLinkBoundsOp ctx ptr

@[simp, grind =]
theorem Sim.OperationPtr.setNextOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextOp ctx ptr next ib nextIb).spec = ptr.spec.setNextOp ctx.spec next.spec := by
  grind [setNextOp]

@[simp, grind =]
theorem Sim.OperationPtr.setNextOp!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextOp! ctx ptr next).spec = ptr.spec.setNextOp! ctx.spec next.spec := by
  grind

@[inline]
def Sim.OperationPtr.getPrevOp (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readPrev ctx.buf (by prove_setLinkBoundsOp ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).prev)⟩

@[simp, grind =]
theorem Sim.OperationPtr.getPrevOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).prev := by
  grind [getPrevOp]

@[grind .]
theorem Sim.OperationPtr.getPrevOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).prev
  grind [getPrevOp]

@[inline]
def Sim.OperationPtr.getPrevOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readPrev! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).prev)⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getPrevOp_eq_getPrevOp! (ctx : IRContext OpInfo) ptr ib :
    getPrevOp ctx ptr ib = getPrevOp! ctx ptr := by
  simp [getPrevOp, getPrevOp!] <;> grind

@[inline]
def Sim.OperationPtr.setParent (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl (by prove_setLinkBoundsOp ctx ptr), (Erased.mk (ptr.spec, ctx.spec, parent.spec)).map (fun (ptr, ctx, value) => ptr.setParent! ctx value), by
    prove_setLinkSim ctx op Buffed.OperationMPtr.writeParent operationMPtr_writeParent OperationPtr_setParent
      (ptr.spec.setParent ctx.spec parent.spec (by grind)) parentIb⟩

open Classical in
noncomputable def Sim.OperationPtr.setParent! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Operation.Offsets.parent).toInt + Buffed.Operation.Sizes.parent.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OperationMPtr.writeParent ctx.buf ptr.impl parent.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, parent.spec)).map (fun (ptr, ctx, value) => ptr.setParent! ctx value) } then
    ⟨ptr.impl.writeParent ctx.buf parent.impl h₁, (Erased.mk (ptr.spec, ctx.spec, parent.spec)).map (fun (ptr, ctx, value) => ptr.setParent! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.setParent_eq_setParent! (ctx : IRContext OpInfo) ptr parent ib parentIb :
    setParent ctx ptr parent ib parentIb = setParent! ctx ptr parent := by
  simp [setParent, setParent!]
  split
  · grind
  · prove_setLinkBoundsOp ctx ptr

@[simp, grind =]
theorem Sim.OperationPtr.setPrevOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevOp ctx ptr prev ib prevIb).spec = ptr.spec.setPrevOp ctx.spec prev.spec := by
  grind [setPrevOp]

@[simp, grind =]
theorem Sim.OperationPtr.setPrevOp!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevOp! ctx ptr prev).spec = ptr.spec.setPrevOp! ctx.spec prev.spec := by
  grind

@[inline]
def Sim.OperationPtr.getParent (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readParent ctx.buf (by prove_setLinkBoundsOp ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).parent)⟩

@[simp, grind =]
theorem Sim.OperationPtr.getParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).spec = (ptr.spec.get ctx.spec).parent := by
  grind [getParent]

@[grind .]
theorem Sim.OperationPtr.getParent_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).parent
  grind [getParent]

@[inline]
def Sim.OperationPtr.getParent! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readParent! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).parent)⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getParent_eq_getParent! (ctx : IRContext OpInfo) ptr ib :
    getParent ctx ptr ib = getParent! ctx ptr := by
  simp [getParent, getParent!] <;> grind

@[simp, grind =]
theorem Sim.OperationPtr.setParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent ctx ptr parent ib parentIb).spec = ptr.spec.setParent ctx.spec parent.spec := by
  grind [setParent]

@[simp, grind =]
theorem Sim.OperationPtr.setParent!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent! ctx ptr parent).spec = ptr.spec.setParent! ctx.spec parent.spec := by
  grind

set_option maxHeartbeats 1000000000 in
@[inline]
def Sim.OperationPtr.setAttributes (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (attrs : DictionaryAttr) (_ib : ptr.InBounds ctx) : Option (Sim.IRContext OpInfo) := do
  match _ : ctx with
  | ⟨ctxBuf', ctxSpec', ctxSim⟩ =>
    rlet ⟨ctxBuf, idx⟩ ← ctxBuf'.insertAttrs attrs
    some ⟨ptr.impl.writeAttrs ctxBuf idx (by
      have incl : IsIncludedIN ((ptr).spec.range (ctx).spec) (ctx).buf.mem.range := by
        have := ctx.sim.in_bounds (.operation (ptr).spec)
        grind
      have : ctxBuf.mem.size < 2^63 := by grind
      grind [layout_grind, Buffed.IRBufContext.insertAttrs]),
    (Erased.mk (ptr.spec, ctxSpec'.out)).map (fun (ptr, spec) => ptr.setAttributes! spec attrs), by
   let ctxSpec := ctxSpec'.out
   simp only [Erased.map_mk]
   conv => arg 1; arg 2; arg 1; tactic =>
     change _ = ptr.spec.setAttributes ctxSpec attrs (by grind)
     grind
   have := ctx.sim.in_bounds (.operation ptr.spec) (by grind)
   have : ctx.buf.mem.size < 2^63 := by grind
   have hmem : ctxBuf.mem = ctx.buf.mem := by grind [Buffed.IRBufContext.insertAttrs]
   have hfree : ctxBuf.freeList = ctx.buf.freeList := by grind [Buffed.IRBufContext.insertAttrs]
   have hattr_push : ctxBuf.attributes = ctx.buf.attributes.push (Attribute.dictionaryAttr attrs) := by
     grind [Buffed.IRBufContext.insertAttrs]
   have hidx : idx.toNat = ctx.buf.attributes.size := by
     grind [Buffed.IRBufContext.insertAttrs]
   have himpl : ptr.spec.toM = ptr.impl := _ib.sim.out
   have hwib : ptr.spec.InBounds ctxSpec := by grind
   have haddr_w := Veir.OperationPtr.toM_toNat ctx.sim.repr ptr.spec (by grind)
   have hwrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) ptr.spec (by grind)
   have hsize := Veir.Sim.IRContext.mem_size_lt ctx
   have hFIB : ctxSpec.FieldsInBounds := by have := ctx.sim.fieldsInBounds; grind
   have hlay : ctxSpec.LayoutPreserved (ptr.spec.setAttributes ctxSpec attrs (by grind)) :=
     IRContext.LayoutPreserved.of_layoutUnchanged_ltr (OperationPtr.setAttributes_preservesLayout _)
   have hlayF : ctx.spec.LayoutPreserved (ptr.spec.setAttributes ctxSpec attrs (by grind)) :=
     IRContext.LayoutPreserved.of_layoutUnchanged_ltr (by grind)
   have hwaddr : ((ptr.impl + Buffed.Operation.Offsets.attrs).toNat : Int) = ptr.spec.id + 64 := by
     rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [_root_.Veir.OperationPtr.toFlat]
   -- The single attrs-word write over the post-`insertAttrs` buffer: any window disjoint
   -- from that word agrees, the pushed attribute table preserving all old lookups.
   have hb0 : (ptr.impl + Buffed.Operation.Offsets.attrs).toInt + Buffed.Operation.Sizes.attrs.toInt
       ≤ ctxBuf.size := by
     have incl : IsIncludedIN (ptr.spec.range ctx.spec) ctx.buf.mem.range := by
       have := ctx.sim.in_bounds (.operation ptr.spec)
       grind
     have : ctxBuf.mem.size < 2^63 := by grind
     grind [layout_grind, Buffed.IRBufContext.insertAttrs]
   have hagreeD : ∀ (lo hi : Nat),
       (hi ≤ (ptr.impl + Buffed.Operation.Offsets.attrs).toNat
        ∨ (ptr.impl + Buffed.Operation.Offsets.attrs).toNat + 8 ≤ lo) →
       Buffed.AgreesOn (Buffed.OperationMPtr.writeAttrs ctxBuf ptr.impl idx hb0) ctx.buf lo hi := by
     intro lo hi hd
     simp only [Sim.RawIRContext.spec] at *
     refine ⟨?_, fun w a len h1 h2 => ?_, fun i a h => ?_⟩
     · simp only [Buffed.OperationMPtr.writeAttrs]
       simp [hmem]
     · simp only [Buffed.OperationMPtr.writeAttrs]
       rw [ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega), hmem]
     · simp only [Buffed.OperationMPtr.writeAttrs, hattr_push]
       grind [Array.getElem?_push_lt, Array.getElem?_eq_some_iff]
   constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
   · grind
   · grind [layout_grind]
   · try simp only [Sim.RawIRContext.spec, Erased.out_mk]
     intros gptr gptrIb
     simp only [Sim.RawIRContext.spec] at *
     have := ctx.sim.in_bounds gptr (by grind)
     grind [TopLevelPtr]
   · try simp only [Sim.RawIRContext.spec, Erased.out_mk]
     have := ctx.sim.disjoint_allocs
     grind [TopLevelPtr]
   · try simp only [Sim.RawIRContext.spec, Erased.out_mk]
     intros op opIb
     simp only [Sim.RawIRContext.spec] at *
     have hopin : op.InBounds ctxSpec := by grind
     have haddr_r := Veir.OperationPtr.toM_toNat ctx.sim.repr op (by grind)
     have hrrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op (by grind)
     have hdisj := fun hne : op ≠ ptr.spec =>
       Veir.Sim.disjoint_operation_operation (ctx := ctx) op ptr.spec (by grind) (by grind) hne
     have := ctx.sim.in_bounds (.operation op) (by grind)
     have := ctx.sim.disjoint_allocs (.operation op) (.operation ptr.spec) (by grind) (by grind)
     have := ctx.sim.encoding_op op (by grind)
     have hopin' : op.InBounds ctx.spec := by grind
     constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
     · -- MatchesBase: framed for other ops; per-field for the writer (its attrs changed).
       by_cases hcase : op = ptr.spec
       · subst hcase
         constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
         · have := this.prev
           grind (splits := 8) only [Erased.out_mk, footprint_grind, isDisjointI_def, IsIncludedI,
               _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
               OperationPtr.get!_OperationPtr_setAttributes, BlockPtr.get!_OperationPtr_setAttributes,
               RegionPtr.get!_OperationPtr_setAttributes, OperationPtr.getOpType!_OperationPtr_setAttributes,
               OperationPtr.getNumOperands!_OperationPtr_setAttributes, OperationPtr.getNumRegions!_OperationPtr_setAttributes,
               OperationPtr.getNumResults!_OperationPtr_setAttributes, OperationPtr.getNumSuccessors!_OperationPtr_setAttributes,
               BlockPtr.getNumArguments!_OperationPtr_setAttributes,
               OperationPtr.prev!_OperationPtr_setAttributes, OperationPtr.next!_OperationPtr_setAttributes,
               OperationPtr.parent!_OperationPtr_setAttributes,
               _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
               _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
         · have := this.next
           grind (splits := 8) only [Erased.out_mk, footprint_grind, isDisjointI_def, IsIncludedI,
               _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
               OperationPtr.get!_OperationPtr_setAttributes, BlockPtr.get!_OperationPtr_setAttributes,
               RegionPtr.get!_OperationPtr_setAttributes, OperationPtr.getOpType!_OperationPtr_setAttributes,
               OperationPtr.getNumOperands!_OperationPtr_setAttributes, OperationPtr.getNumRegions!_OperationPtr_setAttributes,
               OperationPtr.getNumResults!_OperationPtr_setAttributes, OperationPtr.getNumSuccessors!_OperationPtr_setAttributes,
               BlockPtr.getNumArguments!_OperationPtr_setAttributes,
               OperationPtr.prev!_OperationPtr_setAttributes, OperationPtr.next!_OperationPtr_setAttributes,
               OperationPtr.parent!_OperationPtr_setAttributes,
               _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
               _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
         · have := this.parent
           grind (splits := 8) only [Erased.out_mk, footprint_grind, isDisjointI_def, IsIncludedI,
               _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
               OperationPtr.get!_OperationPtr_setAttributes, BlockPtr.get!_OperationPtr_setAttributes,
               RegionPtr.get!_OperationPtr_setAttributes, OperationPtr.getOpType!_OperationPtr_setAttributes,
               OperationPtr.getNumOperands!_OperationPtr_setAttributes, OperationPtr.getNumRegions!_OperationPtr_setAttributes,
               OperationPtr.getNumResults!_OperationPtr_setAttributes, OperationPtr.getNumSuccessors!_OperationPtr_setAttributes,
               BlockPtr.getNumArguments!_OperationPtr_setAttributes,
               OperationPtr.prev!_OperationPtr_setAttributes, OperationPtr.next!_OperationPtr_setAttributes,
               OperationPtr.parent!_OperationPtr_setAttributes,
               _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
               _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
         · have := this.opType
           grind (splits := 8) only [Erased.out_mk, footprint_grind, isDisjointI_def, IsIncludedI,
               _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
               OperationPtr.get!_OperationPtr_setAttributes, BlockPtr.get!_OperationPtr_setAttributes,
               RegionPtr.get!_OperationPtr_setAttributes, OperationPtr.getOpType!_OperationPtr_setAttributes,
               OperationPtr.getNumOperands!_OperationPtr_setAttributes, OperationPtr.getNumRegions!_OperationPtr_setAttributes,
               OperationPtr.getNumResults!_OperationPtr_setAttributes, OperationPtr.getNumSuccessors!_OperationPtr_setAttributes,
               BlockPtr.getNumArguments!_OperationPtr_setAttributes,
               OperationPtr.prev!_OperationPtr_setAttributes, OperationPtr.next!_OperationPtr_setAttributes,
               OperationPtr.parent!_OperationPtr_setAttributes,
               _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
               _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
         · have := this.attrs
           simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at this ⊢
           grind (splits := 8) only [Erased.out_mk, footprint_grind, isDisjointI_def, IsIncludedI,
               _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
               OperationPtr.get!_OperationPtr_setAttributes, _root_.Veir.OperationPtr.toFlat,
               Array.getElem?_push_lt, Array.getElem?_push_size, Array.getElem?_eq_some_iff,
               Option.bind_some, Option.pure_def, Option.bind_eq_bind]
         · have hprops := OperationPtr.props_frame (spec' := ptr.spec.setAttributes ctxSpec attrs (by grind))
             ctx ptr.spec hopin' this.props (hagreeD _ _ (by omega))
             (by grind)
             (by grind)
           grind

       · refine OperationPtr.matchesBase_frame ctx op hopin' this.toMatchesBase (hagreeD _ _ ?_) hlayF
           (by grind only [Erased.out_mk, OperationPtr.get!_OperationPtr_setAttributes]) (by grind only [Erased.out_mk, OperationPtr.get!_OperationPtr_setAttributes]) (by grind only [Erased.out_mk, OperationPtr.get!_OperationPtr_setAttributes]) (by grind only [Erased.out_mk, OperationPtr.get!_OperationPtr_setAttributes])
           (by grind only [Erased.out_mk, OperationPtr.getOpType!_OperationPtr_setAttributes])
           (by grind only [Erased.out_mk, OperationPtr.getProperties!_OperationPtr_setAttributes]) opIb
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
     · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
       · refine OperationPtr.numBlockOperands_frame ctx op hopin' this.numBlockOperands (hagreeD _ _ ?_)
           (by grind only [Erased.out_mk, OperationPtr.get!_OperationPtr_setAttributes])
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
       · intros bo boIb heq
         simp only [Sim.RawIRContext.spec] at *
         have hboIb : bo.InBounds ctx.spec := by grind
         have hbincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboIb
         have hpib := Veir.Sim.BlockOperandPtr.op_inBounds hboIb
         have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) bo.op hpib
         refine BlockOperandPtr.matches_frame ctx bo hboIb (this.blockOperands bo hboIb heq)
           (hagreeD _ _ ?_) hlayF (by grind only [Erased.out_mk, BlockOperandPtr.get!_OperationPtr_setAttributes]) boIb
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
     · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
       · refine OperationPtr.numRegions_frame ctx op hopin' this.numRegions (hagreeD _ _ ?_)
           (by grind only [Erased.out_mk, OperationPtr.get!_OperationPtr_setAttributes])
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
       · intros ridx idxIn
         simp only [Sim.RawIRContext.spec] at *
         have hnr : ridx < op.getNumRegions! ctx.spec := by grind
         have hcapr := ctx.sim.repr.operations_indices op hopin' |>.capRegions
         have hcntr := ctx.sim.repr.operations_indices op hopin' |>.regions
         refine OperationPtr.nthRegion_frame ctx op hopin' ridx hnr (this.regions ridx hnr)
           (hagreeD _ _ ?_) ?_
           (by grind only [Erased.out_mk, OperationPtr.getRegion!_OperationPtr_setAttributes])
         · grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
         · have hidxc : ridx < (op.get! ctx.spec).capRegions := by grind
           have haddrR : ((op.toM.toNat : Nat) : Int) = op.id := by
             grind [Veir.OperationPtr.toM, _root_.Veir.OperationPtr.toFlat]
           have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op ridx.toUInt64
             (by grind [UInt64.toNat_ofNat']) hopin'
           refine hagreeD _ _ ?_
           grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt, UInt64.toNat_ofNat']
     · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
       · refine OperationPtr.numOperands_frame ctx op hopin' this.numOperands (hagreeD _ _ ?_)
           (by grind only [Erased.out_mk, OperationPtr.get!_OperationPtr_setAttributes])
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
       · intros oper operIb heq
         simp only [Sim.RawIRContext.spec] at *
         have hooIb : oper.InBounds ctx.spec := by grind
         have hoincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hooIb
         have hpib := Veir.Sim.OpOperandPtr.op_inBounds hooIb
         have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) oper.op hpib
         refine OpOperandPtr.matches_frame ctx oper hooIb (this.operands oper hooIb heq)
           (hagreeD _ _ ?_) hlayF (by grind only [Erased.out_mk, OpOperandPtr.get!_OperationPtr_setAttributes]) operIb
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
     · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
       · refine OperationPtr.numResults_frame ctx op hopin' this.numResults (hagreeD _ _ ?_)
           (by grind only [Erased.out_mk, OperationPtr.get!_OperationPtr_setAttributes])
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
       · intros res resIb heq
         simp only [Sim.RawIRContext.spec] at *
         have hresIb : res.InBounds ctx.spec := by grind
         have hrincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresIb
         have hpib := Veir.Sim.OpResultPtr.op_inBounds hresIb
         have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) res.op hpib
         refine OpResultPtr.matches_frame ctx res hresIb (this.results res hresIb heq)
           (hagreeD _ _ ?_) hlayF (by grind only [Erased.out_mk, OpResultPtr.get!_OperationPtr_setAttributes]) resIb
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
   · try simp only [Sim.RawIRContext.spec, Erased.out_mk]
     intros blk blkIb
     simp only [Sim.RawIRContext.spec] at *
     have hblin' : blk.InBounds ctx.spec := by grind
     have henc := ctx.sim.encoding_block blk hblin'
     have hbrange := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk hblin'
     have hdisjB := Veir.Sim.disjoint_block_operation (ctx := ctx) blk ptr.spec hblin' (by grind)
     constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
     · refine BlockPtr.matchesBase_frame ctx blk hblin' henc.toMatchesBase (hagreeD _ _ ?_) hlayF
         (by grind only [Erased.out_mk, BlockPtr.get!_OperationPtr_setAttributes])
         (by grind only [Erased.out_mk, BlockPtr.get!_OperationPtr_setAttributes])
         (by grind only [Erased.out_mk, BlockPtr.get!_OperationPtr_setAttributes])
         (by grind only [Erased.out_mk, BlockPtr.get!_OperationPtr_setAttributes])
         (by grind only [Erased.out_mk, BlockPtr.get!_OperationPtr_setAttributes])
         (by grind only [Erased.out_mk, BlockPtr.get!_OperationPtr_setAttributes]) blkIb
       grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
     · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
       · refine BlockPtr.numArguments_frame ctx blk hblin' henc.numArguments (hagreeD _ _ ?_)
           (by grind only [Erased.out_mk, BlockPtr.get!_OperationPtr_setAttributes])
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
       · intros arg argIn heq
         try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
         have hargIb : arg.InBounds ctx.spec := by grind
         have haincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargIb
         have hpib := Veir.Sim.BlockArgumentPtr.block_inBounds hargIb
         have hprangeS := Veir.Sim.BlockPtr.range_linear (ctx := ctx) arg.block hpib
         refine BlockArgumentPtr.matches_frame ctx arg hargIb (henc.arguments arg hargIb heq)
           (hagreeD _ _ ?_) hlayF (by grind only [Erased.out_mk, BlockArgumentPtr.get!_OperationPtr_setAttributes]) argIn
         grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
   · try simp only [Sim.RawIRContext.spec, Erased.out_mk]
     intros rg rgIb
     simp only [Sim.RawIRContext.spec] at *
     have hrgin' : rg.InBounds ctx.spec := by grind
     have henc := ctx.sim.encoding_region rg hrgin'
     have hrgrange := Veir.Sim.RegionPtr.range_linear (ctx := ctx) rg hrgin'
     have hdisjR := Veir.Sim.disjoint_region_operation (ctx := ctx) rg ptr.spec hrgin' (by grind)
     refine RegionPtr.matches_frame ctx rg hrgin' henc (hagreeD _ _ ?_) hlayF
       (by grind only [Erased.out_mk, RegionPtr.get!_OperationPtr_setAttributes]) rgIb
     grind (splits := 6) only [Erased.out_mk, isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
   · -- `insertAttrs` only pushes onto the attribute table and slot 0 is occupied, so the push leaves it unchanged.
     have := ctx.sim.attr_empty
     grind [Buffed.OperationMPtr.writeAttrs, Buffed.IRBufContext.insertAttrs]
   · simpa [Buffed.OperationMPtr.writeAttrs, hfree, hmem] using ctx.sim.free_valid
   · simp only [Buffed.OperationMPtr.writeAttrs, hfree]
     intro size address hm p hp
     simp only [Sim.RawIRContext.spec] at *
     have := ctx.sim.free_disjoint size address hm p (by grind)
     grind [TopLevelPtr]⟩

@[simp, grind →]
theorem Sim.OperationPtr.setAttributes_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (attrs : DictionaryAttr) (ib : ptr.InBounds ctx) :
    setAttributes ctx ptr attrs ib = some ctx →
    ctx.spec = ptr.spec.setAttributes ctx.spec attrs := by
  simp only [setAttributes]; grind

@[inline]
def Sim.OperationPtr.getAttributes (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : DictionaryAttr :=
  let idx := ptr.impl.readAttrs ctx.buf (by prove_setLinkBoundsOp ctx ptr)
  -- The `Sim` encoding invariant `attrs` says the stored attribute index points into the attribute table (`attributes[readAttrs!]? = some _`), which is exactly the array bound.
  (ctx.buf.attributes[idx.toNat]'(by
    have hattr := ctx.sim.encoding_op ptr.spec (by grind) |>.attrs
    grind)).asDict (by
    have hattr := ctx.sim.encoding_op ptr.spec (by grind) |>.attrs
    grind)

@[inline]
def Sim.OperationPtr.getAttributes! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : DictionaryAttr :=
  let idx := ptr.impl.readAttrs! ctx.buf
  -- Without an `InBounds` hypothesis nothing guarantees the read index lands on a dictionary in the attribute table, so fall back to `.empty` on garbage input.
  match ctx.buf.attributes[idx.toNat]! with
  | .dictionaryAttr dict => dict
  | _ => .empty

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getAttributes_eq_getAttributes! (ctx : IRContext OpInfo) ptr ib :
    getAttributes ctx ptr ib = getAttributes! ctx ptr := by
  have hattr := ctx.sim.encoding_op ptr.spec (by grind) |>.attrs
  simp [getAttributes, getAttributes!] <;> grind

@[inline]
def Sim.OperationPtr.getOperandPtr (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.OpOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeOperandOffset (OpInfo := OpInfo) ctx.buf index (by prove_setLinkBoundsOp ctx ptr),
   ptr.spec'.map (·.getOpOperand index.toNat)⟩


@[inline]
def Sim.OperationPtr.getOperandPtr! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.OpOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeOperandOffset! (OpInfo := OpInfo) ctx.buf index,
   ptr.spec'.map (·.getOpOperand index.toNat)⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getOperandPtr_eq_getOperandPtr! (ctx : IRContext OpInfo) ptr index ib :
    getOperandPtr ctx ptr index ib = getOperandPtr! ctx ptr index := by
  simp [getOperandPtr, getOperandPtr!]

/-! Loop-friendly operand accessors. `getOperandPtr` recomputes the operands base offset on every
call, which in generic code is a `propertySizeOfEncoded` call through the boxed `HasBuffedOpCode`
dictionary (one `lean_box_uint32` + `lean_apply_1` heap allocation pair per call).
`getOperandsOffset` exposes the base offset so loops can hoist the dispatch, `getOperandPtrAt`
builds an operand pointer from the hoisted offset, and `getOperandPtrOf` handles the
statically-known-op-type case where `Operation.propertySize c` folds to a literal. -/

@[inline]
def Sim.OperationPtr.getOperandsOffset (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Int64 :=
  ptr.impl.computeOperandsOffset (OpInfo := OpInfo) ctx.buf (by prove_setLinkBoundsOp ctx ptr)

@[simp, grind =]
theorem Sim.OperationPtr.getOperandsOffset_eq (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    getOperandsOffset ctx ptr ib = Buffed.Operation.Offsets.operands ptr.spec ctx.spec :=
  OperationPtr.computeOperandOffset_eq ctx ptr ib.ib ib.sim _

@[inline]
def Sim.OperationPtr.getOperandPtrAt (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (off : Int64) (index : UInt64) (_ib : ptr.InBounds ctx)
    (_hoff : off = Buffed.Operation.Offsets.operands ptr.spec ctx.spec) : Sim.OpOperandPtr :=
  ⟨ptr.impl + (off + Buffed.OpOperand.size * index), ptr.spec'.map (·.getOpOperand index.toNat)⟩

@[grind =]
theorem Sim.OperationPtr.getOperandPtrAt_eq_getOperandPtr (ctx : Sim.IRContext OpInfo)
    (ptr : Sim.OperationPtr) (off : Int64) (index : UInt64) (ib : ptr.InBounds ctx)
    (hoff : off = Buffed.Operation.Offsets.operands ptr.spec ctx.spec) :
    getOperandPtrAt ctx ptr off index ib hoff = getOperandPtr ctx ptr index ib := by
  simp only [getOperandPtrAt, getOperandPtr,
    Buffed.OperationMPtr.computeOperandOffset]
  rw [hoff, OperationPtr.computeOperandOffset_eq ctx ptr ib.ib ib.sim]

@[inline]
def Sim.OperationPtr.getOperandPtrOf (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (c : OpInfo) (index : UInt64)
    (_hty : ptr.getOpTypeEncoded! ctx = SerializableOpInfo.encode c) : Sim.OpOperandPtr :=
  ⟨ptr.impl + (Buffed.Operation.Offsets.properties + Buffed.Operation.propertySize c + Buffed.OpOperand.size * index),
   ptr.spec'.map (·.getOpOperand index.toNat)⟩

@[grind =]
theorem Sim.OperationPtr.getOperandPtrOf_eq_getOperandPtr! (ctx : Sim.IRContext OpInfo)
    (ptr : Sim.OperationPtr) (c : OpInfo) (index : UInt64)
    (hty : ptr.getOpTypeEncoded! ctx = SerializableOpInfo.encode c) :
    getOperandPtrOf ctx ptr c index hty = getOperandPtr! ctx ptr index := by
  rw [getOperandPtrOf]
  simp only [getOpTypeEncoded!] at hty
  simp only [getOperandPtr!,
    Buffed.OperationMPtr.computeOperandOffset!, Buffed.OperationMPtr.computeOperandsOffset!,
    hty, HasBuffedOpCode.propertySizeOfEncoded_eq, SerializableOpInfo.decode_encode]

@[inline]
def Sim.OperationPtr.getResultPtr (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.OpResultPtr :=
  ⟨ptr.impl + ptr.impl.computeResultOffset ctx.buf index (by prove_setLinkBoundsOp ctx ptr),
   ptr.spec'.map (·.getResult index.toNat)⟩

@[inline]
def Sim.OperationPtr.getResultPtr! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.OpResultPtr :=
  ⟨ptr.impl + ptr.impl.computeResultOffset! ctx.buf index,
   ptr.spec'.map (·.getResult index.toNat)⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getResultPtr_eq_getResultPtr! (ctx : IRContext OpInfo) ptr index ib :
    getResultPtr ctx ptr index ib = getResultPtr! ctx ptr index := by
  simp [getResultPtr, getResultPtr!]

@[inline]
def Sim.OperationPtr.getRegionPtr (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) (hindex : index.toNat < ptr.spec.getNumRegions! ctx.spec) : Sim.RegionPtr :=
  ⟨ptr.impl.readNthRegion (OpInfo := OpInfo) ctx.buf index (by prove_setLinkBoundsOp ctx ptr) (by prove_setLinkBoundsRegionSlot ctx ptr index),
   (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => ptr.getRegion! ctx index.toNat)⟩

@[inline]
def Sim.OperationPtr.getRegionPtr! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.RegionPtr :=
  ⟨ptr.impl.readNthRegion! (OpInfo := OpInfo) ctx.buf index,
   (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => ptr.getRegion! ctx index.toNat)⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getRegionPtr_eq_getRegionPtr! (ctx : IRContext OpInfo) ptr index ib hindex :
    getRegionPtr ctx ptr index ib hindex = getRegionPtr! ctx ptr index := by
  grind [getRegionPtr, getRegionPtr!]

@[inline]
def Sim.OperationPtr.getBlockOperandPtr (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.BlockOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeBlockOperandOffset (OpInfo := OpInfo) ctx.buf index (by prove_setLinkBoundsOp ctx ptr),
   ptr.spec'.map (·.getBlockOperand index.toNat)⟩

@[inline]
def Sim.OperationPtr.getBlockOperandPtr! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.BlockOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeBlockOperandOffset! (OpInfo := OpInfo) ctx.buf index,
   ptr.spec'.map (·.getBlockOperand index.toNat)⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getBlockOperandPtr_eq_getBlockOperandPtr! (ctx : IRContext OpInfo) ptr index ib :
    getBlockOperandPtr ctx ptr index ib = getBlockOperandPtr! ctx ptr index := by
  simp [getBlockOperandPtr, getBlockOperandPtr!]

@[inline]
def Sim.OperationPtr.getNumOperands (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumOperands ctx.buf (by prove_setLinkBoundsOp ctx ptr)

@[inline]
def Sim.OperationPtr.getNumOperands! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : UInt64 :=
  ptr.impl.readNumOperands! ctx.buf

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNumOperands_eq_getNumOperands! (ctx : IRContext OpInfo) ptr ib :
    getNumOperands ctx ptr ib = getNumOperands! ctx ptr := by
  simp [getNumOperands, getNumOperands!]

@[grind =]
theorem Sim.OperationPtr.getNumOperands!_spec (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} :
    (getNumOperands! ctx ptr) = (ptr.spec.get! ctx.spec).capOperands.toUInt64 := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).numOperands
  simp [getNumOperands!] <;> grind

@[grind =]
theorem Sim.OperationPtr.getNumOperands!_spec_of_wf (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} (wf : ctx.spec.WellFormed) :
    (getNumOperands! ctx ptr) = (ptr.spec.getNumOperands! ctx.spec).toUInt64 := by
  grind [wf.operations ptr.spec, OperationPtr.WellFormed.numOperands_eq_capOperands]

@[inline]
def Sim.OperationPtr.getNumSuccessors (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumBlockOperands ctx.buf (by prove_setLinkBoundsOp ctx ptr)

@[inline]
def Sim.OperationPtr.getNumSuccessors! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : UInt64 :=
  ptr.impl.readNumBlockOperands! ctx.buf

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNumSuccessors_eq_getNumSuccessors! (ctx : IRContext OpInfo) ptr ib :
    getNumSuccessors ctx ptr ib = getNumSuccessors! ctx ptr := by
  simp [getNumSuccessors, getNumSuccessors!]

@[grind =]
theorem Sim.OperationPtr.getNumSuccessors!_spec (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} :
    (getNumSuccessors! ctx ptr) = (ptr.spec.get! ctx.spec).capBlockOperands.toUInt64 := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).numBlockOperands
  simp [getNumSuccessors!] <;> grind

@[grind =]
theorem Sim.OperationPtr.getNumSuccessors!_spec_of_wf (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} (wf : ctx.spec.WellFormed) :
    (getNumSuccessors! ctx ptr) = (ptr.spec.getNumSuccessors! ctx.spec).toUInt64 := by
  grind [wf.operations ptr.spec, OperationPtr.WellFormed.numSuccessors_eq_capBlockOperands]

@[inline]
def Sim.OperationPtr.getNumResults (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumResults ctx.buf (by prove_setLinkBoundsOp ctx ptr)

@[inline]
def Sim.OperationPtr.getNumResults! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : UInt64 :=
  ptr.impl.readNumResults! ctx.buf

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNumResults_eq_getNumResults! (ctx : IRContext OpInfo) ptr ib :
    getNumResults ctx ptr ib = getNumResults! ctx ptr := by
  simp [getNumResults, getNumResults!]

@[grind =]
theorem Sim.OperationPtr.getNumResults!_spec (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} :
    (getNumResults! ctx ptr) = (ptr.spec.get! ctx.spec).capResults.toUInt64 := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).numResults
  simp [getNumResults!] <;> grind

@[grind =]
theorem Sim.OperationPtr.getNumResults!_spec_of_wf (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} (wf : ctx.spec.WellFormed) :
    (getNumResults! ctx ptr) = (ptr.spec.getNumResults! ctx.spec).toUInt64 := by
  grind [IRContext.WellFormed.operations]

@[inline]
def Sim.OperationPtr.getNumRegions (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumRegions ctx.buf (by prove_setLinkBoundsOp ctx ptr)

@[inline]
def Sim.OperationPtr.getNumRegions! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : UInt64 :=
  ptr.impl.readNumRegions! ctx.buf

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNumRegions_eq_getNumRegions! (ctx : IRContext OpInfo) ptr ib :
    getNumRegions ctx ptr ib = getNumRegions! ctx ptr := by
  simp [getNumRegions, getNumRegions!]

@[grind =]
theorem Sim.OperationPtr.getNumRegions!_spec (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} :
    (getNumRegions! ctx ptr) = (ptr.spec.get! ctx.spec).capRegions.toUInt64 := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).numRegions
  simp [getNumRegions!] <;> grind

@[grind =]
theorem Sim.OperationPtr.getNumRegions!_spec_of_wf (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} (wf : ctx.spec.WellFormed) :
    (getNumRegions! ctx ptr) = (ptr.spec.getNumRegions! ctx.spec).toUInt64 := by
  grind [IRContext.WellFormed.operations]

@[inline]
def Sim.OpOperandPtr.setNextUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl (by prove_setLinkBoundsOpOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec, nextUse.spec)).map (fun (ptr, ctx, value) => ptr.setNextUse! ctx value), by
    prove_setLinkSim ctx oo Buffed.OpOperandMPtr.writeNextUse opOperandMPtr_writeNextUse OpOperandPtr_setNextUse
      (ptr.spec.setNextUse ctx.spec nextUse.spec (by grind)) nextUseIb⟩

open Classical in
noncomputable def Sim.OpOperandPtr.setNextUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpOperand.Offsets.nextUse).toInt + Buffed.OpOperand.Sizes.nextUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandMPtr.writeNextUse ctx.buf ptr.impl nextUse.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, nextUse.spec)).map (fun (ptr, ctx, value) => ptr.setNextUse! ctx value) } then
    ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl h₁, (Erased.mk (ptr.spec, ctx.spec, nextUse.spec)).map (fun (ptr, ctx, value) => ptr.setNextUse! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setNextUse_eq_setNextUse! (ctx : IRContext OpInfo) ptr nextUse ib nextUseIb :
    setNextUse ctx ptr nextUse ib nextUseIb = setNextUse! ctx ptr nextUse := by
  simp [setNextUse, setNextUse!]
  split
  · grind
  · prove_setLinkBoundsOpOperand ctx ptr

@[simp, grind =]
theorem Sim.OpOperandPtr.setNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse ctx ptr nextUse ib nextUseIb).spec = ptr.spec.setNextUse ctx.spec nextUse.spec := by
  grind [setNextUse]

@[simp, grind =]
theorem Sim.OpOperandPtr.setNextUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse! ctx ptr nextUse).spec = ptr.spec.setNextUse! ctx.spec nextUse.spec := by
  grind

@[inline]
def Sim.OpOperandPtr.getNextUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readNextUse ctx.buf (by prove_setLinkBoundsOpOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).nextUse)⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).nextUse := by
  grind [getNextUse]

@[grind .]
theorem Sim.OpOperandPtr.getNextUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind)
    |>.nextUse
  grind [getNextUse]

@[inline]
def Sim.OpOperandPtr.getNextUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readNextUse! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).nextUse)⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getNextUse_eq_getNextUse! (ctx : IRContext OpInfo) ptr ib :
    getNextUse ctx ptr ib = getNextUse! ctx ptr := by
  simp [getNextUse, getNextUse!] <;> grind

@[inline]
def Sim.OpOperandPtr.setBack (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeBack ctx.buf back.impl (by prove_setLinkBoundsOpOperand ctx ptr),
  (Erased.mk (ptr.spec, ctx.spec, back.spec)).map (fun (ptr, ctx, value) => ptr.setBack! ctx value), by
    prove_setLinkSim ctx oo Buffed.OpOperandMPtr.writeBack opOperandMPtr_writeBack OpOperandPtr_setBack
      (ptr.spec.setBack ctx.spec back.spec (by grind)) backIb⟩

open Classical in
noncomputable def Sim.OpOperandPtr.setBack! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpOperand.Offsets.back).toInt + Buffed.OpOperand.Sizes.back.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandMPtr.writeBack ctx.buf ptr.impl back.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, back.spec)).map (fun (ptr, ctx, value) => ptr.setBack! ctx value) } then
    ⟨ptr.impl.writeBack ctx.buf back.impl h₁, (Erased.mk (ptr.spec, ctx.spec, back.spec)).map (fun (ptr, ctx, value) => ptr.setBack! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setBack_eq_setBack! (ctx : IRContext OpInfo) ptr back ib backIb :
    setBack ctx ptr back ib backIb = setBack! ctx ptr back := by
  simp [setBack, setBack!]
  split
  · grind
  · prove_setLinkBoundsOpOperand ctx ptr

@[simp, grind =]
theorem Sim.OpOperandPtr.setBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack ctx ptr back ib backIb).spec = ptr.spec.setBack ctx.spec back.spec := by
  grind [setBack]

@[simp, grind =]
theorem Sim.OpOperandPtr.setBack!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack! ctx ptr back).spec = ptr.spec.setBack! ctx.spec back.spec := by
  grind

@[inline]
def Sim.OpOperandPtr.getBack (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OpOperandPtrPtr :=
  ⟨ptr.impl.readBack ctx.buf (by prove_setLinkBoundsOpOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).back)⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).spec = (ptr.spec.get ctx.spec).back := by
  grind [getBack]

@[grind .]
theorem Sim.OpOperandPtr.getBack_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind)
    |>.back
  grind [getBack]

@[inline]
def Sim.OpOperandPtr.getBack! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.OpOperandPtrPtr :=
  ⟨ptr.impl.readBack! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).back)⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getBack_eq_getBack! (ctx : IRContext OpInfo) ptr ib :
    getBack ctx ptr ib = getBack! ctx ptr := by
  simp [getBack, getBack!] <;> grind

@[inline]
def Sim.OpOperandPtr.setOwner (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl (by prove_setLinkBoundsOpOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value), by
    prove_setLinkSim ctx oo Buffed.OpOperandMPtr.writeOwner opOperandMPtr_writeOwner OpOperandPtr_setOwner
      (ptr.spec.setOwner ctx.spec owner.spec (by grind)) ownerIb⟩

open Classical in
noncomputable def Sim.OpOperandPtr.setOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpOperand.Offsets.owner).toInt + Buffed.OpOperand.Sizes.owner.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandMPtr.writeOwner ctx.buf ptr.impl owner.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value) } then
    ⟨ptr.impl.writeOwner ctx.buf owner.impl h₁, (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner, setOwner!]
  split
  · grind
  · prove_setLinkBoundsOpOperand ctx ptr

@[simp, grind =]
theorem Sim.OpOperandPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  grind [setOwner]

@[simp, grind =]
theorem Sim.OpOperandPtr.setOwner!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner! ctx ptr owner).spec = ptr.spec.setOwner! ctx.spec owner.spec := by
  grind

@[inline]
def Sim.OpOperandPtr.getOwner (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner ctx.buf (by prove_setLinkBoundsOpOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).owner)⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  grind [getOwner]

@[grind .]
theorem Sim.OpOperandPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind)
    |>.owner
  grind [getOwner]

@[inline]
def Sim.OpOperandPtr.getOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).owner)⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner, getOwner!] <;> grind

@[inline]
def Sim.OpOperandPtr.setValue (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeValue ctx.buf value.impl (by prove_setLinkBoundsOpOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.setValue! ctx value), by
    prove_setLinkSim ctx oo Buffed.OpOperandMPtr.writeValue opOperandMPtr_writeValue OpOperandPtr_setValue
      (ptr.spec.setValue ctx.spec value.spec (by grind)) valueIb⟩

open Classical in
noncomputable def Sim.OpOperandPtr.setValue! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpOperand.Offsets.value).toInt + Buffed.OpOperand.Sizes.value.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandMPtr.writeValue ctx.buf ptr.impl value.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.setValue! ctx value) } then
    ⟨ptr.impl.writeValue ctx.buf value.impl h₁, (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.setValue! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setValue_eq_setValue! (ctx : IRContext OpInfo) ptr value ib valueIb :
    setValue ctx ptr value ib valueIb = setValue! ctx ptr value := by
  simp [setValue, setValue!]
  split
  · grind
  · prove_setLinkBoundsOpOperand ctx ptr

@[simp, grind =]
theorem Sim.OpOperandPtr.setValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue ctx ptr value ib valueIb).spec = ptr.spec.setValue ctx.spec value.spec := by
  grind [setValue]

@[simp, grind =]
theorem Sim.OpOperandPtr.setValue!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue! ctx ptr value).spec = ptr.spec.setValue! ctx.spec value.spec := by
  grind

@[inline]
def Sim.OpOperandPtr.getValue (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.ValuePtr :=
  ⟨ptr.impl.readValue ctx.buf (by prove_setLinkBoundsOpOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).value)⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).spec = (ptr.spec.get ctx.spec).value := by
  grind [getValue]

@[grind .]
theorem Sim.OpOperandPtr.getValue_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind) |>.value
  grind [getValue]

@[inline]
def Sim.OpOperandPtr.getValue! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.ValuePtr :=
  ⟨ptr.impl.readValue! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).value)⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getValue_eq_getValue! (ctx : IRContext OpInfo) ptr ib :
    getValue ctx ptr ib = getValue! ctx ptr := by
  simp [getValue, getValue!] <;> grind

@[inline]
def Sim.OpResultPtr.setFirstUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl (by prove_setLinkBoundsOpResult ctx ptr), (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value), by
    prove_setLinkSim ctx rs Buffed.OpResultMPtr.writeFirstUse opResultMPtr_writeFirstUse OpResultPtr_setFirstUse
      (ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind)) firstUseIb⟩

open Classical in
noncomputable def Sim.OpResultPtr.setFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.ValueImpl.Offsets.firstUse).toInt + Buffed.ValueImpl.Sizes.firstUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl firstUse.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value) } then
    ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl h₁, (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse, setFirstUse!]
  split
  · grind
  · prove_setLinkBoundsOpResult ctx ptr

@[simp, grind =]
theorem Sim.OpResultPtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  grind [setFirstUse]

@[simp, grind =]
theorem Sim.OpResultPtr.setFirstUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse! ctx ptr firstUse).spec = ptr.spec.setFirstUse! ctx.spec firstUse.spec := by
  grind

@[inline]
def Sim.OpResultPtr.getFirstUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf (by prove_setLinkBoundsOpResult ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstUse)⟩

@[simp, grind =]
theorem Sim.OpResultPtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstUse := by
  grind [getFirstUse]

@[grind .]
theorem Sim.OpResultPtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpResultPtr.inBounds_def])
    |>.results ptr.spec (by grind) (by grind) |>.firstUse
  grind [getFirstUse]

@[inline]
def Sim.OpResultPtr.getFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstUse)⟩

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse, getFirstUse!] <;> grind

@[inline]
def Sim.OpResultPtr.setOwner (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl (by prove_setLinkBoundsOpResult ctx ptr), (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value), by
    prove_setLinkSim ctx rs Buffed.OpResultMPtr.writeOwner opResultMPtr_writeOwner OpResultPtr_setOwner
      (ptr.spec.setOwner ctx.spec owner.spec (by grind)) ownerIb⟩

open Classical in
noncomputable def Sim.OpResultPtr.setOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpResult.Offsets.owner).toInt + Buffed.OpResult.Sizes.owner.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl owner.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value) } then
    ⟨ptr.impl.writeOwner ctx.buf owner.impl h₁, (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner, setOwner!]
  split
  · grind
  · prove_setLinkBoundsOpResult ctx ptr

@[simp, grind =]
theorem Sim.OpResultPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  grind [setOwner]

@[simp, grind =]
theorem Sim.OpResultPtr.setOwner!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner! ctx ptr owner).spec = ptr.spec.setOwner! ctx.spec owner.spec := by
  grind

@[inline]
def Sim.OpResultPtr.getOwner (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner ctx.buf (by prove_setLinkBoundsOpResult ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).owner)⟩

@[simp, grind =]
theorem Sim.OpResultPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  grind [getOwner]

@[grind .]
theorem Sim.OpResultPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpResultPtr.inBounds_def])
    |>.results ptr.spec (by grind) (by grind) |>.owner
  grind [getOwner]

@[inline]
def Sim.OpResultPtr.getOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).owner)⟩

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner, getOwner!] <;> grind

@[inline]
def Sim.BlockArgumentPtr.setFirstUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl (by prove_setLinkBoundsBlockArgument ctx ptr), (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value), by
    prove_setLinkSim ctx ba Buffed.BlockArgumentMPtr.writeFirstUse blockArgumentMPtr_writeFirstUse BlockArgumentPtr_setFirstUse
      (ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind)) firstUseIb⟩

open Classical in
noncomputable def Sim.BlockArgumentPtr.setFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.ValueImpl.Offsets.firstUse).toInt + Buffed.ValueImpl.Sizes.firstUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf ptr.impl firstUse.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value) } then
    ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl h₁, (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse, setFirstUse!]
  split
  · grind
  · prove_setLinkBoundsBlockArgument ctx ptr

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  grind [setFirstUse]

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setFirstUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse! ctx ptr firstUse).spec = ptr.spec.setFirstUse! ctx.spec firstUse.spec := by
  grind

@[inline]
def Sim.BlockArgumentPtr.getFirstUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf (by prove_setLinkBoundsBlockArgument ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstUse)⟩

@[simp, grind =]
theorem Sim.BlockArgumentPtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstUse := by
  grind [getFirstUse]

@[grind .]
theorem Sim.BlockArgumentPtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_block ptr.spec.block (by grind [Veir.BlockArgumentPtr.inBounds_def])
   |>.arguments ptr.spec (by grind) (by grind) |>.firstUse
  grind [getFirstUse]

@[inline]
def Sim.BlockArgumentPtr.getFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstUse)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse, getFirstUse!] <;> grind

@[inline]
def Sim.BlockArgumentPtr.setIndex (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : UInt64) (ib : ptr.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeIndex ctx.buf index (by prove_setLinkBoundsBlockArgument ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => ptr.setIndex! ctx index.toNat), by
    prove_setLinkSim ctx ba Buffed.BlockArgumentMPtr.writeIndex blockArgumentMPtr_writeIndex BlockArgumentPtr_setIndex
      (ptr.spec.setIndex ctx.spec index.toNat (by grind))⟩

open Classical in
noncomputable def Sim.BlockArgumentPtr.setIndex! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : UInt64) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockArgument.Offsets.index).toInt + Buffed.BlockArgument.Sizes.index.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockArgumentMPtr.writeIndex ctx.buf ptr.impl index h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => ptr.setIndex! ctx index.toNat) } then
    ⟨ptr.impl.writeIndex ctx.buf index h₁, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => ptr.setIndex! ctx index.toNat), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.setIndex_eq_setIndex! (ctx : IRContext OpInfo) ptr index ib :
    setIndex ctx ptr index ib = setIndex! ctx ptr index := by
  simp [setIndex, setIndex!]
  split
  · grind
  · prove_setLinkBoundsBlockArgument ctx ptr

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setIndex_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : UInt64)
    (ib : ptr.InBounds ctx) :
    (setIndex ctx ptr index ib).spec = ptr.spec.setIndex ctx.spec index.toNat := by
  grind [setIndex]

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setIndex!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : UInt64)
    (ib : ptr.InBounds ctx) :
    (setIndex! ctx ptr index).spec = ptr.spec.setIndex! ctx.spec index.toNat := by
  grind

@[inline]
def Sim.BlockArgumentPtr.getIndex (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (_index : Nat) (ib : ptr.InBounds ctx) : Nat :=
  (ptr.impl.readIndex ctx.buf (by prove_setLinkBoundsBlockArgument ctx ptr)).toNat

@[inline]
def Sim.BlockArgumentPtr.getIndex! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (_index : Nat) : Nat :=
  (ptr.impl.readIndex! ctx.buf).toNat

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.getIndex_eq_getIndex! (ctx : IRContext OpInfo) ptr index ib :
    getIndex ctx ptr index ib = getIndex! ctx ptr index := by
  simp [getIndex, getIndex!]

@[inline]
def Sim.BlockArgumentPtr.setOwner (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl (by prove_setLinkBoundsBlockArgument ctx ptr), (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value), by
    prove_setLinkSim ctx ba Veir.Buffed.BlockArgumentMPtr.writeOwner blockArgumentMPtr_writeOwner BlockArgumentPtr_setOwner
      (ptr.spec.setOwner ctx.spec owner.spec (by grind)) ownerIb⟩

open Classical in
noncomputable def Sim.BlockArgumentPtr.setOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockArgument.Offsets.owner).toInt + Buffed.BlockArgument.Sizes.owner.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockArgumentMPtr.writeOwner ctx.buf ptr.impl owner.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value) } then
    ⟨ptr.impl.writeOwner ctx.buf owner.impl h₁, (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner, setOwner!]
  split
  · grind
  · prove_setLinkBoundsBlockArgument ctx ptr

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  grind [setOwner]

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setOwner!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner! ctx ptr owner).spec = ptr.spec.setOwner! ctx.spec owner.spec := by
  grind

@[inline]
def Sim.BlockArgumentPtr.getOwner (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) : Sim.BlockPtr :=
  ⟨ptr.impl.readOwner ctx.buf (by prove_setLinkBoundsBlockArgument ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).owner)⟩

@[simp, grind =]
theorem Sim.BlockArgumentPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  grind [getOwner]

@[grind .]
theorem Sim.BlockArgumentPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_block ptr.spec.block (by grind [Veir.BlockArgumentPtr.inBounds_def])
    |>.arguments ptr.spec (by grind) (by grind) |>.owner
  grind [getOwner]

@[inline]
def Sim.BlockArgumentPtr.getOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr) : Sim.BlockPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).owner)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner, getOwner!] <;> grind

@[inline]
def Sim.BlockOperandPtr.setNextUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl (by prove_setLinkBoundsBlockOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec, nextUse.spec)).map (fun (ptr, ctx, value) => ptr.setNextUse! ctx value), by
    prove_setLinkSim ctx bo Buffed.BlockOperandMPtr.writeNextUse blockOperandMPtr_writeNextUse BlockOperandPtr_setNextUse
      (ptr.spec.setNextUse ctx.spec nextUse.spec (by grind)) nextUseIb⟩

open Classical in
noncomputable def Sim.BlockOperandPtr.setNextUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockOperand.Offsets.nextUse).toInt + Buffed.BlockOperand.Sizes.nextUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandMPtr.writeNextUse ctx.buf ptr.impl nextUse.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, nextUse.spec)).map (fun (ptr, ctx, value) => ptr.setNextUse! ctx value) } then
    ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl h₁, (Erased.mk (ptr.spec, ctx.spec, nextUse.spec)).map (fun (ptr, ctx, value) => ptr.setNextUse! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setNextUse_eq_setNextUse! (ctx : IRContext OpInfo) ptr nextUse ib nextUseIb :
    setNextUse ctx ptr nextUse ib nextUseIb = setNextUse! ctx ptr nextUse := by
  simp [setNextUse, setNextUse!]
  split
  · grind
  · prove_setLinkBoundsBlockOperand ctx ptr

@[simp, grind =]
theorem Sim.BlockOperandPtr.setNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse ctx ptr nextUse ib nextUseIb).spec = ptr.spec.setNextUse ctx.spec nextUse.spec := by
  grind [setNextUse]

@[simp, grind =]
theorem Sim.BlockOperandPtr.setNextUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse! ctx ptr nextUse).spec = ptr.spec.setNextUse! ctx.spec nextUse.spec := by
  grind

@[inline]
def Sim.BlockOperandPtr.getNextUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readNextUse ctx.buf (by prove_setLinkBoundsBlockOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).nextUse)⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).nextUse := by
  grind [getNextUse]

@[grind .]
theorem Sim.BlockOperandPtr.getNextUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.nextUse
  grind [getNextUse]

@[inline]
def Sim.BlockOperandPtr.getNextUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readNextUse! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).nextUse)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getNextUse_eq_getNextUse! (ctx : IRContext OpInfo) ptr ib :
    getNextUse ctx ptr ib = getNextUse! ctx ptr := by
  simp [getNextUse, getNextUse!] <;> grind

@[inline]
def Sim.BlockOperandPtr.setBack (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeBack ctx.buf back.impl (by prove_setLinkBoundsBlockOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec, back.spec)).map (fun (ptr, ctx, value) => ptr.setBack! ctx value), by
    prove_setLinkSim ctx bo Buffed.BlockOperandMPtr.writeBack blockOperandMPtr_writeBack BlockOperandPtr_setBack
      (ptr.spec.setBack ctx.spec back.spec (by grind)) backIb⟩

open Classical in
noncomputable def Sim.BlockOperandPtr.setBack! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockOperand.Offsets.back).toInt + Buffed.BlockOperand.Sizes.back.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandMPtr.writeBack ctx.buf ptr.impl back.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, back.spec)).map (fun (ptr, ctx, value) => ptr.setBack! ctx value) } then
    ⟨ptr.impl.writeBack ctx.buf back.impl h₁, (Erased.mk (ptr.spec, ctx.spec, back.spec)).map (fun (ptr, ctx, value) => ptr.setBack! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setBack_eq_setBack! (ctx : IRContext OpInfo) ptr back ib backIb :
    setBack ctx ptr back ib backIb = setBack! ctx ptr back := by
  simp [setBack, setBack!]
  split
  · grind
  · prove_setLinkBoundsBlockOperand ctx ptr

@[simp, grind =]
theorem Sim.BlockOperandPtr.setBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack ctx ptr back ib backIb).spec = ptr.spec.setBack ctx.spec back.spec := by
  grind [setBack]

@[simp, grind =]
theorem Sim.BlockOperandPtr.setBack!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack! ctx ptr back).spec = ptr.spec.setBack! ctx.spec back.spec := by
  grind

@[inline]
def Sim.BlockOperandPtr.getBack (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.BlockOperandPtrPtr :=
  ⟨ptr.impl.readBack ctx.buf (by prove_setLinkBoundsBlockOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).back)⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).spec = (ptr.spec.get ctx.spec).back := by
  grind [getBack]

@[grind .]
theorem Sim.BlockOperandPtr.getBack_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.back
  grind [getBack]

@[inline]
def Sim.BlockOperandPtr.getBack! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.BlockOperandPtrPtr :=
  ⟨ptr.impl.readBack! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).back)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getBack_eq_getBack! (ctx : IRContext OpInfo) ptr ib :
    getBack ctx ptr ib = getBack! ctx ptr := by
  simp [getBack, getBack!] <;> grind

@[inline]
def Sim.BlockOperandPtr.setOwner (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl (by prove_setLinkBoundsBlockOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value), by
    prove_setLinkSim ctx bo Buffed.BlockOperandMPtr.writeOwner blockOperandMPtr_writeOwner BlockOperandPtr_setOwner
      (ptr.spec.setOwner ctx.spec owner.spec (by grind)) ownerIb⟩

open Classical in
noncomputable def Sim.BlockOperandPtr.setOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockOperand.Offsets.owner).toInt + Buffed.BlockOperand.Sizes.owner.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandMPtr.writeOwner ctx.buf ptr.impl owner.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value) } then
    ⟨ptr.impl.writeOwner ctx.buf owner.impl h₁, (Erased.mk (ptr.spec, ctx.spec, owner.spec)).map (fun (ptr, ctx, value) => ptr.setOwner! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner, setOwner!]
  split
  · grind
  · prove_setLinkBoundsBlockOperand ctx ptr

@[simp, grind =]
theorem Sim.BlockOperandPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  grind [setOwner]

@[simp, grind =]
theorem Sim.BlockOperandPtr.setOwner!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner! ctx ptr owner).spec = ptr.spec.setOwner! ctx.spec owner.spec := by
  grind

@[inline]
def Sim.BlockOperandPtr.getOwner (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner ctx.buf (by prove_setLinkBoundsBlockOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).owner)⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  grind [getOwner]

@[grind .]
theorem Sim.BlockOperandPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.owner
  grind [getOwner]

@[inline]
def Sim.BlockOperandPtr.getOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).owner)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner, getOwner!] <;> grind

@[inline]
def Sim.BlockOperandPtr.setValue (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeValue ctx.buf value.impl (by prove_setLinkBoundsBlockOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.setValue! ctx value), by
    prove_setLinkSim ctx bo Buffed.BlockOperandMPtr.writeValue blockOperandMPtr_writeValue BlockOperandPtr_setValue
      (ptr.spec.setValue ctx.spec value.spec (by grind)) valueIb⟩

open Classical in
noncomputable def Sim.BlockOperandPtr.setValue! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockOperand.Offsets.value).toInt + Buffed.BlockOperand.Sizes.value.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandMPtr.writeValue ctx.buf ptr.impl value.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.setValue! ctx value) } then
    ⟨ptr.impl.writeValue ctx.buf value.impl h₁, (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.setValue! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setValue_eq_setValue! (ctx : IRContext OpInfo) ptr value ib valueIb :
    setValue ctx ptr value ib valueIb = setValue! ctx ptr value := by
  simp [setValue, setValue!]
  split
  · grind
  · prove_setLinkBoundsBlockOperand ctx ptr

@[simp, grind =]
theorem Sim.BlockOperandPtr.setValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue ctx ptr value ib valueIb).spec = ptr.spec.setValue ctx.spec value.spec := by
  grind [setValue]

@[simp, grind =]
theorem Sim.BlockOperandPtr.setValue!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue! ctx ptr value).spec = ptr.spec.setValue! ctx.spec value.spec := by
  grind

@[inline]
def Sim.BlockOperandPtr.getValue (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.BlockPtr :=
  ⟨ptr.impl.readValue ctx.buf (by prove_setLinkBoundsBlockOperand ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).value)⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).spec = (ptr.spec.get ctx.spec).value := by
  grind [getValue]

@[grind .]
theorem Sim.BlockOperandPtr.getValue_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.value
  grind [getValue]

@[inline]
def Sim.BlockOperandPtr.getValue! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.BlockPtr :=
  ⟨ptr.impl.readValue! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).value)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getValue_eq_getValue! (ctx : IRContext OpInfo) ptr ib :
    getValue ctx ptr ib = getValue! ctx ptr := by
  simp [getValue, getValue!] <;> grind

@[inline]
def Sim.BlockPtr.allocEmptyImpl (ctx₀ : Buffed.IRBufContext) (numArgs : UInt64)
    (hnumArgs : numArgs.toNat ≤ Buffed.countCard) : Option (Buffed.IRBufContext × Buffed.BlockMPtr) :=
  let size := Buffed.BlockMPtr.computeBlockSize numArgs
  let ptr : Buffed.BlockMPtr := ctx₀.usize
  rlet halloc : ctx ← ctx₀.alloc size.toUInt64
  have hsize : ctx.size = ctx₀.size + size.toUInt64.toNat := ctx₀.alloc_size halloc
  have hbsize : size.toUInt64.toNat = Buffed.Block.sizeBaseNat + numArgs.toNat * Buffed.BlockArgument.sizeNat :=
    Buffed.BlockMPtr.computeBlockSize_toNat numArgs hnumArgs
  let ctx := ptr.writeNumArguments ctx numArgs (by prove_allocBounds ctx₀)
  let ctx := ptr.writeFirstUse ctx .none (by prove_allocBounds ctx₀)
  let ctx := ptr.writePrev ctx .none (by prove_allocBounds ctx₀)
  let ctx := ptr.writeNext ctx .none (by prove_allocBounds ctx₀)
  let ctx := ptr.writeParent ctx .none (by prove_allocBounds ctx₀)
  let ctx := ptr.writeFirstOp ctx .none (by prove_allocBounds ctx₀)
  let ctx := ptr.writeLastOp ctx .none (by prove_allocBounds ctx₀)
  some (ctx, ptr)

theorem Sim.BlockPtr.allocEmptyImpl_freeList {ctx₀ ctxBuf : Buffed.IRBufContext}
    {ptr : UInt64} (numArgs : UInt64) (hnumArgs : numArgs.toNat ≤ Buffed.countCard)
    (h : allocEmptyImpl ctx₀ numArgs hnumArgs = some (ctxBuf, ptr)) :
    ctxBuf.freeList = ctx₀.freeList := by
  simp only [allocEmptyImpl] at h
  split at h
  · contradiction
  · rename_i buf halloc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Buffed.IRBufContext.alloc_freeList (bctx' := buf) halloc

@[noinline]
def Sim.BlockPtr.allocEmptySpec (ctx : Veir.IRContext OpInfo) (capArguments : Nat) (address : UInt64) : Option (Veir.IRContext OpInfo × Veir.BlockPtr) :=
  BlockPtr.allocEmptyAtAddress ctx capArguments address.toNat

theorem Sim.BlockPtr.slot_free (ctx : Sim.IRContext OpInfo) :
    ¬ (⟨ctx.buf.mem.size⟩ : Veir.BlockPtr).InBounds ctx.spec := by
  intro hin
  have := ctx.sim.in_bounds (.block ⟨ctx.buf.mem.size⟩) (by grind)
  simp only [TopLevelPtr.range, Veir.BlockPtr.range, Veir.BlockPtr.toFlat, IsIncludedIN] at this
  grind

set_option maxHeartbeats 8000000 in
/-- The `Sim` relation survives an empty-block allocation. -/
theorem Sim.BlockPtr.allocEmpty_sim (ctx : Sim.IRContext OpInfo) (numArgs : UInt64)
    (hnumArgs : numArgs.toNat ≤ Buffed.countCard)
    {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.BlockMPtr}
    (heq : Sim.BlockPtr.allocEmptyImpl ctx.buf numArgs hnumArgs = some (ctxBuf, ptrImpl))
    {ctxSpec : Veir.IRContext OpInfo} {ptrSpec : Veir.BlockPtr}
    (hspec : Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptrImpl.toNat = some (ctxSpec, ptrSpec)) :
    Veir.Sim (OpInfo := OpInfo) ⟨ctxBuf, .mk ctxSpec⟩ := by
  have hfree := Sim.BlockPtr.allocEmptyImpl_freeList numArgs hnumArgs heq
  simp only [Sim.BlockPtr.allocEmptyImpl] at heq
  split at heq
  · exact absurd heq (by simp)
  · rename_i buf halloc
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨hctxBuf, rfl⟩ := heq
    have hu := ctx.buf.usize_toNat
    have hs := ctx.buf.size_def
    have hgrow := ctx.buf.alloc_size halloc
    have hfits := buf.mem.fits_in_memory
    have hbsize := Buffed.BlockMPtr.computeBlockSize_toNat numArgs hnumArgs
    have hsize : ctx.buf.mem.size < 2 ^ 63 := by
      simp only [Buffed.IRBufContext.size_def, Int64.maxNatValue] at *; omega
    have hptr := Veir.BlockPtr.allocEmptyAtAddress_ptr hspec
    have hlay := Veir.BlockPtr.allocEmptyAtAddress_preservesLayout hspec
    have hsizeAlloc : buf.size = ctx.buf.size + (Buffed.BlockMPtr.computeBlockSize numArgs).toUInt64.toNat := hgrow
    have hread : ∀ (w : Nat) (a len : UInt64), a.toNat + len.toNat ≤ ctx.buf.mem.size →
        ctxBuf.mem.read! (w := w) a len
        = ctx.buf.mem.read! a len := by
      intro w a len ha
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      rw [← hctxBuf]; clear hctxBuf
      have hab : a.toNat + len.toNat ≤ ctx.buf.usize.toNat := by grind
      have husz63 : ctx.buf.usize.toNat < 2 ^ 63 := by grind
      have ek : ∀ (off : Int64), 0 ≤ off.toInt → off.toInt ≤ 48 →
          a.toNat + len.toNat ≤ (ctx.buf.usize + off).toNat := by
        intro off h0 h48
        try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
      have hincl : IsIncluded (a.toNat...(a.toNat + len.toNat)) ctx.buf.mem.range := by
        simp only [IsIncluded]; grind [ExArray.range_lower, ExArray.range_upper]
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp,
          Buffed.BlockMPtr.writeParent, Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev,
          Buffed.BlockMPtr.writeFirstUse, Buffed.BlockMPtr.writeNumArguments]
        rw [ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.lastOp (by decide) (by decide); omega),
          ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.firstOp (by decide) (by decide); omega),
          ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.parent (by decide) (by decide); omega),
          ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.next (by decide) (by decide); omega),
          ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.prev (by decide) (by decide); omega),
          ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.firstUse (by decide) (by decide); omega),
          ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.numArguments (by decide) (by decide); omega),
          ExArray.read!_extend _ _ _ _ _ hincl]
      · exact absurd halloc (by simp)
    have hsizele : ctx.buf.mem.size ≤ ctxBuf.mem.size := by
      rw [← hctxBuf]; clear hctxBuf
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp,
          Buffed.BlockMPtr.writeParent, Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev,
          Buffed.BlockMPtr.writeFirstUse, Buffed.BlockMPtr.writeNumArguments]
        grind [ExArray.blit64_size, ExArray.extend_size]
      · exact absurd halloc (by simp)
    have hattr : ctxBuf.attributes
        = ctx.buf.attributes := by
      rw [← hctxBuf]; clear hctxBuf
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp,
          Buffed.BlockMPtr.writeParent, Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev,
          Buffed.BlockMPtr.writeFirstUse, Buffed.BlockMPtr.writeNumArguments]
      · exact absurd halloc (by simp)
    have hagree : Buffed.AgreesOn ctxBuf ctx.buf 0 ctx.buf.mem.size :=
      ⟨hsizele, fun w a len _ ha => hread w a len ha, fun _ _ h => by simp only [hattr]; exact h⟩
    have hptrrepr : ptrSpec.IsRepr := by
      simp only [Veir.BlockPtr.IsRepr, Veir.BlockPtr.toFlat, hptr, Int64.maxNatValue] at *
      omega
    have hnewrepr : ctxSpec.IsRepr :=
      BlockPtr.allocEmptyAtAddress_fieldsIsRepr hspec (by simpa using hnumArgs) hptrrepr ctx.sim.repr
    have hrange : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
        p.range ctxSpec = p.range ctx.spec := by
      intro p hp
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      cases p with
      | operation op => exact LayoutPreserved.same_operationPtr_range op (by simpa using hp) hlay |>.symm
      | block bl => exact LayoutPreserved.same_blockPtr_range bl (by simpa using hp) hlay |>.symm
      | region rg => rfl
    have hupper : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
        (p.range ctxSpec).upper ≤ ctx.buf.mem.size := by
      intro p hp
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      have hin := ctx.sim.in_bounds p hp
      rw [hrange p hp]
      simp only [IsIncludedIN, Sim.RawIRContext.spec] at hin
      simp only [ExArray.range_lower, ExArray.range_upper] at hin
      simp only [Sim.IRContext.spec]
      omega
    have hmem : ∀ (p : TopLevelPtr), p.InBounds ctxSpec →
        p.InBounds ctx.spec ∨ p = .block ptrSpec := by
      intro p hp
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      cases p with
      | operation op =>
        rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.operation op) hspec).mp (by simpa using hp)
          with h | h | h
        · exact Or.inl (by simpa using h)
        · exact absurd h (by simp)
        · exact absurd h (by simp)
      | block bl =>
        rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block bl) hspec).mp (by simpa using hp)
          with h | h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simp only [GenericPtr.block.injEq] at h; grind)
        · exact absurd h (by simp)
      | region rg =>
        rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.region rg) hspec).mp (by simpa using hp)
          with h | h | h
        · exact Or.inl (by simpa using h)
        · exact absurd h (by simp)
        · exact absurd h (by simp)
    have hnewlow : (Veir.BlockPtr.range ptrSpec ctxSpec).lower = (ctx.buf.mem.size : Int) := by
      simp only [Veir.BlockPtr.range, Veir.BlockPtr.toFlat, Buffed.Block.range, hptr,
        add_nat_range_def]
      grind
    constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
    · -- fieldsInBounds (spec only)
      exact Veir.BlockPtr.allocEmptyAtAddress_fieldsInBounds hspec ctx.sim.fieldsInBounds
    · -- repr (spec only)
      exact hnewrepr
    · -- in_bounds
      intro ptr hib
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      rw [← hctxBuf]; clear hctxBuf
      simp only [Buffed.BlockMPtr.writeLastOp_range, Buffed.BlockMPtr.writeFirstOp_range,
        Buffed.BlockMPtr.writeParent_range, Buffed.BlockMPtr.writeNext_range,
        Buffed.BlockMPtr.writePrev_range, Buffed.BlockMPtr.writeFirstUse_range,
        Buffed.BlockMPtr.writeNumArguments_range]
      have hbufrange : buf.mem.range = 0...(ctx.buf.mem.size + (Buffed.BlockMPtr.computeBlockSize numArgs).toUInt64.toNat) := by
        simp only [Buffed.IRBufContext.alloc] at halloc
        split at halloc
        · simp only [Option.some.injEq] at halloc
          subst halloc
          simp only [ExArray.extend_range]
        · exact absurd halloc (by simp)
      rw [hbufrange]
      cases ptr with
      | operation op =>
        have holdib : op.InBounds ctx.spec := by
          have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.operation op) hspec).mp (by simpa using hib)
          grind
        have hin := ctx.sim.in_bounds (.operation op) (by simpa using holdib)
        have hrange : op.range ctxSpec = op.range ctx.spec :=
          (LayoutPreserved.same_operationPtr_range op holdib hlay).symm
        simp only [TopLevelPtr.range, IsIncludedIN, hrange] at hin ⊢
        grind
      | block bl =>
        rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block bl) hspec).mp (by simpa using hib)
          with hold | hnew | hfu
        · have holdib : bl.InBounds ctx.spec := by simpa using hold
          have hin := ctx.sim.in_bounds (.block bl) (by simpa using holdib)
          have hrange : bl.range ctxSpec = bl.range ctx.spec :=
            (LayoutPreserved.same_blockPtr_range bl holdib hlay).symm
          simp only [TopLevelPtr.range, IsIncludedIN, hrange] at hin ⊢
          grind
        · -- new block = ptrSpec at [usize, usize + Block.after) ⊆ [0, size + computeBlockSize).
          simp only [GenericPtr.block.injEq] at hnew
          subst bl
          have hnewib : ptrSpec.InBounds ctxSpec := by
            have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block ptrSpec) hspec).mpr
              (Or.inr (Or.inl rfl))
            simpa using this
          have hget : ptrSpec.get! ctxSpec = Block.empty numArgs.toNat := by
            have := BlockPtr.get!_BlockPtr_allocEmptyAtAddress (block := ptrSpec) hspec
            simpa using this
          have hcap : (ptrSpec.get! ctxSpec).capArguments = numArgs.toNat := by
            simp only [hget, Veir.Block.empty]
          have hargInt : (Buffed.Block.Offsets.argumentsInt : Int) = 56 := by decide
          have hbaseNat : Buffed.Block.sizeBaseNat = 56 := by decide
          have hszNat : Buffed.BlockArgument.sizeNat = 40 := by decide
          have hargNat : Buffed.Block.Sizes.argumentsNat ptrSpec ctxSpec = numArgs.toNat * 40 := by
            simp only [Buffed.Block.Sizes.argumentsNat, hcap, hszNat]
          have hafterInt : Buffed.Block.Offsets.afterInt ptrSpec ctxSpec
              = ((Buffed.BlockMPtr.computeBlockSize numArgs).toUInt64.toNat : Int) := by
            rw [hbsize, hbaseNat, hszNat,
              show Buffed.Block.Offsets.afterInt ptrSpec ctxSpec
                = (Buffed.Block.Offsets.argumentsInt : Int) + (Buffed.Block.Sizes.argumentsNat ptrSpec ctxSpec : Int)
                from rfl,
              hargInt, hargNat]
            omega
          have hupper : (ptrSpec.rangeInt ctxSpec).upper
              = (ctx.buf.mem.size : Int) + (Buffed.BlockMPtr.computeBlockSize numArgs).toUInt64.toNat := by
            simp only [Veir.BlockPtr.rangeInt, Veir.BlockPtr.toFlat, Buffed.Block.rangeInt,
              add_nat_range_def, hafterInt]
            simp only [hptr]
            omega
          have hlower : (ptrSpec.rangeInt ctxSpec).lower = (ctx.buf.mem.size : Int) := by
            simp only [Veir.BlockPtr.rangeInt, Veir.BlockPtr.toFlat, Buffed.Block.rangeInt,
              add_nat_range_def, hptr]
            omega
          have hrangeInt : ptrSpec.range ctxSpec = ptrSpec.rangeInt ctxSpec :=
            BlockPtr.range_ideal hnewrepr hnewib
          simp only [TopLevelPtr.range, hrangeInt, IsIncludedIN, hlower, hupper]
          refine ⟨by omega, by omega⟩
        · exact absurd hfu (by simp)
      | region rg =>
        have holdib : rg.InBounds ctx.spec := by
          have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.region rg) hspec).mp (by simpa using hib)
          grind
        have hin := ctx.sim.in_bounds (.region rg) (by simpa using holdib)
        simp only [TopLevelPtr.range, RegionPtr.range, RegionPtr.toFlat, IsIncludedIN] at hin ⊢
        grind
    · -- disjoint_allocs
      clear hctxBuf
      intro p1 p2 hib1 hib2 hne
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      simp only [IsDisjointI]
      rcases hmem p1 hib1 with ho1 | hn1 <;> rcases hmem p2 hib2 with ho2 | hn2
      · have hdis := ctx.sim.disjoint_allocs p1 p2 ho1 ho2 hne
        simp only [IsDisjointI, hrange p1 ho1, hrange p2 ho2] at hdis ⊢
        exact hdis
      · subst hn2
        have hu := hupper p1 ho1
        left
        simp only [TopLevelPtr.range] at hnewlow ⊢
        rw [hnewlow]
        exact_mod_cast hu
      · subst hn1
        have hu := hupper p2 ho2
        right
        simp only [TopLevelPtr.range] at hnewlow ⊢
        rw [hnewlow]
        exact_mod_cast hu
      · subst hn1; subst hn2
        exact absurd rfl hne
    · -- encoding_op: every op is old; frame each record over the untouched prefix.
      clear hctxBuf
      intro op opIb
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      have holdib : op.InBounds ctx.spec := by
        have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.operation op) hspec).mp (by simpa using opIb)
        grind
      have henc := ctx.sim.encoding_op op holdib
      have hrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op holdib
      have hget : Veir.OperationPtr.get! op ctxSpec = Veir.OperationPtr.get! op ctx.spec := by grind
      constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · refine OperationPtr.matchesBase_frame ctx op holdib henc.toMatchesBase
          (hagree.mono (Nat.zero_le _) (by grind)) hlay (by rw [hget]) (by rw [hget])
          (by rw [hget]) (by rw [hget]) (by grind [layout_grind]) (Veir.OperationPtr.getProperties!_eq_of_OperationPtr_get!_eq hget) opIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numBlockOperands_frame ctx op holdib henc.numBlockOperands
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
        · intro bo boIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hboIb : bo.InBounds ctx.spec := by
            have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.blockOperand bo) hspec).mp (by simpa using boIb)
            grind
          have hincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboIb
          have hpib := Veir.Sim.BlockOperandPtr.op_inBounds hboIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) bo.op hpib
          refine BlockOperandPtr.matches_frame ctx bo hboIb (henc.blockOperands bo hboIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlay (by grind) boIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numRegions_frame ctx op holdib henc.numRegions
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
        · intro idx idxIn
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hnr : idx < op.getNumRegions! ctx.spec := by grind
          have hcap := ctx.sim.repr.operations_indices op holdib |>.capRegions
          refine OperationPtr.nthRegion_frame ctx op holdib idx hnr (henc.regions idx hnr)
            (hagree.mono (Nat.zero_le _) (by grind)) ?_ (by grind)
          have hidxc : idx < (op.get! ctx.spec).capRegions := by grind
          have haddrR : (op.toM.toNat : Int) = op.id := by
            grind [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
          have hincl := OperationPtr.nthRegion_range_included_op_range ctx op idx.toUInt64 (by grind) holdib
          exact hagree.mono (Nat.zero_le _) (by grind [IsIncludedI, UInt64.toNat_ofNat'])
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numOperands_frame ctx op holdib henc.numOperands
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
        · intro oper operIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hooIb : oper.InBounds ctx.spec := by
            have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.opOperand oper) hspec).mp (by simpa using operIb)
            grind
          have hincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hooIb
          have hpib := Veir.Sim.OpOperandPtr.op_inBounds hooIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) oper.op hpib
          refine OpOperandPtr.matches_frame ctx oper hooIb (henc.operands oper hooIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlay (by grind) operIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numResults_frame ctx op holdib henc.numResults
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
        · intro res resIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hresIb : res.InBounds ctx.spec := by
            have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.opResult res) hspec).mp (by simpa using resIb)
            grind
          have hincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresIb
          have hpib := Veir.Sim.OpResultPtr.op_inBounds hresIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) res.op hpib
          refine OpResultPtr.matches_frame ctx res hresIb (henc.results res hresIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlay (by grind) resIb
    · -- encoding_block
      intro blk blkIb
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block blk) hspec).mp (by simpa using blkIb)
        with hold | hnew | hfu
      · -- Old block: frame the whole record over the untouched prefix.
        clear hctxBuf
        have holdib : blk.InBounds ctx.spec := by simpa using hold
        have henc := ctx.sim.encoding_block blk holdib
        have hrange := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk holdib
        have hget : Veir.BlockPtr.get! blk ctxSpec = Veir.BlockPtr.get! blk ctx.spec := by grind
        constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · refine BlockPtr.matchesBase_frame ctx blk holdib henc.toMatchesBase
            (hagree.mono (Nat.zero_le _) (by grind)) hlay (by rw [hget]) (by rw [hget])
            (by rw [hget]) (by rw [hget]) (by rw [hget]) (by rw [hget]) blkIb
        · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
          · exact BlockPtr.numArguments_frame ctx blk holdib henc.numArguments
              (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
          · intro arg argIn heq
            try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
            have hargIb : arg.InBounds ctx.spec := by
              have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.blockArgument arg) hspec).mp (by simpa using argIn)
              grind
            have hincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargIb
            have hpib := Veir.Sim.BlockArgumentPtr.block_inBounds hargIb
            have hprangeS := Veir.Sim.BlockPtr.range_linear (ctx := ctx) arg.block hpib
            refine BlockArgumentPtr.matches_frame ctx arg hargIb (henc.arguments arg hargIb heq)
              (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlay (by grind) argIn
      · -- New block = ptrSpec: all 7 fields read the fresh writes (each returning `none`/numArgs).
        simp only [GenericPtr.block.injEq] at hnew
        subst blk
        have hget : Veir.BlockPtr.get! ptrSpec ctxSpec = Block.empty numArgs.toNat := by
          have := BlockPtr.get!_BlockPtr_allocEmptyAtAddress (block := ptrSpec) hspec
          simpa using this
        have htoM : ptrSpec.toM = ctx.buf.usize := by
          simp only [hptr, BlockPtr.toM, BlockPtr.toFlat]; clear hctxBuf; grind
        have husz : ctx.buf.usize.toNat < 2 ^ 63 := by clear hctxBuf; grind
        have hmax : (Int64.maxValue.toInt : Int) = 2 ^ 63 - 1 := by decide
        have a0 : (ctx.buf.usize + Buffed.Block.Offsets.firstUse).toNat = ctx.buf.usize.toNat := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> (clear hctxBuf; grind)
        have a8 : (ctx.buf.usize + Buffed.Block.Offsets.prev).toNat = ctx.buf.usize.toNat + 8 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> (clear hctxBuf; grind)
        have a16 : (ctx.buf.usize + Buffed.Block.Offsets.next).toNat = ctx.buf.usize.toNat + 16 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> (clear hctxBuf; grind)
        have a24 : (ctx.buf.usize + Buffed.Block.Offsets.parent).toNat = ctx.buf.usize.toNat + 24 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> (clear hctxBuf; grind)
        have a32 : (ctx.buf.usize + Buffed.Block.Offsets.firstOp).toNat = ctx.buf.usize.toNat + 32 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> (clear hctxBuf; grind)
        have a40 : (ctx.buf.usize + Buffed.Block.Offsets.lastOp).toNat = ctx.buf.usize.toNat + 40 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> (clear hctxBuf; grind)
        have a48 : (ctx.buf.usize + Buffed.Block.Offsets.numArguments).toNat = ctx.buf.usize.toNat + 48 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> (clear hctxBuf; grind)
        constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · -- MatchesBase: firstUse/prev/next/parent/firstOp/lastOp all read `none`.
          constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
          · -- firstUse: read at usize+0, hits writeFirstUse.
            simp only [← hctxBuf, Sim.OptionBlockOperandPtr.Sim_def, Sim.OptionBlockOperandPtr.spec, Erased.out_mk, hget, Block.empty, Buffed.BlockMPtr.readFirstUse!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            simp [Veir.BlockOperandPtr.toO]
          · -- prev: read at usize+8, hits writePrev.
            simp only [← hctxBuf, Sim.OptionBlockPtr.Sim_def, Sim.OptionBlockPtr.spec, Erased.out_mk, hget, Block.empty, Buffed.BlockMPtr.readPrev!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            simp [Veir.BlockPtr.toO]
          · -- next: read at usize+16, hits writeNext.
            simp only [← hctxBuf, Sim.OptionBlockPtr.Sim_def, Sim.OptionBlockPtr.spec, Erased.out_mk, hget, Block.empty, Buffed.BlockMPtr.readNext!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            simp [Veir.BlockPtr.toO]
          · -- parent: read at usize+24, hits writeParent (a region pointer).
            simp only [← hctxBuf, Sim.OptionRegionPtr.Sim_def, Sim.OptionRegionPtr.spec, Erased.out_mk, hget, Block.empty, Buffed.BlockMPtr.readParent!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            simp [Veir.RegionPtr.toO]
          · -- firstOp: read at usize+32, hits writeFirstOp.
            simp only [← hctxBuf, Sim.OptionOperationPtr.Sim_def, Sim.OptionOperationPtr.spec, Erased.out_mk, hget, Block.empty, Buffed.BlockMPtr.readFirstOp!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            simp [Veir.OperationPtr.toO]
          · -- lastOp: read at usize+40, hits writeLastOp (outermost).
            simp only [← hctxBuf, Sim.OptionOperationPtr.Sim_def, Sim.OptionOperationPtr.spec, Erased.out_mk, hget, Block.empty, Buffed.BlockMPtr.readLastOp!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_self]
            simp [Veir.OperationPtr.toO]
        · -- MatchesArguments: numArguments reads numArgs; the arguments loop is vacuous (empty block).
          constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
          · -- numArguments: read at usize+48, hits writeNumArguments (innermost).
            simp only [← hctxBuf, hget, Block.empty, Buffed.BlockMPtr.readNumArguments!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
          · -- arguments loop: no in-bounds argument exists in an empty block.
            intro arg argIn heq
            try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
            exfalso
            have hold : arg.InBounds ctx.spec := by
              rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.blockArgument arg) hspec).mp
                (by simpa using argIn) with h | h | h
              · simpa using h
              · exact absurd h (by simp)
              · exact absurd h (by simp)
            rw [Veir.BlockArgumentPtr.inBounds_def] at hold
            obtain ⟨hbib, _⟩ := hold
            rw [heq] at hbib
            have hpeq : ptrSpec = (⟨ctx.buf.mem.size⟩ : Veir.BlockPtr) := by
              rw [hptr]; grind
            rw [hpeq] at hbib
            exact (Sim.BlockPtr.slot_free ctx) hbib
      · exact absurd hfu (by simp)
    · -- encoding_region: every region is old; frame the 24-byte record.
      clear hctxBuf
      intro rg rgIb
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      have holdib : rg.InBounds ctx.spec := by
        have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.region rg) hspec).mp (by simpa using rgIb)
        grind
      have henc := ctx.sim.encoding_region rg holdib
      have hrange := Veir.Sim.RegionPtr.range_linear (ctx := ctx) rg holdib
      refine RegionPtr.matches_frame ctx rg holdib henc
        (hagree.mono (Nat.zero_le _) (by grind)) hlay (by grind) rgIb
    · -- attr_empty
      rw [hattr]
      exact ctx.sim.attr_empty
    · rw [hfree]
      exact ctx.sim.free_valid.mono hsizele
    · intro size address hm p hp
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      rw [hfree] at hm
      rcases hmem p hp with hold | rfl
      · rw [hrange p hold]
        exact ctx.sim.free_disjoint size address hm p hold
      · have hb := (ctx.sim.free_valid.bounds size address hm).2
        right
        simp only [TopLevelPtr.range, hnewlow]
        exact_mod_cast hb


@[inline]
def Sim.BlockPtr.allocEmpty (ctx : Sim.IRContext OpInfo) (numArgs : UInt64) : Option (Sim.BlockPtr × Sim.IRContext OpInfo) :=
  -- `numArgs` bound needed by `allocEmptyImpl`.
  if hnumArgs : numArgs.toNat ≤ Buffed.countCard then
    match himpl : allocEmptyImpl ctx.buf numArgs hnumArgs with
    | none => none
    | some (ctxBuf, ptrImpl) =>
      let specRes := ctx.spec'.map (fun spec => (Veir.BlockPtr.allocEmptyAtAddress spec numArgs.toNat ptrImpl.toNat).get!)
      have hspec : Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptrImpl.toNat = some specRes.out := by
        have hptr : ptrImpl = ctx.buf.usize := by
          simp only [allocEmptyImpl] at himpl
          split at himpl <;> grind
        have hfree := Sim.BlockPtr.slot_free ctx
        simp only [Veir.BlockPtr.inBounds_def] at hfree
        have husz := ctx.buf.usize_toNat
        have hs := ctx.buf.size_def
        have hsome := Veir.BlockPtr.allocEmptyAtAddress_isSome_of_not_mem
          (ctx := ctx.spec) (capArguments := numArgs.toNat) (address := ptrImpl.toNat) (by grind)
        simpa only [specRes, Erased.map_out, Option.get!] using (Option.some_get! _ hsome).symm
      some ⟨⟨ptrImpl, specRes.map Prod.snd⟩, ⟨ctxBuf, specRes.map Prod.fst, by
        simpa only [Erased.map_eq_mk] using allocEmpty_sim ctx numArgs hnumArgs himpl hspec⟩⟩
  else
    none

/-- Strengthening of `allocEmpty_spec`: the spec-level block is allocated exactly at the address of the returned impl pointer. -/
theorem Sim.BlockPtr.allocEmpty_spec' {ctx : Sim.IRContext OpInfo} numArgs :
    allocEmpty ctx numArgs = some ⟨ptr, ctx'⟩ →
    Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptr.impl.toNat = some ⟨ctx'.spec, ptr.spec⟩ := by
  intro h
  simp only [allocEmpty] at h
  split at h
  · rename_i hnumArgs
    split at h
    · exact absurd h (by simp)
    · rename_i ctxBuf ptrImpl himpl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
      have hptr : ptrImpl = ctx.buf.usize := by
        simp only [allocEmptyImpl] at himpl
        split at himpl <;> grind
      have hfree := Sim.BlockPtr.slot_free ctx
      simp only [Veir.BlockPtr.inBounds_def] at hfree
      have husz := ctx.buf.usize_toNat
      have hs := ctx.buf.size_def
      have hsome := Veir.BlockPtr.allocEmptyAtAddress_isSome_of_not_mem
        (ctx := ctx.spec) (capArguments := numArgs.toNat) (address := ptrImpl.toNat) (by grind)
      rw [← Option.some_get! _ hsome]
      simp [Sim.IRContext.spec, Sim.BlockPtr.spec]
  · exact absurd h (by simp)

@[grind! .]
theorem Sim.BlockPtr.allocEmpty_spec {ctx : Sim.IRContext OpInfo} numArgs :
    allocEmpty ctx numArgs = some ⟨ptr, ctx'⟩ →
    ∃ addr, Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat addr = some ⟨ctx'.spec, ptr.spec⟩:=
  fun h => ⟨ptr.impl.toNat, Sim.BlockPtr.allocEmpty_spec' numArgs h⟩

@[inline]
def Sim.BlockPtr.setParent (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec, parent.spec)).map (fun (ptr, ctx, value) => ptr.setParent! ctx value), by
    prove_setLinkSim ctx bl Buffed.BlockMPtr.writeParent blockMPtr_writeParent BlockPtr_setParent
      (ptr.spec.setParent ctx.spec parent.spec (by grind)) parentIb⟩

open Classical in
noncomputable def Sim.BlockPtr.setParent! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.parent).toInt + Buffed.Block.Sizes.parent.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeParent ctx.buf ptr.impl parent.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, parent.spec)).map (fun (ptr, ctx, value) => ptr.setParent! ctx value) } then
    ⟨ptr.impl.writeParent ctx.buf parent.impl h₁, (Erased.mk (ptr.spec, ctx.spec, parent.spec)).map (fun (ptr, ctx, value) => ptr.setParent! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setParent_eq_setParent! (ctx : IRContext OpInfo) ptr parent ib parentIb :
    setParent ctx ptr parent ib parentIb = setParent! ctx ptr parent := by
  simp [setParent, setParent!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent ctx ptr parent ib parentIb).spec = ptr.spec.setParent ctx.spec parent.spec := by
  grind [setParent]

@[simp, grind =]
theorem Sim.BlockPtr.setParent!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent! ctx ptr parent).spec = ptr.spec.setParent! ctx.spec parent.spec := by
  grind

@[inline]
def Sim.BlockPtr.getParent (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionRegionPtr :=
  ⟨ptr.impl.readParent ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).parent)⟩

@[simp, grind =]
theorem Sim.BlockPtr.getParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).spec = (ptr.spec.get ctx.spec).parent := by
  grind [getParent]

@[grind .]
theorem Sim.BlockPtr.getParent_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).parent
  grind [getParent]

@[inline]
def Sim.BlockPtr.getParent! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionRegionPtr :=
  ⟨ptr.impl.readParent! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).parent)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getParent_eq_getParent! (ctx : IRContext OpInfo) ptr ib :
    getParent ctx ptr ib = getParent! ctx ptr := by
  simp [getParent, getParent!] <;> grind

@[inline]
def Sim.BlockPtr.setFirstUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value), by
    prove_setLinkSim ctx bl Buffed.BlockMPtr.writeFirstUse blockMPtr_writeFirstUse BlockPtr_setFirstUse
      (ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind)) firstUseIb⟩

open Classical in
noncomputable def Sim.BlockPtr.setFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.firstUse).toInt + Buffed.Block.Sizes.firstUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeFirstUse ctx.buf ptr.impl firstUse.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value) } then
    ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl h₁, (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse, setFirstUse!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  grind [setFirstUse]

@[simp, grind =]
theorem Sim.BlockPtr.setFirstUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse! ctx ptr firstUse).spec = ptr.spec.setFirstUse! ctx.spec firstUse.spec := by
  grind

@[inline]
def Sim.BlockPtr.getFirstUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstUse)⟩

@[simp, grind =]
theorem Sim.BlockPtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstUse := by
  grind [getFirstUse]

@[grind .]
theorem Sim.BlockPtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).firstUse
  grind [getFirstUse]

@[inline]
def Sim.BlockPtr.getFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstUse)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse, getFirstUse!] <;> grind

@[inline]
def Sim.BlockPtr.setFirstOp (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (firstOpIb : firstOp.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstOp ctx.buf firstOp.impl (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec, firstOp.spec)).map (fun (ptr, ctx, value) => ptr.setFirstOp! ctx value), by
    prove_setLinkSim ctx bl Buffed.BlockMPtr.writeFirstOp blockMPtr_writeFirstOp BlockPtr_setFirstOp
      (ptr.spec.setFirstOp ctx.spec firstOp.spec (by grind)) firstOpIb⟩

open Classical in
noncomputable def Sim.BlockPtr.setFirstOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.firstOp).toInt + Buffed.Block.Sizes.firstOp.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeFirstOp ctx.buf ptr.impl firstOp.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, firstOp.spec)).map (fun (ptr, ctx, value) => ptr.setFirstOp! ctx value) } then
    ⟨ptr.impl.writeFirstOp ctx.buf firstOp.impl h₁, (Erased.mk (ptr.spec, ctx.spec, firstOp.spec)).map (fun (ptr, ctx, value) => ptr.setFirstOp! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setFirstOp_eq_setFirstOp! (ctx : IRContext OpInfo) ptr firstOp ib firstOpIb :
    setFirstOp ctx ptr firstOp ib firstOpIb = setFirstOp! ctx ptr firstOp := by
  simp [setFirstOp, setFirstOp!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setFirstOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (firstOpIb : firstOp.InBounds ctx) :
    (setFirstOp ctx ptr firstOp ib firstOpIb).spec = ptr.spec.setFirstOp ctx.spec firstOp.spec := by
  grind [setFirstOp]

@[simp, grind =]
theorem Sim.BlockPtr.setFirstOp!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (firstOpIb : firstOp.InBounds ctx) :
    (setFirstOp! ctx ptr firstOp).spec = ptr.spec.setFirstOp! ctx.spec firstOp.spec := by
  grind

@[inline]
def Sim.BlockPtr.getFirstOp (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readFirstOp ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstOp)⟩

@[simp, grind =]
theorem Sim.BlockPtr.getFirstOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstOp := by
  grind [getFirstOp]

@[grind .]
theorem Sim.BlockPtr.getFirstOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).firstOp
  grind [getFirstOp]

@[inline]
def Sim.BlockPtr.getFirstOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readFirstOp! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstOp)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getFirstOp_eq_getFirstOp! (ctx : IRContext OpInfo) ptr ib :
    getFirstOp ctx ptr ib = getFirstOp! ctx ptr := by
  simp [getFirstOp, getFirstOp!] <;> grind

@[inline]
def Sim.BlockPtr.setLastOp (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (lastOpIb : lastOp.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeLastOp ctx.buf lastOp.impl (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec, lastOp.spec)).map (fun (ptr, ctx, value) => ptr.setLastOp! ctx value), by
    prove_setLinkSim ctx bl Buffed.BlockMPtr.writeLastOp blockMPtr_writeLastOp BlockPtr_setLastOp
      (ptr.spec.setLastOp ctx.spec lastOp.spec (by grind)) lastOpIb⟩

open Classical in
noncomputable def Sim.BlockPtr.setLastOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.lastOp).toInt + Buffed.Block.Sizes.lastOp.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeLastOp ctx.buf ptr.impl lastOp.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, lastOp.spec)).map (fun (ptr, ctx, value) => ptr.setLastOp! ctx value) } then
    ⟨ptr.impl.writeLastOp ctx.buf lastOp.impl h₁, (Erased.mk (ptr.spec, ctx.spec, lastOp.spec)).map (fun (ptr, ctx, value) => ptr.setLastOp! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setLastOp_eq_setLastOp! (ctx : IRContext OpInfo) ptr lastOp ib lastOpIb :
    setLastOp ctx ptr lastOp ib lastOpIb = setLastOp! ctx ptr lastOp := by
  simp [setLastOp, setLastOp!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setLastOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (lastOpIb : lastOp.InBounds ctx) :
    (setLastOp ctx ptr lastOp ib lastOpIb).spec = ptr.spec.setLastOp ctx.spec lastOp.spec := by
  grind [setLastOp]

@[simp, grind =]
theorem Sim.BlockPtr.setLastOp!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (lastOpIb : lastOp.InBounds ctx) :
    (setLastOp! ctx ptr lastOp).spec = ptr.spec.setLastOp! ctx.spec lastOp.spec := by
  grind

@[inline]
def Sim.BlockPtr.getLastOp (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readLastOp ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).lastOp)⟩

@[simp, grind =]
theorem Sim.BlockPtr.getLastOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getLastOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).lastOp := by
  grind [getLastOp]

@[grind .]
theorem Sim.BlockPtr.getLastOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getLastOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).lastOp
  grind [getLastOp]

@[inline]
def Sim.BlockPtr.getLastOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readLastOp! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).lastOp)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getLastOp_eq_getLastOp! (ctx : IRContext OpInfo) ptr ib :
    getLastOp ctx ptr ib = getLastOp! ctx ptr := by
  simp [getLastOp, getLastOp!] <;> grind

@[inline]
def Sim.BlockPtr.setNextBlock (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNext ctx.buf next.impl (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec, next.spec)).map (fun (ptr, ctx, value) => ptr.setNextBlock! ctx value), by
    prove_setLinkSim ctx bl Buffed.BlockMPtr.writeNext blockMPtr_writeNext BlockPtr_setNextBlock
      (ptr.spec.setNextBlock ctx.spec next.spec (by grind)) nextIb⟩

open Classical in
noncomputable def Sim.BlockPtr.setNextBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.next).toInt + Buffed.Block.Sizes.next.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeNext ctx.buf ptr.impl next.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, next.spec)).map (fun (ptr, ctx, value) => ptr.setNextBlock! ctx value) } then
    ⟨ptr.impl.writeNext ctx.buf next.impl h₁, (Erased.mk (ptr.spec, ctx.spec, next.spec)).map (fun (ptr, ctx, value) => ptr.setNextBlock! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setNextBlock_eq_setNextBlock! (ctx : IRContext OpInfo) ptr next ib nextIb :
    setNextBlock ctx ptr next ib nextIb = setNextBlock! ctx ptr next := by
  simp [setNextBlock, setNextBlock!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setNextBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextBlock ctx ptr next ib nextIb).spec = ptr.spec.setNextBlock ctx.spec next.spec := by
  grind [setNextBlock]

@[simp, grind =]
theorem Sim.BlockPtr.setNextBlock!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextBlock! ctx ptr next).spec = ptr.spec.setNextBlock! ctx.spec next.spec := by
  grind

@[inline]
def Sim.BlockPtr.getNextBlock (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readNext ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).next)⟩

@[simp, grind =]
theorem Sim.BlockPtr.getNextBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getNextBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).next := by
  grind [getNextBlock]

@[grind .]
theorem Sim.BlockPtr.getNextBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getNextBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).next
  grind [getNextBlock]

@[inline]
def Sim.BlockPtr.getNextBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readNext! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).next)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getNextBlock_eq_getNextBlock! (ctx : IRContext OpInfo) ptr ib :
    getNextBlock ctx ptr ib = getNextBlock! ctx ptr := by
  simp [getNextBlock, getNextBlock!] <;> grind

@[inline]
def Sim.BlockPtr.setPrevBlock (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writePrev ctx.buf prev.impl (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec, prev.spec)).map (fun (ptr, ctx, value) => ptr.setPrevBlock! ctx value), by
    prove_setLinkSim ctx bl Buffed.BlockMPtr.writePrev blockMPtr_writePrev BlockPtr_setPrevBlock
      (ptr.spec.setPrevBlock ctx.spec prev.spec (by grind)) prevIb⟩

open Classical in
noncomputable def Sim.BlockPtr.setPrevBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.prev).toInt + Buffed.Block.Sizes.prev.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writePrev ctx.buf ptr.impl prev.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, prev.spec)).map (fun (ptr, ctx, value) => ptr.setPrevBlock! ctx value) } then
    ⟨ptr.impl.writePrev ctx.buf prev.impl h₁, (Erased.mk (ptr.spec, ctx.spec, prev.spec)).map (fun (ptr, ctx, value) => ptr.setPrevBlock! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setPrevBlock_eq_setPrevBlock! (ctx : IRContext OpInfo) ptr prev ib prevIb :
    setPrevBlock ctx ptr prev ib prevIb = setPrevBlock! ctx ptr prev := by
  simp [setPrevBlock, setPrevBlock!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setPrevBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevBlock ctx ptr prev ib prevIb).spec = ptr.spec.setPrevBlock ctx.spec prev.spec := by
  grind [setPrevBlock]

@[simp, grind =]
theorem Sim.BlockPtr.setPrevBlock!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevBlock! ctx ptr prev).spec = ptr.spec.setPrevBlock! ctx.spec prev.spec := by
  grind

@[inline]
def Sim.BlockPtr.getPrevBlock (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readPrev ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).prev)⟩

@[simp, grind =]
theorem Sim.BlockPtr.getPrevBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).prev := by
  grind [getPrevBlock]

@[grind .]
theorem Sim.BlockPtr.getPrevBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).prev
  grind [getPrevBlock]

@[inline]
def Sim.BlockPtr.getPrevBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readPrev! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).prev)⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getPrevBlock_eq_getPrevBlock! (ctx : IRContext OpInfo) ptr ib :
    getPrevBlock ctx ptr ib = getPrevBlock! ctx ptr := by
  simp [getPrevBlock, getPrevBlock!] <;> grind

@[inline]
def Sim.BlockPtr.getNumArguments (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumArguments ctx.buf (by prove_setLinkBoundsBlock ctx ptr)

@[inline]
def Sim.BlockPtr.getNumArguments! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : UInt64 :=
  ptr.impl.readNumArguments! ctx.buf

@[simp, grind =]
theorem Sim.BlockPtr.getNumArguments_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getNumArguments ctx ptr ib).toNat = (ptr.spec.get! ctx.spec).capArguments := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).numArguments
  grind [getNumArguments]

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getNumArguments_eq_getNumArguments! (ctx : IRContext OpInfo) ptr ib :
    getNumArguments ctx ptr ib = getNumArguments! ctx ptr := by
  simp [getNumArguments, getNumArguments!]

@[inline]
def Sim.BlockPtr.getArgumentPtr (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.BlockArgumentPtr :=
  ⟨ptr.impl + Buffed.BlockMPtr.computeArgumentOffset index,
   ptr.spec'.map (·.getArgument index.toNat)⟩

@[inline]
def Sim.BlockPtr.getArgumentPtr! (_ctx : IRContext OpInfo) (ptr : Sim.BlockPtr)
    (index : UInt64) : Sim.BlockArgumentPtr :=
  ⟨ptr.impl + Buffed.BlockMPtr.computeArgumentOffset! index,
   ptr.spec'.map (·.getArgument index.toNat)⟩

@[simp, grind =]
theorem Sim.BlockPtr.getArgumentPtr_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (index : UInt64) (ib : ptr.InBounds ctx) :
    (getArgumentPtr ctx ptr index ib).spec = ptr.spec.getArgument index.toNat := by
  grind [getArgumentPtr]

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getArgumentPtr_eq_getArgumentPtr! (ctx : IRContext OpInfo) ptr index ib :
    getArgumentPtr ctx ptr index ib = getArgumentPtr! ctx ptr index := by
  simp [getArgumentPtr, getArgumentPtr!]

@[inline]
def Sim.RegionPtr.setParent (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl (by prove_setLinkBoundsRegion ctx ptr), (Erased.mk (ptr.spec, ctx.spec, parent.spec)).map (fun (ptr, ctx, value) => ptr.setParent! ctx value), by
    prove_setLinkSim ctx rg Buffed.RegionMPtr.writeParent regionMPtr_writeParent RegionPtr_setParent
      (ptr.spec.setParent ctx.spec parent.spec (by grind)) parentIb⟩

open Classical in
noncomputable def Sim.RegionPtr.setParent! (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Region.Offsets.parent).toInt + Buffed.Region.Sizes.parent.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.RegionMPtr.writeParent ctx.buf ptr.impl parent.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, parent.spec)).map (fun (ptr, ctx, value) => ptr.setParent! ctx value) } then
    ⟨ptr.impl.writeParent ctx.buf parent.impl h₁, (Erased.mk (ptr.spec, ctx.spec, parent.spec)).map (fun (ptr, ctx, value) => ptr.setParent! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.setParent_eq_setParent! (ctx : IRContext OpInfo) ptr parent ib parentIb :
    setParent ctx ptr parent ib parentIb = setParent! ctx ptr parent := by
  simp [setParent, setParent!]
  split
  · grind
  · prove_setLinkBoundsRegion ctx ptr

@[simp, grind =]
theorem Sim.RegionPtr.setParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent ctx ptr parent ib parentIb).spec = ptr.spec.setParent ctx.spec parent.spec := by
  grind [setParent]

@[simp, grind =]
theorem Sim.RegionPtr.setParent!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent! ctx ptr parent).spec = ptr.spec.setParent! ctx.spec parent.spec := by
  grind

@[inline]
def Sim.RegionPtr.getParent (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readParent ctx.buf (by prove_setLinkBoundsRegion ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).parent)⟩

@[simp, grind =]
theorem Sim.RegionPtr.getParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).spec = (ptr.spec.get ctx.spec).parent := by
  grind [getParent]

@[grind .]
theorem Sim.RegionPtr.getParent_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_region ptr.spec (by grind)).parent
  grind [getParent]

@[inline]
def Sim.RegionPtr.getParent! (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readParent! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).parent)⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.getParent_eq_getParent! (ctx : IRContext OpInfo) ptr ib :
    getParent ctx ptr ib = getParent! ctx ptr := by
  simp [getParent, getParent!] <;> grind

@[inline]
def Sim.RegionPtr.setFirstBlock (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (firstBlockIb : firstBlock.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstBlock ctx.buf firstBlock.impl (by prove_setLinkBoundsRegion ctx ptr), (Erased.mk (ptr.spec, ctx.spec, firstBlock.spec)).map (fun (ptr, ctx, value) => ptr.setFirstBlock! ctx value), by
    prove_setLinkSim ctx rg Buffed.RegionMPtr.writeFirstBlock regionMPtr_writeFirstBlock RegionPtr_setFirstBlock
      (ptr.spec.setFirstBlock ctx.spec firstBlock.spec (by grind)) firstBlockIb⟩

open Classical in
noncomputable def Sim.RegionPtr.setFirstBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Region.Offsets.firstBlock).toInt + Buffed.Region.Sizes.firstBlock.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.RegionMPtr.writeFirstBlock ctx.buf ptr.impl firstBlock.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, firstBlock.spec)).map (fun (ptr, ctx, value) => ptr.setFirstBlock! ctx value) } then
    ⟨ptr.impl.writeFirstBlock ctx.buf firstBlock.impl h₁, (Erased.mk (ptr.spec, ctx.spec, firstBlock.spec)).map (fun (ptr, ctx, value) => ptr.setFirstBlock! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.setFirstBlock_eq_setFirstBlock! (ctx : IRContext OpInfo) ptr firstBlock ib firstBlockIb :
    setFirstBlock ctx ptr firstBlock ib firstBlockIb = setFirstBlock! ctx ptr firstBlock := by
  simp [setFirstBlock, setFirstBlock!]
  split
  · grind
  · prove_setLinkBoundsRegion ctx ptr

@[simp, grind =]
theorem Sim.RegionPtr.setFirstBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (firstBlockIb : firstBlock.InBounds ctx) :
    (setFirstBlock ctx ptr firstBlock ib firstBlockIb).spec = ptr.spec.setFirstBlock ctx.spec firstBlock.spec := by
  grind [setFirstBlock]

@[simp, grind =]
theorem Sim.RegionPtr.setFirstBlock!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (firstBlockIb : firstBlock.InBounds ctx) :
    (setFirstBlock! ctx ptr firstBlock).spec = ptr.spec.setFirstBlock! ctx.spec firstBlock.spec := by
  grind

@[inline]
def Sim.RegionPtr.getFirstBlock (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readFirstBlock ctx.buf (by prove_setLinkBoundsRegion ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstBlock)⟩

@[simp, grind =]
theorem Sim.RegionPtr.getFirstBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstBlock := by
  grind [getFirstBlock]

@[grind .]
theorem Sim.RegionPtr.getFirstBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_region ptr.spec (by grind)).firstBlock
  grind [getFirstBlock]

@[inline]
def Sim.RegionPtr.getFirstBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readFirstBlock! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).firstBlock)⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.getFirstBlock_eq_getFirstBlock! (ctx : IRContext OpInfo) ptr ib :
    getFirstBlock ctx ptr ib = getFirstBlock! ctx ptr := by
  simp [getFirstBlock, getFirstBlock!] <;> grind

@[inline]
def Sim.RegionPtr.setLastBlock (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (lastBlockIb : lastBlock.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeLastBlock ctx.buf lastBlock.impl (by prove_setLinkBoundsRegion ctx ptr), (Erased.mk (ptr.spec, ctx.spec, lastBlock.spec)).map (fun (ptr, ctx, value) => ptr.setLastBlock! ctx value), by
    prove_setLinkSim ctx rg Buffed.RegionMPtr.writeLastBlock regionMPtr_writeLastBlock RegionPtr_setLastBlock
      (ptr.spec.setLastBlock ctx.spec lastBlock.spec (by grind)) lastBlockIb⟩

open Classical in
noncomputable def Sim.RegionPtr.setLastBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Region.Offsets.lastBlock).toInt + Buffed.Region.Sizes.lastBlock.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.RegionMPtr.writeLastBlock ctx.buf ptr.impl lastBlock.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, lastBlock.spec)).map (fun (ptr, ctx, value) => ptr.setLastBlock! ctx value) } then
    ⟨ptr.impl.writeLastBlock ctx.buf lastBlock.impl h₁, (Erased.mk (ptr.spec, ctx.spec, lastBlock.spec)).map (fun (ptr, ctx, value) => ptr.setLastBlock! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.setLastBlock_eq_setLastBlock! (ctx : IRContext OpInfo) ptr lastBlock ib lastBlockIb :
    setLastBlock ctx ptr lastBlock ib lastBlockIb = setLastBlock! ctx ptr lastBlock := by
  simp [setLastBlock, setLastBlock!]
  split
  · grind
  · prove_setLinkBoundsRegion ctx ptr

@[simp, grind =]
theorem Sim.RegionPtr.setLastBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (lastBlockIb : lastBlock.InBounds ctx) :
    (setLastBlock ctx ptr lastBlock ib lastBlockIb).spec = ptr.spec.setLastBlock ctx.spec lastBlock.spec := by
  grind [setLastBlock]

@[simp, grind =]
theorem Sim.RegionPtr.setLastBlock!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (lastBlockIb : lastBlock.InBounds ctx) :
    (setLastBlock! ctx ptr lastBlock).spec = ptr.spec.setLastBlock! ctx.spec lastBlock.spec := by
  grind

@[inline]
def Sim.RegionPtr.getLastBlock (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readLastBlock ctx.buf (by prove_setLinkBoundsRegion ctx ptr), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).lastBlock)⟩

@[simp, grind =]
theorem Sim.RegionPtr.getLastBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getLastBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).lastBlock := by
  grind [getLastBlock]

@[grind .]
theorem Sim.RegionPtr.getLastBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getLastBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_region ptr.spec (by grind)).lastBlock
  grind [getLastBlock]

@[inline]
def Sim.RegionPtr.getLastBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readLastBlock! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => (ptr.get! ctx).lastBlock)⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.getLastBlock_eq_getLastBlock! (ctx : IRContext OpInfo) ptr ib :
    getLastBlock ctx ptr ib = getLastBlock! ctx ptr := by
  simp [getLastBlock, getLastBlock!] <;> grind

@[inline]
def Sim.ValuePtr.setFirstUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl (by prove_setLinkBoundsValue), (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value), by
    prove_setLinkSim ctx vi Buffed.ValueImplMPtr.writeFirstUse valueImplMPtr_writeFirstUse ValuePtr_setFirstUse
      (ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind)) firstUseIb⟩

open Classical in
noncomputable def Sim.ValuePtr.setFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.ValueImpl.Offsets.firstUse).toInt + Buffed.ValueImpl.Sizes.firstUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl firstUse.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value) } then
    ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl h₁, (Erased.mk (ptr.spec, ctx.spec, firstUse.spec)).map (fun (ptr, ctx, value) => ptr.setFirstUse! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.ValuePtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse, setFirstUse!]
  split
  · grind
  · prove_setLinkBoundsValue

@[simp, grind =]
theorem Sim.ValuePtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  grind [setFirstUse]

@[simp, grind =]
theorem Sim.ValuePtr.setFirstUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse! ctx ptr firstUse).spec = ptr.spec.setFirstUse! ctx.spec firstUse.spec := by
  grind

@[inline]
def Sim.ValuePtr.getFirstUse (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf (by prove_setLinkBoundsValue), (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => ptr.getFirstUse! ctx)⟩

@[simp, grind =]
theorem Sim.ValuePtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = ptr.spec.getFirstUse ctx.spec (by grind) := by
  grind [getFirstUse]

@[grind .]
theorem Sim.ValuePtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  cases heq : ptr.spec
  case opResult res =>
    have := ctx.sim.encoding_op res.op (by grind [Veir.OpResultPtr.inBounds_def])
      |>.results res (by grind) (by grind) |>.firstUse
    simp_all [getFirstUse, eq_bang]
    unfold Buffed.OpResultMPtr.readFirstUse! at this
    unfold Buffed.ValueImplMPtr.readFirstUse!
    grind
  case blockArgument arg =>
    have := ctx.sim.encoding_block arg.block (by grind [Veir.BlockArgumentPtr.inBounds_def])
      |>.arguments arg (by grind) (by grind) |>.firstUse
    simp_all [getFirstUse, eq_bang]
    unfold Buffed.BlockArgumentMPtr.readFirstUse! at this
    unfold Buffed.ValueImplMPtr.readFirstUse!
    grind

@[inline]
def Sim.ValuePtr.getFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => ptr.getFirstUse! ctx)⟩

@[eq_bang, grind _=_]
theorem Sim.ValuePtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse, getFirstUse!] <;> grind

@[inline]
def Sim.OpOperandPtrPtr.set (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtrPtr)
    (value : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.write ctx.buf value.impl (by
    have : ctx.buf.mem.size < 2^63 := by grind
    have := Sim.OpOperandPtrPtr.after_lt_ctx (ctx := ctx) ptr.spec (by grind)
    grind [layout_grind]),
   (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.set! ctx value), by
    prove_setLinkSim ctx oopp Buffed.OpOperandPtrMPtr.write opOperandPtrMPtr_write OpOperandPtrPtr_set
      (ptr.spec.set ctx.spec value.spec (by grind)) valueIb⟩

open Classical in
noncomputable def Sim.OpOperandPtrPtr.set! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtrPtr)
    (value : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : ptr.impl.toNat + Buffed.ptrSize.toNat ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl value.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.set! ctx value) } then
    ⟨ptr.impl.write ctx.buf value.impl h₁, (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.set! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtrPtr.set_eq_set! (ctx : IRContext OpInfo) ptr value ib valueIb :
    set ctx ptr value ib valueIb = set! ctx ptr value := by
  simp [set, set!]
  split
  · grind
  · have : ctx.buf.mem.size < 2^63 := by grind
    have := Sim.OpOperandPtrPtr.after_lt_ctx (ctx := ctx) ptr.spec (by grind)
    grind [layout_grind]

@[simp, grind =]
theorem Sim.OpOperandPtrPtr.set_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtrPtr)
    (value : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (set ctx ptr value ib valueIb).spec = ptr.spec.set ctx.spec value.spec := by
  grind [set]

@[inline]
def Sim.BlockOperandPtrPtr.set (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr)
    (value : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.write ctx.buf value.impl (by
    have : ctx.buf.mem.size < 2^63 := by grind
    have := Sim.BlockOperandPtrPtr.after_lt_ctx (ctx := ctx) ptr.spec (by grind)
    grind [layout_grind]),
   (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.set! ctx value), by
    prove_setLinkSim ctx bopp Buffed.BlockOperandPtrMPtr.write blockOperandPtrMPtr_write BlockOperandPtrPtr_set
      (ptr.spec.set ctx.spec value.spec (by grind)) valueIb⟩

open Classical in
noncomputable def Sim.BlockOperandPtrPtr.set! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr)
    (value : Sim.OptionBlockOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : ptr.impl.toNat + Buffed.ptrSize.toNat ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl value.impl h₁,
      spec' := (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.set! ctx value) } then
    ⟨ptr.impl.write ctx.buf value.impl h₁, (Erased.mk (ptr.spec, ctx.spec, value.spec)).map (fun (ptr, ctx, value) => ptr.set! ctx value), h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtrPtr.set_eq_set! (ctx : IRContext OpInfo) ptr value ib valueIb :
    set ctx ptr value ib valueIb = set! ctx ptr value := by
  simp [set, set!]
  split
  · grind
  · have : ctx.buf.mem.size < 2^63 := by grind
    have := Sim.BlockOperandPtrPtr.after_lt_ctx (ctx := ctx) ptr.spec (by grind)
    grind [layout_grind]

@[simp, grind =]
theorem Sim.BlockOperandPtrPtr.set_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr)
    (value : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (set ctx ptr value ib valueIb).spec = ptr.spec.set ctx.spec value.spec := by
  grind [set]

/-! Allocation of empty regions and operations. -/

@[inline]
def Sim.RegionPtr.allocEmptyImpl (ctx₀ : Buffed.IRBufContext) : Option (Buffed.IRBufContext × Buffed.RegionMPtr) :=
  let size := Buffed.Region.size
  let ptr : Buffed.RegionMPtr := ctx₀.usize
  rlet halloc : ctx ← ctx₀.alloc size
  have hsize : ctx.size = ctx₀.size + size.toNat := ctx₀.alloc_size halloc
  let ctx := ptr.writeParent ctx .none (by prove_allocBounds ctx₀)
  let ctx := ptr.writeFirstBlock ctx .none (by prove_allocBounds ctx₀)
  let ctx := ptr.writeLastBlock ctx .none (by prove_allocBounds ctx₀)
  some (ctx, ptr)

theorem Sim.RegionPtr.allocEmptyImpl_freeList {ctx₀ ctxBuf : Buffed.IRBufContext}
    {ptr : UInt64}
    (h : allocEmptyImpl ctx₀ = some (ctxBuf, ptr)) :
    ctxBuf.freeList = ctx₀.freeList := by
  simp only [allocEmptyImpl] at h
  split at h
  · contradiction
  · rename_i buf halloc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Buffed.IRBufContext.alloc_freeList (bctx' := buf) halloc

def Sim.RegionPtr.allocEmptySpec (ctx : Veir.IRContext OpInfo) (addr : UInt64) : Option (Veir.IRContext OpInfo × Veir.RegionPtr) :=
  RegionPtr.allocEmptyAt ctx addr.toNat

/-- The address at the end of the buffer is free in the spec: a region there would have its range escape the buffer, contradicting `in_bounds`. -/
theorem Sim.RegionPtr.slot_free (ctx : Sim.IRContext OpInfo) :
    ¬ (⟨ctx.buf.mem.size⟩ : Veir.RegionPtr).InBounds ctx.spec := by
  intro hin
  have := ctx.sim.in_bounds (.region ⟨ctx.buf.mem.size⟩) (by grind)
  simp only [TopLevelPtr.range, Veir.RegionPtr.range, Veir.RegionPtr.toFlat, IsIncludedIN] at this
  grind

set_option maxHeartbeats 4000000 in
/-- The `Sim` relation survives an empty-region allocation: given that `allocEmptyImpl` produced `ctxBuf`/`ptrImpl` and the spec allocated the matching region at `ptrImpl.toNat`, the resulting buffer and spec still simulate each other. -/
theorem Sim.RegionPtr.allocEmpty_sim (ctx : Sim.IRContext OpInfo)
    {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.RegionMPtr}
    (heq : Sim.RegionPtr.allocEmptyImpl ctx.buf = some (ctxBuf, ptrImpl))
    {ctxSpec : Veir.IRContext OpInfo} {ptrSpec : Veir.RegionPtr}
    (hspec : Veir.RegionPtr.allocEmptyAt ctx.spec ptrImpl.toNat = some (ctxSpec, ptrSpec)) :
    Veir.Sim (OpInfo := OpInfo) ⟨ctxBuf, .mk ctxSpec⟩ := by
  have hfree := Sim.RegionPtr.allocEmptyImpl_freeList heq
  simp only [Sim.RegionPtr.allocEmptyImpl] at heq
  split at heq
  · exact absurd heq (by simp)
  · rename_i buf halloc
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hu := ctx.buf.usize_toNat
    have hs := ctx.buf.size_def
    have hgrow := ctx.buf.alloc_size halloc
    have hfits := buf.mem.fits_in_memory
    have hsize : ctx.buf.mem.size < 2 ^ 63 := by
      simp only [Buffed.IRBufContext.size_def, Int64.maxNatValue] at *; omega
    have hptr := Veir.RegionPtr.allocEmptyAt_ptr hspec
    have hlay := (Veir.RegionPtr.allocEmptyAt_preservesLayout hspec).preserves
    have hread : ∀ (w : Nat) (a len : UInt64), a.toNat + len.toNat ≤ ctx.buf.mem.size →
        (Buffed.RegionMPtr.writeLastBlock
          (Buffed.RegionMPtr.writeFirstBlock
            (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
            ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
          ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read! (w := w) a len
        = ctx.buf.mem.read! a len := by
      intro w a len ha
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
          Buffed.RegionMPtr.writeParent]
        grind [IsDisjoint, IsIncluded]
      · exact absurd halloc (by simp)
    have hsizele : ctx.buf.mem.size ≤
        (Buffed.RegionMPtr.writeLastBlock
          (Buffed.RegionMPtr.writeFirstBlock
            (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
            ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
          ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.size := by
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
          Buffed.RegionMPtr.writeParent]
        grind [ExArray.blit64_size, ExArray.extend_size]
      · exact absurd halloc (by simp)
    have hattr : (Buffed.RegionMPtr.writeLastBlock
          (Buffed.RegionMPtr.writeFirstBlock
            (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
            ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
          ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).attributes
        = ctx.buf.attributes := by
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
          Buffed.RegionMPtr.writeParent]
      · exact absurd halloc (by simp)
    have hagree : Buffed.AgreesOn _ ctx.buf 0 ctx.buf.mem.size :=
      ⟨hsizele, fun w a len _ ha => hread w a len ha, fun _ _ h => by simp only [hattr]; exact h⟩
    have hrange : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
        p.range ctxSpec = p.range ctx.spec := by
      intro p hp
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      cases p with
      | operation op => exact LayoutPreserved.same_operationPtr_range op (by simpa using hp) hlay |>.symm
      | block bl => exact LayoutPreserved.same_blockPtr_range bl (by simpa using hp) hlay |>.symm
      | region rg => rfl
    have hupper : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
        (p.range ctxSpec).upper ≤ ctx.buf.mem.size := by
      intro p hp
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      have hin := ctx.sim.in_bounds p hp
      rw [hrange p hp]
      simp only [IsIncludedIN, Sim.RawIRContext.spec] at hin
      simp only [ExArray.range_lower, ExArray.range_upper] at hin
      simp only [Sim.IRContext.spec]
      omega
    have hmem : ∀ (p : TopLevelPtr), p.InBounds ctxSpec →
        p.InBounds ctx.spec ∨ p = .region ptrSpec := by
      intro p hp
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      cases p with
      | operation op =>
        have := (RegionPtr.allocEmptyAt_genericPtr_iff (.operation op) hspec).mp (by simpa using hp)
        rcases this with h | h
        · exact Or.inl (by simpa using h)
        · exact absurd h (by simp)
      | block bl =>
        have := (RegionPtr.allocEmptyAt_genericPtr_iff (.block bl) hspec).mp (by simpa using hp)
        rcases this with h | h
        · exact Or.inl (by simpa using h)
        · exact absurd h (by simp)
      | region rg =>
        have := (RegionPtr.allocEmptyAt_genericPtr_iff (.region rg) hspec).mp (by simpa using hp)
        rcases this with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simp only [GenericPtr.region.injEq] at h; grind)
    have hnewrange : ∀ (rg : Veir.RegionPtr), rg = ptrSpec →
        (rg.range).lower = (ctx.buf.mem.size : Int) ∧
        (rg.range).upper = (ctx.buf.mem.size : Int) + Buffed.Region.size.toNat := by
      intro rg hrg
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      subst hrg
      simp only [RegionPtr.range, RegionPtr.toFlat, hptr]
      refine ⟨by grind, by grind⟩
    constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
    · -- fieldsInBounds (spec only)
      exact Veir.RegionPtr.allocEmptyAt_fieldsInBounds hspec ctx.sim.fieldsInBounds
    · -- repr (spec only)
      have hrepr := ctx.sim.repr
      constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · intro op hin
        simp only [Sim.RawIRContext.spec] at *
        grind
      · intro op hin
        simp only [Sim.RawIRContext.spec] at *
        grind
      · intro blk hin
        simp only [Sim.RawIRContext.spec] at *
        grind
      · intro blk hin
        simp only [Sim.RawIRContext.spec] at *
        grind
      · intro rg hin
        simp only [Sim.RawIRContext.spec] at *
        grind
    · -- in_bounds
      intro ptr hib
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      simp only [Buffed.RegionMPtr.writeLastBlock_range, Buffed.RegionMPtr.writeFirstBlock_range,
        Buffed.RegionMPtr.writeParent_range] at hib ⊢
      have hbufrange : buf.mem.range = 0...(ctx.buf.mem.size + Buffed.Region.size.toNat) := by
        simp only [Buffed.IRBufContext.alloc] at halloc
        split at halloc
        · simp only [Option.some.injEq] at halloc
          subst halloc
          simp only [ExArray.extend_range]
        · exact absurd halloc (by simp)
      rw [hbufrange]
      cases ptr with
      | operation op =>
        have holdib : op.InBounds ctx.spec := by
          have := (RegionPtr.allocEmptyAt_genericPtr_iff (.operation op) hspec).mp (by simpa using hib)
          grind
        have hin := ctx.sim.in_bounds (.operation op) (by simpa using holdib)
        have hrange : op.range ctxSpec = op.range ctx.spec :=
          (LayoutPreserved.same_operationPtr_range op holdib hlay).symm
        simp only [TopLevelPtr.range, IsIncludedIN, hrange] at hin ⊢
        grind
      | block bl =>
        have holdib : bl.InBounds ctx.spec := by
          have := (RegionPtr.allocEmptyAt_genericPtr_iff (.block bl) hspec).mp (by simpa using hib)
          grind
        have hin := ctx.sim.in_bounds (.block bl) (by simpa using holdib)
        have hrange : bl.range ctxSpec = bl.range ctx.spec :=
          (LayoutPreserved.same_blockPtr_range bl holdib hlay).symm
        simp only [TopLevelPtr.range, IsIncludedIN, hrange] at hin ⊢
        grind
      | region rg =>
        rcases (RegionPtr.allocEmptyAt_genericPtr_iff (.region rg) hspec).mp (by simpa using hib)
          with hold | hnew
        · have hin := ctx.sim.in_bounds (.region rg) (by simpa using hold)
          simp only [TopLevelPtr.range, RegionPtr.range, RegionPtr.toFlat, IsIncludedIN] at hin ⊢
          grind
        · simp only [GenericPtr.region.injEq] at hnew
          subst hnew
          simp only [TopLevelPtr.range, RegionPtr.range, RegionPtr.toFlat, IsIncludedIN, hptr]
          grind
    · -- disjoint_allocs
      intro p1 p2 hib1 hib2 hne
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      simp only [IsDisjointI]
      rcases hmem p1 hib1 with ho1 | hn1 <;> rcases hmem p2 hib2 with ho2 | hn2
      · -- both old: use the old disjointness, transported along range preservation
        have hdis := ctx.sim.disjoint_allocs p1 p2 ho1 ho2 hne
        simp only [IsDisjointI, hrange p1 ho1, hrange p2 ho2] at hdis ⊢
        exact hdis
      · -- p1 old, p2 = new region: old upper ≤ size = new lower
        subst hn2
        have hu := hupper p1 ho1
        have hnl := (hnewrange ptrSpec rfl).1
        left
        simp only [TopLevelPtr.range] at hnl ⊢
        rw [hnl]
        exact_mod_cast hu
      · -- p1 = new region, p2 old
        subst hn1
        have hu := hupper p2 ho2
        have hnl := (hnewrange ptrSpec rfl).1
        right
        simp only [TopLevelPtr.range] at hnl ⊢
        rw [hnl]
        exact_mod_cast hu
      · -- both = new region: contradicts p1 ≠ p2
        subst hn1; subst hn2
        exact absurd rfl hne
    · -- encoding_op: every op is old; frame each record over the untouched prefix.
      intro op opIb
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      have holdib : op.InBounds ctx.spec := by
        have := (RegionPtr.allocEmptyAt_genericPtr_iff (.operation op) hspec).mp (by simpa using opIb)
        grind
      have henc := ctx.sim.encoding_op op holdib
      have hrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op holdib
      have hget : Veir.OperationPtr.get! op ctxSpec = Veir.OperationPtr.get! op ctx.spec := by grind
      constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · refine OperationPtr.matchesBase_frame ctx op holdib henc.toMatchesBase
          (hagree.mono (Nat.zero_le _) (by grind)) hlay (by rw [hget]) (by rw [hget])
          (by rw [hget]) (by rw [hget]) (by grind [layout_grind]) (Veir.OperationPtr.getProperties!_eq_of_OperationPtr_get!_eq hget) opIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numBlockOperands_frame ctx op holdib henc.numBlockOperands
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
        · intro bo boIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hboIb : bo.InBounds ctx.spec := by
            have := (RegionPtr.allocEmptyAt_genericPtr_iff (.blockOperand bo) hspec).mp (by simpa using boIb)
            grind
          have hincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboIb
          have hpib := Veir.Sim.BlockOperandPtr.op_inBounds hboIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) bo.op hpib
          refine BlockOperandPtr.matches_frame ctx bo hboIb (henc.blockOperands bo hboIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlay (by grind) boIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numRegions_frame ctx op holdib henc.numRegions
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
        · intro idx idxIn
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hnr : idx < op.getNumRegions! ctx.spec := by grind
          have hcap := ctx.sim.repr.operations_indices op holdib |>.capRegions
          refine OperationPtr.nthRegion_frame ctx op holdib idx hnr (henc.regions idx hnr)
            (hagree.mono (Nat.zero_le _) (by grind)) ?_ (by grind)
          have hidxc : idx < (op.get! ctx.spec).capRegions := by grind
          have haddrR : (op.toM.toNat : Int) = op.id := by
            grind [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
          have hincl := OperationPtr.nthRegion_range_included_op_range ctx op idx.toUInt64 (by grind) holdib
          exact hagree.mono (Nat.zero_le _) (by grind [IsIncludedI, UInt64.toNat_ofNat'])
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numOperands_frame ctx op holdib henc.numOperands
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
        · intro oper operIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hooIb : oper.InBounds ctx.spec := by
            have := (RegionPtr.allocEmptyAt_genericPtr_iff (.opOperand oper) hspec).mp (by simpa using operIb)
            grind
          have hincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hooIb
          have hpib := Veir.Sim.OpOperandPtr.op_inBounds hooIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) oper.op hpib
          refine OpOperandPtr.matches_frame ctx oper hooIb (henc.operands oper hooIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlay (by grind) operIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numResults_frame ctx op holdib henc.numResults
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
        · intro res resIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hresIb : res.InBounds ctx.spec := by
            have := (RegionPtr.allocEmptyAt_genericPtr_iff (.opResult res) hspec).mp (by simpa using resIb)
            grind
          have hincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresIb
          have hpib := Veir.Sim.OpResultPtr.op_inBounds hresIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) res.op hpib
          refine OpResultPtr.matches_frame ctx res hresIb (henc.results res hresIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlay (by grind) resIb
    · -- encoding_block: every block is old; frame each record over the untouched prefix.
      intro blk blkIb
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      have holdib : blk.InBounds ctx.spec := by
        have := (RegionPtr.allocEmptyAt_genericPtr_iff (.block blk) hspec).mp (by simpa using blkIb)
        grind
      have henc := ctx.sim.encoding_block blk holdib
      have hrange := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk holdib
      have hget : Veir.BlockPtr.get! blk ctxSpec = Veir.BlockPtr.get! blk ctx.spec := by grind
      constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · refine BlockPtr.matchesBase_frame ctx blk holdib henc.toMatchesBase
          (hagree.mono (Nat.zero_le _) (by grind)) hlay (by rw [hget]) (by rw [hget])
          (by rw [hget]) (by rw [hget]) (by rw [hget]) (by rw [hget]) blkIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact BlockPtr.numArguments_frame ctx blk holdib henc.numArguments
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget])
        · intro arg argIn heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hargIb : arg.InBounds ctx.spec := by
            have := (RegionPtr.allocEmptyAt_genericPtr_iff (.blockArgument arg) hspec).mp (by simpa using argIn)
            grind
          have hincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargIb
          have hpib := Veir.Sim.BlockArgumentPtr.block_inBounds hargIb
          have hprangeS := Veir.Sim.BlockPtr.range_linear (ctx := ctx) arg.block hpib
          refine BlockArgumentPtr.matches_frame ctx arg hargIb (henc.arguments arg hargIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlay (by grind) argIn
    · -- encoding_region
      intro rg rgIb
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      rcases (RegionPtr.allocEmptyAt_genericPtr_iff (.region rg) hspec).mp (by simpa using rgIb)
        with hold | hnew
      · -- Old region: frame the 24-byte record.
        have holdib : rg.InBounds ctx.spec := by simpa using hold
        have henc := ctx.sim.encoding_region rg holdib
        have hrange := Veir.Sim.RegionPtr.range_linear (ctx := ctx) rg holdib
        refine RegionPtr.matches_frame ctx rg holdib henc
          (hagree.mono (Nat.zero_le _) (by grind)) hlay (by grind) rgIb
      · -- New region = ptrSpec: reads at fresh address return the written `none`s.
        simp only [GenericPtr.region.injEq] at hnew
        subst hnew
        have hget : Veir.RegionPtr.get! rg ctxSpec = Region.empty := by grind
        have htoM : rg.toM = ctx.buf.usize := by
          simp only [hptr, RegionPtr.toM, RegionPtr.toFlat]; grind
        have husz : ctx.buf.usize.toNat < 2 ^ 63 := by grind
        have hmax : (Int64.maxValue.toInt : Int) = 2 ^ 63 - 1 := by decide
        have a0 : (ctx.buf.usize + Buffed.Region.Offsets.firstBlock).toNat = ctx.buf.usize.toNat := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
        have a8 : (ctx.buf.usize + Buffed.Region.Offsets.lastBlock).toNat = ctx.buf.usize.toNat + 8 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
        have a16 : (ctx.buf.usize + Buffed.Region.Offsets.parent).toNat = ctx.buf.usize.toNat + 16 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
        constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · -- firstBlock: read at usize+0 hits writeFirstBlock
          simp only [Sim.OptionBlockPtr.Sim_def, Sim.OptionBlockPtr.spec, Erased.out_mk, hget, Region.empty, Buffed.RegionMPtr.readFirstBlock!,
            Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
            Buffed.RegionMPtr.writeParent, htoM]
          rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
            ExArray.read64!_blit64_self]
          simp [Veir.BlockPtr.toO]
        · -- lastBlock: read at usize+8 hits writeLastBlock (passing writeFirstBlock at +0)
          simp only [Sim.OptionBlockPtr.Sim_def, Sim.OptionBlockPtr.spec, Erased.out_mk, hget, Region.empty, Buffed.RegionMPtr.readLastBlock!,
            Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
            Buffed.RegionMPtr.writeParent, htoM]
          rw [ExArray.read64!_blit64_self]
          simp [Veir.BlockPtr.toO]
        · -- parent: read at usize+16 hits writeParent (passing the two block writes)
          simp only [Sim.OptionOperationPtr.Sim_def, Sim.OptionOperationPtr.spec, Erased.out_mk, hget, Region.empty, Buffed.RegionMPtr.readParent!,
            Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
            Buffed.RegionMPtr.writeParent, htoM]
          rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
            ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
            ExArray.read64!_blit64_self]
          simp [Veir.OperationPtr.toO]
    · -- attr_empty
      rw [hattr]
      exact ctx.sim.attr_empty
    · rw [hfree]
      exact ctx.sim.free_valid.mono hsizele
    · intro size address hm p hp
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      rw [hfree] at hm
      rcases hmem p hp with hold | rfl
      · rw [hrange p hold]
        exact ctx.sim.free_disjoint size address hm p hold
      · have hb := (ctx.sim.free_valid.bounds size address hm).2
        right
        simp only [TopLevelPtr.range]
        rw [(hnewrange ptrSpec rfl).1]
        exact_mod_cast hb


@[inline]
def Sim.RegionPtr.allocEmpty (ctx : Sim.IRContext OpInfo) : Option (Sim.RegionPtr × Sim.IRContext OpInfo) :=
  match himpl : allocEmptyImpl ctx.buf with
  | none => none
  | some (ctxBuf, ptrImpl) =>
    let specRes := ctx.spec'.map (fun spec => (Veir.RegionPtr.allocEmptyAt spec ptrImpl.toNat).get!)
    have hspec : Veir.RegionPtr.allocEmptyAt ctx.spec ptrImpl.toNat = some specRes.out := by
      have hptr : ptrImpl = ctx.buf.usize := by
        simp only [allocEmptyImpl] at himpl
        split at himpl <;> grind
      have hfree := Sim.RegionPtr.slot_free ctx
      simp only [Veir.RegionPtr.inBounds_def] at hfree
      have husz := ctx.buf.usize_toNat
      have hs := ctx.buf.size_def
      have hsome := Veir.RegionPtr.allocEmptyAt_isSome_of_not_mem
        (ctx := ctx.spec) (addr := ptrImpl.toNat) (by grind)
      simpa only [specRes, Erased.map_out, Option.get!] using (Option.some_get! _ hsome).symm
    some ⟨⟨ptrImpl, specRes.map Prod.snd⟩, ⟨ctxBuf, specRes.map Prod.fst, by
      simpa only [Erased.map_eq_mk] using allocEmpty_sim ctx himpl hspec⟩⟩

/-- Strengthening of `allocEmpty_spec`: the spec-level region is allocated exactly at the address of the returned impl pointer. -/
theorem Sim.RegionPtr.allocEmpty_spec' {ctx : Sim.IRContext OpInfo} :
    allocEmpty ctx = some ⟨ptr, ctx'⟩ →
    Veir.RegionPtr.allocEmptyAt ctx.spec ptr.impl.toNat = some ⟨ctx'.spec, ptr.spec⟩ := by
  intro h
  simp only [allocEmpty] at h
  split at h
  · exact absurd h (by simp)
  · rename_i ctxBuf ptrImpl himpl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    have hptr : ptrImpl = ctx.buf.usize := by
      simp only [allocEmptyImpl] at himpl
      split at himpl <;> grind
    have hfree := Sim.RegionPtr.slot_free ctx
    simp only [Veir.RegionPtr.inBounds_def] at hfree
    have husz := ctx.buf.usize_toNat
    have hs := ctx.buf.size_def
    have hsome := Veir.RegionPtr.allocEmptyAt_isSome_of_not_mem
      (ctx := ctx.spec) (addr := ptrImpl.toNat) (by grind)
    rw [← Option.some_get! _ hsome]
    simp [Sim.IRContext.spec, Sim.RegionPtr.spec]

@[grind! .]
theorem Sim.RegionPtr.allocEmpty_spec {ctx : Sim.IRContext OpInfo} :
    allocEmpty ctx = some ⟨ptr, ctx'⟩ →
    ∃ addr, Veir.RegionPtr.allocEmptyAt ctx.spec addr = some ⟨ctx'.spec, ptr.spec⟩:=
  fun h => ⟨ptr.impl.toNat, Sim.RegionPtr.allocEmpty_spec' h⟩

set_option maxHeartbeats 10000000 in
@[inline]
def Sim.OperationPtr.allocEmptyHeaderImpl (ctx₀ : Buffed.IRBufContext)
    (numResults numOperands numBlockOperands numRegions propSize : UInt64)
    (opType : UInt32)
    (hr : numResults.toNat ≤ Buffed.countCard) (ho : numOperands.toNat ≤ Buffed.countCard)
    (hbo : numBlockOperands.toNat ≤ Buffed.countCard) (hreg : numRegions.toNat ≤ Buffed.countCard)
    (hp : propSize.toNat ≤ Buffed.countCard) :
    Option (Buffed.IRBufContext × Buffed.OperationMPtr) :=
  let size := Buffed.OperationMPtr.computeOperationSize numResults numOperands numBlockOperands numRegions propSize
  -- The operation pointer points past the (back-allocated) results array.
  let ptr : Buffed.OperationMPtr := ctx₀.usize + (Buffed.OpResult.size * numResults)
  rlet halloc : ctx ← ctx₀.alloc size
  have hsize : ctx.size = ctx₀.size + size.toNat := ctx₀.alloc_size halloc
  have hopsize : size.toNat =
      Buffed.Operation.sizeBase.toNat + propSize.toNat +
      numResults.toNat * Buffed.OpResult.size.toNat + numOperands.toNat * Buffed.OpOperand.size.toNat +
      numBlockOperands.toNat * Buffed.BlockOperand.size.toNat + numRegions.toNat * Buffed.ptrSize.toNat :=
    Buffed.OperationMPtr.computeOperationSize_toNat _ _ _ _ _ hr ho hbo hreg hp
  have hprefix : ctx₀.size + numResults.toNat * Buffed.OpResult.size.toNat ≤ ctx.size := by grind
  have hcs : ctx.size < 2 ^ 63 := by
    have := ctx.mem.fits_in_memory
    grind
  have hptr : ptr.toNat = ctx₀.size + numResults.toNat * Buffed.OpResult.size.toNat := by grind [UInt64.toNat_mul]
  have hptrlt : ptr.toNat < 2 ^ 63 := by omega
  let ctx := ptr.writeNumOperands ctx numOperands (by prove_allocBoundsOp ctx₀)
  let ctx := ptr.writeNumResults ctx numResults (by prove_allocBoundsOp ctx₀)
  let ctx := ptr.writeNumBlockOperands ctx numBlockOperands (by prove_allocBoundsOp ctx₀)
  let ctx := ptr.writeNumRegions ctx numRegions (by prove_allocBoundsOp ctx₀)
  let ctx := ptr.writeParent ctx .none (by prove_allocBoundsOp ctx₀)
  let ctx := ptr.writeNext ctx .none (by prove_allocBoundsOp ctx₀)
  let ctx := ptr.writePrev ctx .none (by prove_allocBoundsOp ctx₀)
  let ctx := ptr.writeOpType ctx opType (by prove_allocBoundsOp ctx₀)
  some (ctx, ptr)

theorem Sim.OperationPtr.allocEmptyHeaderImpl_freeList {ctx₀ ctxBuf : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ptr : UInt64}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptr)) :
    ctxBuf.freeList = ctx₀.freeList := by
  simp only [allocEmptyHeaderImpl] at h
  split at h
  · contradiction
  · rename_i buf halloc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Buffed.IRBufContext.alloc_freeList (bctx' := buf) halloc

/-- The operation pointer produced by `allocEmptyHeaderImpl` lies at or past the end of the buffer: its address is the old buffer size plus the back-allocated results prefix. -/
theorem Sim.OperationPtr.allocEmptyHeaderImpl_ptr_ge {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64}
    {hr ho hbo hreg hp hc} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize hc
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl)) :
    ctx₀.mem.size ≤ ptrImpl.toNat := by
  simp only [allocEmptyHeaderImpl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i buf halloc
    have hu := ctx₀.usize_toNat
    obtain ⟨_, rfl⟩ := Option.some.injEq _ _ ▸ h
    have hfits := buf.mem.fits_in_memory
    have hsz := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
      numBlockOperands numRegions propSize hr ho hbo hreg hp
    have halsz := ctx₀.alloc_size halloc
    have hnr := UInt64.toNat_lt numResults
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    simp only [Buffed.IRBufContext.size_def, show Buffed.OpResult.size.toNat = 40 from rfl,
      Int64.maxNatValue, Buffed.ptrSize] at *
    omega

/-- Closed form of the operation pointer returned by `allocEmptyHeaderImpl`: the old buffer size plus the back-allocated results array. -/
theorem Sim.OperationPtr.allocEmptyHeaderImpl_ptr_toNat {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl)) :
    ptrImpl.toNat = ctx₀.mem.size + Buffed.OpResult.size.toNat * numResults.toNat := by
  simp only [allocEmptyHeaderImpl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i buf halloc
    have hu := ctx₀.usize_toNat
    obtain ⟨_, rfl⟩ := Option.some.injEq _ _ ▸ h
    have hfits := buf.mem.fits_in_memory
    have hsz := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
      numBlockOperands numRegions propSize hr ho hbo hreg hp
    have halsz := ctx₀.alloc_size halloc
    have hnr := UInt64.toNat_lt numResults
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    simp only [Buffed.IRBufContext.size_def, show Buffed.OpResult.size.toNat = 40 from rfl,
      Int64.maxNatValue, Buffed.ptrSize] at *
    omega

/-- `allocEmptyHeaderImpl` only touches `mem`; the attribute table is unchanged. -/
theorem Sim.OperationPtr.allocEmptyHeaderImpl_attributes {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl)) :
    ctxBuf.attributes = ctx₀.attributes := by
  simp only [allocEmptyHeaderImpl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i buf halloc
    obtain ⟨rfl, rfl⟩ := Option.some.injEq _ _ ▸ h
    simp only [Buffed.IRBufContext.alloc] at halloc
    split at halloc
    · obtain rfl := Option.some.injEq _ _ ▸ halloc
      rfl
    · exact absurd halloc (by simp)

/-- `allocEmptyHeaderImpl` grows the buffer by exactly the computed operation size. -/
theorem Sim.OperationPtr.allocEmptyHeaderImpl_size {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl)) :
    ctxBuf.mem.size = ctx₀.mem.size +
      (Buffed.OperationMPtr.computeOperationSize numResults numOperands numBlockOperands
        numRegions propSize).toNat := by
  simp only [allocEmptyHeaderImpl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i buf halloc
    obtain ⟨rfl, rfl⟩ := Option.some.injEq _ _ ▸ h
    have halsz := ctx₀.alloc_size halloc
    simp only [Buffed.IRBufContext.size_def] at *
    grind [Buffed.OperationMPtr.writeNumResults_size, Buffed.OperationMPtr.writeNumOperands_size,
      Buffed.OperationMPtr.writeNumBlockOperands_size, Buffed.OperationMPtr.writeNumRegions_size,
      Buffed.OperationMPtr.writeParent_size, Buffed.OperationMPtr.writeNext_size,
      Buffed.OperationMPtr.writePrev_size, Buffed.OperationMPtr.writeOpType_size]

/-- 64-bit reads that lie entirely inside the old buffer are unchanged by `allocEmptyHeaderImpl`: the fresh operation is written past the old buffer end. -/
theorem Sim.OperationPtr.allocEmptyHeaderImpl_read64_old {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl))
    (n : UInt64) (hn : n.toNat + 8 ≤ ctx₀.mem.size) :
    ctxBuf.mem.read64! n = ctx₀.mem.read64! n := by
  have hptr := Sim.OperationPtr.allocEmptyHeaderImpl_ptr_ge h
  have hptn := Sim.OperationPtr.allocEmptyHeaderImpl_ptr_toNat h
  have hu := ctx₀.usize_toNat
  have hfits := ctx₀.mem.fits_in_memory
  have hsz := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions propSize hr ho hbo hreg hp
  have hnr := UInt64.toNat_lt numResults
  simp only [allocEmptyHeaderImpl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i buf halloc
    obtain ⟨rfl, rfl⟩ := Option.some.injEq _ _ ▸ h
    have halsz := ctx₀.alloc_size halloc
    have hbfits := buf.mem.fits_in_memory
    simp only [Buffed.IRBufContext.alloc] at halloc
    split at halloc
    · obtain rfl := Option.some.injEq _ _ ▸ halloc
      simp only [Buffed.IRBufContext.size_def, show Buffed.OpResult.size = (40 : UInt64) from rfl,
        show ((40 : UInt64)).toNat = 40 from rfl,
        show Buffed.Operation.sizeBase.toNat = 72 from rfl, Int64.maxNatValue] at *
      have hrange : ctx₀.mem.range = 0...ctx₀.mem.size := ExArray.range_def _
      have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 64 →
          (ctx₀.usize + 40 * numResults + k).toNat
          = (ctx₀.usize + 40 * numResults).toNat + kn := by
        intro k kn hkn hk
        rw [UInt64.toNat_add, hkn]
        apply Nat.mod_eq_of_lt
        omega
      have h8 := hstep 8 8 rfl (by omega)
      have h16 := hstep 16 16 rfl (by omega)
      have h24 := hstep 24 24 rfl (by omega)
      have h32 := hstep 32 32 rfl (by omega)
      have h40 := hstep 40 40 rfl (by omega)
      have h48 := hstep 48 48 rfl (by omega)
      have h56 := hstep 56 56 rfl (by omega)
      have h64 := hstep 64 64 rfl (by omega)
      clear hstep
      simp only [Buffed.OperationMPtr.writeOpType, Buffed.OperationMPtr.writePrev,
        Buffed.OperationMPtr.writeNext, Buffed.OperationMPtr.writeParent,
        Buffed.OperationMPtr.writeNumRegions, Buffed.OperationMPtr.writeNumBlockOperands,
        Buffed.OperationMPtr.writeNumResults, Buffed.OperationMPtr.writeNumOperands]
      grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded]
    · exact absurd halloc (by simp)

/-- 32-bit variant of `allocEmptyHeaderImpl_read64_old`. -/
theorem Sim.OperationPtr.allocEmptyHeaderImpl_read32_old {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl))
    (n : UInt64) (hn : n.toNat + 4 ≤ ctx₀.mem.size) :
    ctxBuf.mem.read32! n = ctx₀.mem.read32! n := by
  have hptr := Sim.OperationPtr.allocEmptyHeaderImpl_ptr_ge h
  have hptn := Sim.OperationPtr.allocEmptyHeaderImpl_ptr_toNat h
  have hu := ctx₀.usize_toNat
  have hfits := ctx₀.mem.fits_in_memory
  have hsz := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions propSize hr ho hbo hreg hp
  have hnr := UInt64.toNat_lt numResults
  simp only [allocEmptyHeaderImpl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i buf halloc
    obtain ⟨rfl, rfl⟩ := Option.some.injEq _ _ ▸ h
    have halsz := ctx₀.alloc_size halloc
    have hbfits := buf.mem.fits_in_memory
    simp only [Buffed.IRBufContext.alloc] at halloc
    split at halloc
    · obtain rfl := Option.some.injEq _ _ ▸ halloc
      simp only [Buffed.IRBufContext.size_def, show Buffed.OpResult.size = (40 : UInt64) from rfl,
        show ((40 : UInt64)).toNat = 40 from rfl,
        show Buffed.Operation.sizeBase.toNat = 72 from rfl, Int64.maxNatValue] at *
      have hrange : ctx₀.mem.range = 0...ctx₀.mem.size := ExArray.range_def _
      have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 64 →
          (ctx₀.usize + 40 * numResults + k).toNat
          = (ctx₀.usize + 40 * numResults).toNat + kn := by
        intro k kn hkn hk
        rw [UInt64.toNat_add, hkn]
        apply Nat.mod_eq_of_lt
        omega
      have h8 := hstep 8 8 rfl (by omega)
      have h16 := hstep 16 16 rfl (by omega)
      have h24 := hstep 24 24 rfl (by omega)
      have h32 := hstep 32 32 rfl (by omega)
      have h40 := hstep 40 40 rfl (by omega)
      have h48 := hstep 48 48 rfl (by omega)
      have h56 := hstep 56 56 rfl (by omega)
      have h64 := hstep 64 64 rfl (by omega)
      clear hstep
      simp only [Buffed.OperationMPtr.writeOpType, Buffed.OperationMPtr.writePrev,
        Buffed.OperationMPtr.writeNext, Buffed.OperationMPtr.writeParent,
        Buffed.OperationMPtr.writeNumRegions, Buffed.OperationMPtr.writeNumBlockOperands,
        Buffed.OperationMPtr.writeNumResults, Buffed.OperationMPtr.writeNumOperands]
      grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded]
    · exact absurd halloc (by simp)

/-- Generic-width variant of `allocEmptyHeaderImpl_read64_old`. -/
theorem Sim.OperationPtr.allocEmptyHeaderImpl_read_old {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl))
    (w : Nat) (n len : UInt64) (hn : n.toNat + len.toNat ≤ ctx₀.mem.size) :
    ctxBuf.mem.read! (w := w) n len = ctx₀.mem.read! n len := by
  have hptr := Sim.OperationPtr.allocEmptyHeaderImpl_ptr_ge h
  have hptn := Sim.OperationPtr.allocEmptyHeaderImpl_ptr_toNat h
  have hu := ctx₀.usize_toNat
  have hfits := ctx₀.mem.fits_in_memory
  have hsz := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions propSize hr ho hbo hreg hp
  have hnr := UInt64.toNat_lt numResults
  simp only [allocEmptyHeaderImpl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i buf halloc
    obtain ⟨rfl, rfl⟩ := Option.some.injEq _ _ ▸ h
    have halsz := ctx₀.alloc_size halloc
    have hbfits := buf.mem.fits_in_memory
    simp only [Buffed.IRBufContext.alloc] at halloc
    split at halloc
    · obtain rfl := Option.some.injEq _ _ ▸ halloc
      simp only [Buffed.IRBufContext.size_def, show Buffed.OpResult.size = (40 : UInt64) from rfl,
        show ((40 : UInt64)).toNat = 40 from rfl,
        show Buffed.Operation.sizeBase.toNat = 72 from rfl, Int64.maxNatValue] at *
      have hrange : ctx₀.mem.range = 0...ctx₀.mem.size := ExArray.range_def _
      have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 64 →
          (ctx₀.usize + 40 * numResults + k).toNat
          = (ctx₀.usize + 40 * numResults).toNat + kn := by
        intro k kn hkn hk
        rw [UInt64.toNat_add, hkn]
        apply Nat.mod_eq_of_lt
        omega
      have h8 := hstep 8 8 rfl (by omega)
      have h16 := hstep 16 16 rfl (by omega)
      have h24 := hstep 24 24 rfl (by omega)
      have h32 := hstep 32 32 rfl (by omega)
      have h40 := hstep 40 40 rfl (by omega)
      have h48 := hstep 48 48 rfl (by omega)
      have h56 := hstep 56 56 rfl (by omega)
      have h64 := hstep 64 64 rfl (by omega)
      clear hstep
      simp only [Buffed.OperationMPtr.writeOpType, Buffed.OperationMPtr.writePrev,
        Buffed.OperationMPtr.writeNext, Buffed.OperationMPtr.writeParent,
        Buffed.OperationMPtr.writeNumRegions, Buffed.OperationMPtr.writeNumBlockOperands,
        Buffed.OperationMPtr.writeNumResults, Buffed.OperationMPtr.writeNumOperands]
      grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded]
    · exact absurd halloc (by simp)

/-- The header fields of the freshly allocated operation read back as written: the counts are the requested capacities, the links are `none`, the opType is the encoded opcode, and the `attrs` slot is still zero-initialized (pointing at the canonical empty dictionary). -/
theorem Sim.OperationPtr.allocEmptyHeaderImpl_new_op_reads {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl)) :
    Buffed.OperationMPtr.readNumResults! ctxBuf ptrImpl = numResults ∧
    Buffed.OperationMPtr.readNumOperands! ctxBuf ptrImpl = numOperands ∧
    Buffed.OperationMPtr.readNumBlockOperands! ctxBuf ptrImpl = numBlockOperands ∧
    Buffed.OperationMPtr.readNumRegions! ctxBuf ptrImpl = numRegions ∧
    Buffed.OperationMPtr.readPrev! ctxBuf ptrImpl = Buffed.OperationOPtr.none ∧
    Buffed.OperationMPtr.readNext! ctxBuf ptrImpl = Buffed.OperationOPtr.none ∧
    Buffed.OperationMPtr.readParent! ctxBuf ptrImpl = Buffed.BlockOPtr.none ∧
    Buffed.OperationMPtr.readOpType! ctxBuf ptrImpl = opType ∧
    Buffed.OperationMPtr.readAttrs! ctxBuf ptrImpl = 0 := by
  have hptr := Sim.OperationPtr.allocEmptyHeaderImpl_ptr_ge h
  have hptn := Sim.OperationPtr.allocEmptyHeaderImpl_ptr_toNat h
  have hu := ctx₀.usize_toNat
  have hfits := ctx₀.mem.fits_in_memory
  have hsz := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions propSize hr ho hbo hreg hp
  have hnr := UInt64.toNat_lt numResults
  simp only [allocEmptyHeaderImpl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i buf halloc
    obtain ⟨rfl, rfl⟩ := Option.some.injEq _ _ ▸ h
    have halsz := ctx₀.alloc_size halloc
    have hbfits := buf.mem.fits_in_memory
    simp only [Buffed.IRBufContext.alloc] at halloc
    split at halloc
    · obtain rfl := Option.some.injEq _ _ ▸ halloc
      simp only [Buffed.IRBufContext.size_def, show Buffed.OpResult.size = (40 : UInt64) from rfl,
        show ((40 : UInt64)).toNat = 40 from rfl,
        show Buffed.Operation.sizeBase.toNat = 72 from rfl, Int64.maxNatValue] at *
      have hrange : ctx₀.mem.range = 0...ctx₀.mem.size := ExArray.range_def _
      have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 64 →
          (ctx₀.usize + 40 * numResults + k).toNat
          = (ctx₀.usize + 40 * numResults).toNat + kn := by
        intro k kn hkn hk
        rw [UInt64.toNat_add, hkn]
        apply Nat.mod_eq_of_lt
        omega
      have h8 := hstep 8 8 rfl (by omega)
      have h16 := hstep 16 16 rfl (by omega)
      have h24 := hstep 24 24 rfl (by omega)
      have h32 := hstep 32 32 rfl (by omega)
      have h40 := hstep 40 40 rfl (by omega)
      have h48 := hstep 48 48 rfl (by omega)
      have h56 := hstep 56 56 rfl (by omega)
      have h64 := hstep 64 64 rfl (by omega)
      clear hstep
      simp only [Buffed.OperationMPtr.readNumResults!, Buffed.OperationMPtr.readNumOperands!,
        Buffed.OperationMPtr.readNumBlockOperands!, Buffed.OperationMPtr.readNumRegions!,
        Buffed.OperationMPtr.readPrev!, Buffed.OperationMPtr.readNext!,
        Buffed.OperationMPtr.readParent!, Buffed.OperationMPtr.readOpType!,
        Buffed.OperationMPtr.readAttrs!,
        Buffed.OperationMPtr.writeOpType, Buffed.OperationMPtr.writePrev,
        Buffed.OperationMPtr.writeNext, Buffed.OperationMPtr.writeParent,
        Buffed.OperationMPtr.writeNumRegions, Buffed.OperationMPtr.writeNumBlockOperands,
        Buffed.OperationMPtr.writeNumResults, Buffed.OperationMPtr.writeNumOperands]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded, ExArray.read64!_extend_new]
    · exact absurd halloc (by simp)

/-- The property slot of the fresh operation starts at `ptrImpl + 72`, which is at or past the old buffer end. -/
theorem Sim.OperationPtr.allocEmptyHeaderImpl_properties_toNat {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxH : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize
      opType hr ho hbo hreg hp = some (ctxH, ptrImpl)) :
    ∀ (off : Int64) (k : Nat), off.toInt = (k : Int) → k ≤ 72 →
      (ptrImpl + off).toNat = ptrImpl.toNat + k := by
  have hptn := allocEmptyHeaderImpl_ptr_toNat h
  have hsz := allocEmptyHeaderImpl_size h
  have hfits := ctxH.mem.fits_in_memory
  have hcst := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions propSize hr ho hbo hreg hp
  have hnr := UInt64.toNat_lt numResults
  have hmax : Int64.maxValue.toInt = 2^63 - 1 := by decide
  have hptrlt : ptrImpl.toNat + 72 < 2^63 := by
    simp only [Int64.maxNatValue,
      show Buffed.OpResult.size.toNat = 40 from rfl,
      show Buffed.Operation.sizeBase.toNat = 72 from rfl] at *
    omega
  intro off k hoff hk
  rw [UInt64.uint64_add_int64_toNat_lt (by omega) (by omega)]
  omega

/-- Largest attribute-table size accepted by `allocEmptyImpl` (`2^63 - 1`).
A `@[noinline]` constant: the value is the largest scalar `Nat`, and both literal spellings
compile badly at use sites — `< 2^63` compares against an mpz (GMP temporary per allocation),
and an inline `2^63 - 1` literal is re-materialized by `lean_cstr_to_nat` (GMP string parse per
allocation). As a constant it is built once and every guard is a scalar compare. -/
@[noinline]
def Sim.OperationPtr.attrTableMaxSize : Nat := 9223372036854775807

theorem Sim.OperationPtr.attrTableMaxSize_eq : attrTableMaxSize = 2^63 - 1 := rfl

/-- Allocate an empty operation record and store its property: the header fields are written by
`allocEmptyHeaderImpl` (with the property slot sized by `HasDialectOpInfo.propertySize`), then the
property itself is written into the slot (which may also append its spilled encoding to the
attribute table — hence the guard that the table still has a free 63-bit index). -/
@[inline]
def Sim.OperationPtr.allocEmptyImpl {opCode : OpInfo} (ctx₀ : Buffed.IRBufContext)
    (numResults numOperands numBlockOperands numRegions : UInt64)
    (opType : UInt32) (prop : HasDialectOpInfo.propertiesOf opCode)
    (hr : numResults.toNat ≤ Buffed.countCard) (ho : numOperands.toNat ≤ Buffed.countCard)
    (hbo : numBlockOperands.toNat ≤ Buffed.countCard) (hreg : numRegions.toNat ≤ Buffed.countCard) :
    Option (Buffed.IRBufContext × Buffed.OperationMPtr) :=
  if hattrs : ctx₀.attributes.size ≤ attrTableMaxSize then
    match heq : allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions
        (HasDialectOpInfo.propertySize opCode) opType hr ho hbo hreg
        (Nat.le_of_lt HasDialectOpInfo.propertySize_small) with
    | none => none
    | some (ctx, ptr) =>
      some (HasBuffedProperties.writePropertyAt opCode prop
        (ptr + Buffed.Operation.Offsets.properties) ctx
        (by
          have hsz := Sim.OperationPtr.allocEmptyHeaderImpl_size heq
          have hptn := Sim.OperationPtr.allocEmptyHeaderImpl_ptr_toNat heq
          have hoff := Sim.OperationPtr.allocEmptyHeaderImpl_properties_toNat heq
            Buffed.Operation.Offsets.properties 72 (by decide) (by omega)
          have hcst := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
            numBlockOperands numRegions (HasDialectOpInfo.propertySize opCode) hr ho hbo hreg
            (Nat.le_of_lt HasDialectOpInfo.propertySize_small)
          simp only [show Buffed.OpResult.size.toNat = 40 from rfl,
            show Buffed.Operation.sizeBase.toNat = 72 from rfl] at *
          omega)
        (by
          rw [Sim.OperationPtr.allocEmptyHeaderImpl_attributes heq]
          rw [Sim.OperationPtr.attrTableMaxSize_eq] at hattrs
          omega), ptr)
  else
    none

/-- Destructure a successful `allocEmptyImpl` into its header allocation and the property write. -/
theorem Sim.OperationPtr.allocEmptyImpl_eq {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl)) :
    ∃ (ctxH : Buffed.IRBufContext),
      allocEmptyHeaderImpl ctx₀ numResults numOperands numBlockOperands numRegions
        (HasDialectOpInfo.propertySize opCode) opType hr ho hbo hreg
        (Nat.le_of_lt HasDialectOpInfo.propertySize_small) = some (ctxH, ptrImpl) ∧
      ∃ h₁ h₂, ctxBuf = HasBuffedProperties.writePropertyAt opCode prop
        (ptrImpl + Buffed.Operation.Offsets.properties) ctxH h₁ h₂ := by
  simp only [allocEmptyImpl] at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · rename_i ctxH ptr heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hbuf, rfl⟩ := h
      exact ⟨ctxH, heq, _, _, hbuf.symm⟩
  · exact absurd h (by simp)

theorem Sim.OperationPtr.allocEmptyImpl_freeList {opCode : OpInfo}
    {ctx₀ ctxBuf : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode} {hr ho hbo hreg} {ptr : UInt64}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptr)) :
    ctxBuf.freeList = ctx₀.freeList := by
  obtain ⟨ctxH, hH, _, _, rfl⟩ := allocEmptyImpl_eq h
  rw [HasBuffedProperties.preserves_freeList]
  exact allocEmptyHeaderImpl_freeList hH

/-- The operation pointer produced by `allocEmptyImpl` lies at or past the end of the buffer. -/
theorem Sim.OperationPtr.allocEmptyImpl_ptr_ge {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl)) :
    ctx₀.mem.size ≤ ptrImpl.toNat := by
  obtain ⟨ctxH, hH, -⟩ := allocEmptyImpl_eq h
  exact allocEmptyHeaderImpl_ptr_ge hH

/-- Closed form of the operation pointer returned by `allocEmptyImpl`. -/
theorem Sim.OperationPtr.allocEmptyImpl_ptr_toNat {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl)) :
    ptrImpl.toNat = ctx₀.mem.size + Buffed.OpResult.size.toNat * numResults.toNat := by
  obtain ⟨ctxH, hH, -⟩ := allocEmptyImpl_eq h
  exact allocEmptyHeaderImpl_ptr_toNat hH

/-- `allocEmptyImpl` only appends to the attribute table (when the property is spilled), so existing entries keep their index. -/
theorem Sim.OperationPtr.allocEmptyImpl_attributes {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl))
    {i : Nat} {a : Attribute} (hsome : ctx₀.attributes[i]? = some a) :
    ctxBuf.attributes[i]? = some a := by
  obtain ⟨ctxH, hH, h₁, h₂, rfl⟩ := allocEmptyImpl_eq h
  refine HasBuffedProperties.only_adds_attributes i ?_
  rw [allocEmptyHeaderImpl_attributes hH]
  exact hsome

/-- `allocEmptyImpl` grows the buffer by exactly the computed operation size. -/
theorem Sim.OperationPtr.allocEmptyImpl_size {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl)) :
    ctxBuf.mem.size = ctx₀.mem.size +
      (Buffed.OperationMPtr.computeOperationSize numResults numOperands numBlockOperands
        numRegions (HasDialectOpInfo.propertySize opCode)).toNat := by
  obtain ⟨ctxH, hH, h₁, h₂, rfl⟩ := allocEmptyImpl_eq h
  rw [HasBuffedProperties.preserves_size]
  exact allocEmptyHeaderImpl_size hH

/-- 64-bit reads that lie entirely inside the old buffer are unchanged by `allocEmptyImpl`. -/
theorem Sim.OperationPtr.allocEmptyImpl_read64_old {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl))
    (n : UInt64) (hn : n.toNat + 8 ≤ ctx₀.mem.size) :
    ctxBuf.mem.read64! n = ctx₀.mem.read64! n := by
  obtain ⟨ctxH, hH, h₁, h₂, rfl⟩ := allocEmptyImpl_eq h
  have hge := allocEmptyHeaderImpl_ptr_ge hH
  have haddr := allocEmptyHeaderImpl_properties_toNat hH Buffed.Operation.Offsets.properties 72
    (by decide) (by omega)
  rw [HasBuffedProperties.read64!_writePropertyAt (Or.inl (show n.toNat + 8
    ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat by omega))]
  exact allocEmptyHeaderImpl_read64_old hH n hn

/-- 32-bit variant of `allocEmptyImpl_read64_old`. -/
theorem Sim.OperationPtr.allocEmptyImpl_read32_old {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl))
    (n : UInt64) (hn : n.toNat + 4 ≤ ctx₀.mem.size) :
    ctxBuf.mem.read32! n = ctx₀.mem.read32! n := by
  obtain ⟨ctxH, hH, h₁, h₂, rfl⟩ := allocEmptyImpl_eq h
  have hge := allocEmptyHeaderImpl_ptr_ge hH
  have haddr := allocEmptyHeaderImpl_properties_toNat hH Buffed.Operation.Offsets.properties 72
    (by decide) (by omega)
  rw [HasBuffedProperties.read32!_writePropertyAt (Or.inl (show n.toNat + 4
    ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat by omega))]
  exact allocEmptyHeaderImpl_read32_old hH n hn

/-- Generic-width variant of `allocEmptyImpl_read64_old`. -/
theorem Sim.OperationPtr.allocEmptyImpl_read_old {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl))
    (w : Nat) (n len : UInt64) (hn : n.toNat + len.toNat ≤ ctx₀.mem.size) :
    ctxBuf.mem.read! (w := w) n len = ctx₀.mem.read! n len := by
  obtain ⟨ctxH, hH, h₁, h₂, rfl⟩ := allocEmptyImpl_eq h
  have hge := allocEmptyHeaderImpl_ptr_ge hH
  have haddr := allocEmptyHeaderImpl_properties_toNat hH Buffed.Operation.Offsets.properties 72
    (by decide) (by omega)
  rw [HasBuffedProperties.only_modifies_properties (Or.inl (show n.toNat + len.toNat
    ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat by omega))]
  exact allocEmptyHeaderImpl_read_old hH w n len hn

/-- The property slot of the freshly allocated operation reads back the written property. -/
theorem Sim.OperationPtr.allocEmptyImpl_readProperty {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl)) :
    HasBuffedProperties.readPropertyAt opCode (ptrImpl + Buffed.Operation.Offsets.properties) ctxBuf
      = some prop := by
  obtain ⟨ctxH, hH, h₁, h₂, rfl⟩ := allocEmptyImpl_eq h
  exact HasBuffedProperties.read_after_write

/-- The header fields of the freshly allocated operation read back as written: the property write
lands past the 72-byte header, so the header lemma's values survive. -/
theorem Sim.OperationPtr.allocEmptyImpl_new_op_reads {opCode : OpInfo}
    {ctx₀ : Buffed.IRBufContext}
    {numResults numOperands numBlockOperands numRegions : UInt64} {opType : UInt32}
    {prop : HasDialectOpInfo.propertiesOf opCode}
    {hr ho hbo hreg} {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions opType
      prop hr ho hbo hreg = some (ctxBuf, ptrImpl)) :
    Buffed.OperationMPtr.readNumResults! ctxBuf ptrImpl = numResults ∧
    Buffed.OperationMPtr.readNumOperands! ctxBuf ptrImpl = numOperands ∧
    Buffed.OperationMPtr.readNumBlockOperands! ctxBuf ptrImpl = numBlockOperands ∧
    Buffed.OperationMPtr.readNumRegions! ctxBuf ptrImpl = numRegions ∧
    Buffed.OperationMPtr.readPrev! ctxBuf ptrImpl = Buffed.OperationOPtr.none ∧
    Buffed.OperationMPtr.readNext! ctxBuf ptrImpl = Buffed.OperationOPtr.none ∧
    Buffed.OperationMPtr.readParent! ctxBuf ptrImpl = Buffed.BlockOPtr.none ∧
    Buffed.OperationMPtr.readOpType! ctxBuf ptrImpl = opType ∧
    Buffed.OperationMPtr.readAttrs! ctxBuf ptrImpl = 0 := by
  obtain ⟨ctxH, hH, h₁, h₂, rfl⟩ := allocEmptyImpl_eq h
  obtain ⟨hnr', hno', hnb', hnrg', hprev', hnext', hpar', hty', hattrs'⟩ :=
    allocEmptyHeaderImpl_new_op_reads hH
  have hstep := allocEmptyHeaderImpl_properties_toNat hH
  have haddr := hstep Buffed.Operation.Offsets.properties 72 (by decide) (by omega)
  have h0 := hstep Buffed.Operation.Offsets.numResults 0 (by decide) (by omega)
  have h8 := hstep Buffed.Operation.Offsets.prev 8 (by decide) (by omega)
  have h16 := hstep Buffed.Operation.Offsets.next 16 (by decide) (by omega)
  have h24 := hstep Buffed.Operation.Offsets.parent 24 (by decide) (by omega)
  have h32 := hstep Buffed.Operation.Offsets.opType 32 (by decide) (by omega)
  have h40 := hstep Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by omega)
  have h48 := hstep Buffed.Operation.Offsets.numRegions 48 (by decide) (by omega)
  have h56 := hstep Buffed.Operation.Offsets.numOperands 56 (by decide) (by omega)
  have h64 := hstep Buffed.Operation.Offsets.attrs 64 (by decide) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Buffed.OperationMPtr.readNumResults!] at hnr' ⊢
    rw [HasBuffedProperties.read64!_writePropertyAt (Or.inl
      (show (ptrImpl + Buffed.Operation.Offsets.numResults).toNat + 8
        ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat from by omega))]
    exact hnr'
  · simp only [Buffed.OperationMPtr.readNumOperands!] at hno' ⊢
    rw [HasBuffedProperties.read64!_writePropertyAt (Or.inl
      (show (ptrImpl + Buffed.Operation.Offsets.numOperands).toNat + 8
        ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat from by omega))]
    exact hno'
  · simp only [Buffed.OperationMPtr.readNumBlockOperands!] at hnb' ⊢
    rw [HasBuffedProperties.read64!_writePropertyAt (Or.inl
      (show (ptrImpl + Buffed.Operation.Offsets.numBlockOperands).toNat + 8
        ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat from by omega))]
    exact hnb'
  · simp only [Buffed.OperationMPtr.readNumRegions!] at hnrg' ⊢
    rw [HasBuffedProperties.read64!_writePropertyAt (Or.inl
      (show (ptrImpl + Buffed.Operation.Offsets.numRegions).toNat + 8
        ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat from by omega))]
    exact hnrg'
  · simp only [Buffed.OperationMPtr.readPrev!] at hprev' ⊢
    rw [HasBuffedProperties.read64!_writePropertyAt (Or.inl
      (show (ptrImpl + Buffed.Operation.Offsets.prev).toNat + 8
        ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat from by omega))]
    exact hprev'
  · simp only [Buffed.OperationMPtr.readNext!] at hnext' ⊢
    rw [HasBuffedProperties.read64!_writePropertyAt (Or.inl
      (show (ptrImpl + Buffed.Operation.Offsets.next).toNat + 8
        ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat from by omega))]
    exact hnext'
  · simp only [Buffed.OperationMPtr.readParent!] at hpar' ⊢
    rw [HasBuffedProperties.read64!_writePropertyAt (Or.inl
      (show (ptrImpl + Buffed.Operation.Offsets.parent).toNat + 8
        ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat from by omega))]
    exact hpar'
  · simp only [Buffed.OperationMPtr.readOpType!] at hty' ⊢
    rw [HasBuffedProperties.read32!_writePropertyAt (Or.inl
      (show (ptrImpl + Buffed.Operation.Offsets.opType).toNat + 4
        ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat from by omega))]
    exact hty'
  · simp only [Buffed.OperationMPtr.readAttrs!] at hattrs' ⊢
    rw [HasBuffedProperties.read64!_writePropertyAt (Or.inl
      (show (ptrImpl + Buffed.Operation.Offsets.attrs).toNat + 8
        ≤ (ptrImpl + Buffed.Operation.Offsets.properties).toNat from by omega))]
    exact hattrs'

def Sim.OperationPtr.allocEmptySpec (ctx : Veir.IRContext OpInfo) (addr : Nat) (opType : OpInfo)
    (properties : HasOpInfo.propertiesOf opType) (capResults capBlockOperands capRegions capOperands : Nat)
    : Option (Veir.IRContext OpInfo × Veir.OperationPtr) :=
  OperationPtr.allocEmptyAt ctx opType properties capResults capBlockOperands capRegions capOperands addr

/-- `allocEmptyAt` preserves `FieldsInBounds`: existing objects keep their fields (whose `InBounds` facts transfer since allocation only grows the `InBounds` sets), and the fresh operation is empty, so its clauses are vacuous or trivial. -/
theorem IRContext.fieldsInBounds_OperationPtr_allocEmptyAt {ctx ctx' : IRContext OpInfo}
    {opType : OpInfo} {props : HasOpInfo.propertiesOf opType}
    {capResults capBlockOperands capRegions capOperands addr : Nat} {newOp : OperationPtr}
    (heq : OperationPtr.allocEmptyAt ctx opType props capResults capBlockOperands capRegions
      capOperands addr = some (ctx', newOp))
    (hfib : ctx.FieldsInBounds) : ctx'.FieldsInBounds := by
  constructor
  · intro op opIn
    by_cases hop : op = newOp
    · subst hop
      constructor
      · intro res resIn hres
        exact absurd resIn (OpResultPtr.allocEmptyAt_no_results heq hres)
      · grind [Option.maybe_def, Operation.empty]
      · grind [Option.maybe_def, Operation.empty]
      · grind [Option.maybe_def, Operation.empty]
      · intro bo boIn hbo
        exact absurd boIn (BlockOperandPtr.allocEmptyAt_no_operands heq hbo)
      · grind
      · intro oper operIn hoper
        exact absurd operIn (OpOperandPtr.allocEmptyAt_no_operands heq hoper)
    · have hold := hfib.operations_inBounds op (by grind)
      constructor
      · intro res resIn hres
        have := hold.results_inBounds res (by grind [Veir.OpResultPtr.inBounds_def]) hres
        grind [OpResult.FieldsInBounds, Option.maybe_def, Veir.OpResultPtr.inBounds_def,
          Veir.OpOperandPtr.inBounds_def]
      · have := hold.prev_inBounds
        grind [Option.maybe_def]
      · have := hold.next_inBounds
        grind [Option.maybe_def]
      · have := hold.parent_inBounds
        grind [Option.maybe_def]
      · intro bo boIn hbo
        have := hold.blockOperands_inBounds bo (by grind [Veir.BlockOperandPtr.inBounds_def]) hbo
        grind [BlockOperand.FieldsInBounds, Option.maybe_def, Veir.BlockOperandPtr.inBounds_def]
      · intro i hi
        have := hold.regions_inBounds i (by grind)
        grind
      · intro oper operIn hoper
        have := hold.operands_inBounds oper (by grind [Veir.OpOperandPtr.inBounds_def]) hoper
        grind [OpOperand.FieldsInBounds, Option.maybe_def, Veir.OpOperandPtr.inBounds_def]
  · intro block blockIn
    have hold := hfib.blocks_inBounds block (by grind)
    constructor
    · have := hold.firstUse_inBounds
      grind [Option.maybe_def, Veir.BlockOperandPtr.inBounds_def]
    · have := hold.prev_inBounds
      grind [Option.maybe_def]
    · have := hold.next_inBounds
      grind [Option.maybe_def]
    · have := hold.parent_inBounds
      grind [Option.maybe_def]
    · have := hold.firstOp_inBounds
      grind [Option.maybe_def]
    · have := hold.lastOp_inBounds
      grind [Option.maybe_def]
    · intro arg argIn harg
      have := hold.arguments_inBounds arg (by grind [Veir.BlockArgumentPtr.inBounds_def]) harg
      grind [BlockArgument.FieldsInBounds, Option.maybe_def, Veir.BlockArgumentPtr.inBounds_def,
        Veir.OpOperandPtr.inBounds_def]
  · intro region regionIn
    have hold := hfib.regions_inBounds region (by grind)
    constructor
    · have := hold.firstBlock_inBounds
      grind
    · have := hold.lastBlock_inBounds
      grind
    · have := hold.parent_inBounds
      grind

/-- `allocEmptyAt` preserves `IsRepr` provided the new address and capacities are representable. -/
theorem IRContext.isRepr_OperationPtr_allocEmptyAt {ctx ctx' : IRContext OpInfo}
    {opType : OpInfo} {props : HasOpInfo.propertiesOf opType}
    {capResults capBlockOperands capRegions capOperands addr : Nat} {newOp : OperationPtr}
    (heq : OperationPtr.allocEmptyAt ctx opType props capResults capBlockOperands capRegions
      capOperands addr = some (ctx', newOp))
    (hrepr : ctx.IsRepr) (haddr : addr ≤ Int64.maxNatValue)
    (hc₁ : capResults ≤ Buffed.countCard) (hc₂ : capOperands ≤ Buffed.countCard)
    (hc₃ : capBlockOperands ≤ Buffed.countCard) (hc₄ : capRegions ≤ Buffed.countCard) :
    ctx'.IsRepr := by
  constructor
  · intro op hin
    rcases (OperationPtr.allocEmptyAt_operationPtr_iff op heq).mp hin with h | rfl
    · exact hrepr.operations op h
    · grind [OperationPtr.IsRepr, OperationPtr.toFlat]
  · intro op hin
    by_cases hop : op = newOp
    · subst hop
      constructor <;> grind [Operation.empty]
    · have := hrepr.operations_indices op (by grind)
      constructor <;> grind
  · intro blk hin
    have := hrepr.blocks blk (by grind)
    grind
  · intro blk hin
    have := hrepr.blocks_indices blk (by grind)
    constructor <;> grind
  · intro rg hin
    have := hrepr.regions rg (by grind)
    grind

/-- Existing operations keep their byte range across `allocEmptyAt` (their capacities are unchanged). -/
theorem OperationPtr.range_OperationPtr_allocEmptyAt {ctx ctx' : IRContext OpInfo}
    {opType : OpInfo} {props : HasOpInfo.propertiesOf opType}
    {capResults capBlockOperands capRegions capOperands addr : Nat} {newOp op : OperationPtr}
    (heq : OperationPtr.allocEmptyAt ctx opType props capResults capBlockOperands capRegions
      capOperands addr = some (ctx', newOp))
    (hne : op ≠ newOp) :
    op.range ctx' = op.range ctx := by
  grind [OperationPtr.range]

/-- Blocks keep their byte range across `allocEmptyAt`. -/
theorem BlockPtr.range_OperationPtr_allocEmptyAt {ctx ctx' : IRContext OpInfo}
    {opType : OpInfo} {props : HasOpInfo.propertiesOf opType}
    {capResults capBlockOperands capRegions capOperands addr : Nat} {newOp : OperationPtr}
    {bl : BlockPtr}
    (heq : OperationPtr.allocEmptyAt ctx opType props capResults capBlockOperands capRegions
      capOperands addr = some (ctx', newOp)) :
    bl.range ctx' = bl.range ctx := by
  grind [BlockPtr.range]

/-- Any address at or beyond the end of the buffer is free in the spec: an operation there would have its range escape the buffer, contradicting `in_bounds`. -/
theorem Sim.OperationPtr.slot_free (ctx : Sim.IRContext OpInfo) {a : Nat} (ha : ctx.buf.mem.size ≤ a) :
    ¬ (⟨a⟩ : Veir.OperationPtr).InBounds ctx.spec := by
  intro hin
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) ⟨a⟩ hin
  have : (0 : Int) < Buffed.Operation.Offsets.afterInt (⟨a⟩ : Veir.OperationPtr) ctx.spec := by
    simp only [Buffed.Operation.Offsets.afterInt, Buffed.Operation.Offsets.regionsInt,
      Buffed.Operation.Offsets.blockOperandsInt, Buffed.Operation.Offsets.operandsInt]
    grind
  grind

set_option maxHeartbeats 1000000000 in
/-- Freshly allocating an empty operation — buffer side (`allocEmptyImpl`) and spec side (`allocEmptyAt`, at the same address) — preserves the simulation invariant. -/
theorem Sim.OperationPtr.allocEmpty_sim {ctx : Sim.IRContext OpInfo} {opType : OpInfo}
    {props : HasOpInfo.propertiesOf opType}
    {numResults numOperands numBlockOperands numRegions : UInt64}
    {h₁ : numResults.toNat ≤ countCard} {h₂ : numOperands.toNat ≤ countCard}
    {h₃ : numBlockOperands.toNat ≤ countCard} {h₄ : numRegions.toNat ≤ countCard}
    {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    {ctxSpec : Veir.IRContext OpInfo} {ptrSpec : Veir.OperationPtr}
    (heqImpl : allocEmptyImpl ctx.buf numResults numOperands numBlockOperands numRegions
      (SerializableOpInfo.encode opType)
      (props : HasDialectOpInfo.propertiesOf opType)
      h₁ h₂ h₃ h₄ = some (ctxBuf, ptrImpl))
    (heqSpec : Veir.OperationPtr.allocEmptyAt ctx.spec opType props numResults.toNat
      numBlockOperands.toNat numRegions.toNat numOperands.toNat ptrImpl.toNat
      = some (ctxSpec, ptrSpec)) :
    Veir.Sim (OpInfo := OpInfo) ⟨ctxBuf, .mk ctxSpec⟩ := by
  have hp : (Buffed.Operation.propertySize opType).toNat ≤ countCard :=
    Nat.le_of_lt HasDialectOpInfo.propertySize_small
  have hps : Buffed.Operation.propertySize opType = HasDialectOpInfo.propertySize opType := rfl
  have hattrs : ∀ {i : Nat} {a : Attribute}, ctx.buf.attributes[i]? = some a →
      ctxBuf.attributes[i]? = some a :=
    fun h => Sim.OperationPtr.allocEmptyImpl_attributes heqImpl h
  have hsize := Sim.OperationPtr.allocEmptyImpl_size heqImpl
  rw [← hps] at hsize
  have hge := Sim.OperationPtr.allocEmptyImpl_ptr_ge heqImpl
  have hptn := Sim.OperationPtr.allocEmptyImpl_ptr_toNat heqImpl
  have hro := Sim.OperationPtr.allocEmptyImpl_read_old heqImpl
  have hagree : Buffed.AgreesOn ctxBuf ctx.buf 0 ctx.buf.mem.size :=
    ⟨by omega, fun w a len _ ha => hro w a len ha, fun _ _ h => hattrs h⟩
  obtain ⟨hRnr, hRno, hRnb, hRnrg, hRprev, hRnext, hRpar, hRty, hRattrs⟩ :=
    Sim.OperationPtr.allocEmptyImpl_new_op_reads heqImpl
  have hnew : ptrSpec = ⟨ptrImpl.toNat⟩ := Veir.OperationPtr.allocEmptyAt_ptr_eq heqSpec
  subst hnew
  have hnewIb : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).InBounds ctxSpec :=
    Veir.OperationPtr.allocEmptyAt_new_inBounds heqSpec
  have hget : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec = Veir.Operation.empty opType props
      numResults.toNat numBlockOperands.toNat numRegions.toNat numOperands.toNat := by
    simpa using Veir.OperationPtr.get!_OperationPtr_allocEmptyAt
      (operation := (⟨ptrImpl.toNat⟩ : Veir.OperationPtr)) heqSpec
  have hgetTy : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).getOpType! ctxSpec = opType := by
    simpa using Veir.OperationPtr.getOpType!_OperationPtr_allocEmptyAt
      (operation := (⟨ptrImpl.toNat⟩ : Veir.OperationPtr)) heqSpec
  have hcapR : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capResults = numResults.toNat := by
    rw [hget]; rfl
  have hcapO : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capOperands = numOperands.toNat := by
    rw [hget]; rfl
  have hcapB : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capBlockOperands
      = numBlockOperands.toNat := by rw [hget]; rfl
  have hcapRg : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capRegions
      = numRegions.toNat := by rw [hget]; rfl
  have hlp : ctx.spec.LayoutPreserved ctxSpec := by
    have hni := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
    constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
    · intro op hib
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by grind
      constructor <;>
        grind [Veir.OperationPtr.get!_OperationPtr_allocEmptyAt,
          Veir.OperationPtr.getOpType!_OperationPtr_allocEmptyAt]
    · intro blk hib
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      grind [Veir.BlockPtr.LayoutPreserved, Veir.BlockPtr.get!_OperationPtr_allocEmptyAt]
  have hfree := Sim.OperationPtr.allocEmptyImpl_freeList heqImpl
  have hrgOld : ∀ (q : TopLevelPtr), q.InBounds ctx.spec → q.range ctxSpec = q.range ctx.spec := by
    intro q hq
    try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
    have hni := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
    cases q with
    | operation op =>
      have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by grind
      simpa [TopLevelPtr.range] using Veir.OperationPtr.range_OperationPtr_allocEmptyAt heqSpec hne
    | block bl =>
      simpa [TopLevelPtr.range] using
        Veir.BlockPtr.range_OperationPtr_allocEmptyAt (bl := bl) heqSpec
    | region rg => rfl
  have hfits := ctxBuf.mem.fits_in_memory
  have hfits₀ := ctx.buf.mem.fits_in_memory
  have hszdec := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions (Buffed.Operation.propertySize opType) h₁ h₂ h₃ h₄ hp
  simp only [show Buffed.OpResult.size.toNat = 40 from rfl,
    show Buffed.ptrSize.toNat = 8 from rfl,
    show Buffed.Operation.sizeBase.toNat = 72 from rfl,
    Int64.maxNatValue] at hszdec hsize hptn hfits hfits₀
  have hfib' := IRContext.fieldsInBounds_OperationPtr_allocEmptyAt heqSpec ctx.sim.fieldsInBounds
  have hrepr' := IRContext.isRepr_OperationPtr_allocEmptyAt heqSpec ctx.sim.repr
    (by simp only [Int64.maxNatValue]; omega) h₁ h₂ h₃ h₄
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
  · exact hfib'
  · exact hrepr'
  · -- `in_bounds`
    intro ptr ib
    try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
    rcases (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff ptr heqSpec).mp ib with hold | rfl
    · have hin := ctx.sim.in_bounds ptr hold
      cases ptr with
      | operation op =>
        have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by
          have := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
          grind
        have hrg := Veir.OperationPtr.range_OperationPtr_allocEmptyAt heqSpec hne
        simp only [TopLevelPtr.range] at hin ⊢
        rw [hrg]
        grind [IsIncludedIN, ExArray.range_def]
      | block bl =>
        have hrg := Veir.BlockPtr.range_OperationPtr_allocEmptyAt (bl := bl) heqSpec
        simp only [TopLevelPtr.range] at hin ⊢
        rw [hrg]
        grind [IsIncludedIN, ExArray.range_def]
      | region rg =>
        simp only [TopLevelPtr.range] at hin ⊢
        grind [IsIncludedIN, ExArray.range_def]
    · -- the freshly allocated operation: its range is exactly the block just appended
      clear hro hRnr hRno hRnb hRnrg hRprev hRnext hRpar hRty hRattrs
      simp only [TopLevelPtr.range, Veir.OperationPtr.range_ideal hrepr' hnewIb,
        Veir.OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def,
        Veir.OperationPtr.toFlat, IsIncludedIN, ExArray.range_def]
      grind
  · -- `disjoint_allocs`
    clear hro hRnr hRno hRnb hRnrg hRprev hRnext hRpar hRty hRattrs
    have hnewRange : ∀ (q : TopLevelPtr), q.InBounds ctx.spec →
        IsDisjointI (q.range ctxSpec)
          ((TopLevelPtr.operation (⟨ptrImpl.toNat⟩ : Veir.OperationPtr)).range ctxSpec) := by
      intro q hq
      try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
      have hin := ctx.sim.in_bounds q hq
      rw [hrgOld q hq]
      simp only [TopLevelPtr.range, Veir.OperationPtr.range_ideal hrepr' hnewIb,
        Veir.OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def,
        Veir.OperationPtr.toFlat]
      simp only [IsIncludedIN, ExArray.range_def] at hin
      simp only [IsDisjointI]
      left
      grind
    intro q₁ q₂ ib₁ ib₂ hne
    try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
    rcases (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff q₁ heqSpec).mp ib₁ with h₁old | rfl <;>
      rcases (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff q₂ heqSpec).mp ib₂ with h₂old | rfl
    · have := ctx.sim.disjoint_allocs q₁ q₂ h₁old h₂old hne
      rw [hrgOld q₁ h₁old, hrgOld q₂ h₂old]
      exact this
    · exact hnewRange q₁ h₁old
    · have := hnewRange q₂ h₂old
      grind [IsDisjointI]
    · exact absurd rfl hne
  · -- `encoding_op`
    intro op ib
    try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
    rcases (Veir.OperationPtr.allocEmptyAt_operationPtr_iff op heqSpec).mp ib with hold | rfl
    · -- existing operation: frame each record over the untouched prefix
      have hni := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
      have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by grind
      have henc := ctx.sim.encoding_op op hold
      have hrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op hold
      have hget2 : Veir.OperationPtr.get! op ctxSpec = Veir.OperationPtr.get! op ctx.spec := by
        grind [Veir.OperationPtr.get!_OperationPtr_allocEmptyAt]
      constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · refine OperationPtr.matchesBase_frame ctx op hold henc.toMatchesBase
          (hagree.mono (Nat.zero_le _) (by grind)) hlp (by rw [hget2]) (by rw [hget2])
          (by rw [hget2]) (by rw [hget2])
          (by grind [Veir.OperationPtr.getOpType!_OperationPtr_allocEmptyAt])
          (Veir.OperationPtr.getProperties!_eq_of_OperationPtr_get!_eq hget2) ib
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numBlockOperands_frame ctx op hold henc.numBlockOperands
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget2])
        · intro bo boIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hboIb : bo.InBounds ctx.spec := by grind [Veir.BlockOperandPtr.inBounds_def]
          have hincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboIb
          have hpib := Veir.Sim.BlockOperandPtr.op_inBounds hboIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) bo.op hpib
          refine BlockOperandPtr.matches_frame ctx bo hboIb (henc.blockOperands bo hboIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlp (by grind [layout_grind]) boIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numRegions_frame ctx op hold henc.numRegions
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget2])
        · intro idx idxIn
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hnr : idx < op.getNumRegions! ctx.spec := by
            grind [Veir.OperationPtr.getNumRegions!_OperationPtr_allocEmptyAt]
          have hcap := ctx.sim.repr.operations_indices op hold |>.capRegions
          refine OperationPtr.nthRegion_frame ctx op hold idx hnr (henc.regions idx hnr)
            (hagree.mono (Nat.zero_le _) (by grind)) ?_ (by grind [layout_grind])
          have hidxc : idx < (op.get! ctx.spec).capRegions := by grind
          have haddrR : (op.toM.toNat : Int) = op.id := by
            grind [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
          have hincl := OperationPtr.nthRegion_range_included_op_range ctx op idx.toUInt64 (by grind) hold
          exact hagree.mono (Nat.zero_le _) (by grind [IsIncludedI, UInt64.toNat_ofNat'])
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numOperands_frame ctx op hold henc.numOperands
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget2])
        · intro oper operIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hooIb : oper.InBounds ctx.spec := by grind [Veir.OpOperandPtr.inBounds_def]
          have hincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hooIb
          have hpib := Veir.Sim.OpOperandPtr.op_inBounds hooIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) oper.op hpib
          refine OpOperandPtr.matches_frame ctx oper hooIb (henc.operands oper hooIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlp (by grind [layout_grind]) operIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact OperationPtr.numResults_frame ctx op hold henc.numResults
            (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget2])
        · intro res resIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          have hresIb : res.InBounds ctx.spec := by grind [Veir.OpResultPtr.inBounds_def]
          have hincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresIb
          have hpib := Veir.Sim.OpResultPtr.op_inBounds hresIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) res.op hpib
          refine OpResultPtr.matches_frame ctx res hresIb (henc.results res hresIb heq)
            (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlp (by grind [layout_grind]) resIb
    · -- the freshly allocated operation: every field reads back what `allocEmptyImpl` wrote
      have hnewToM : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).toM = ptrImpl := by
        simp [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
      clear hro
      constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · grind [Buffed.OperationMPtr.readPrev!, Veir.Operation.empty,
            Veir.OperationPtr.toO]
        · grind [Buffed.OperationMPtr.readNext!, Veir.Operation.empty,
            Veir.OperationPtr.toO]
        · grind [Buffed.OperationMPtr.readParent!, Veir.Operation.empty,
            Veir.BlockPtr.toO]
        · grind [SerializableOpInfo.decode_encode]
        · -- `attrs`: the zero-initialized index denotes the canonical empty dictionary
          have hae := ctx.sim.attr_empty
          rw [hnewToM, hRattrs, hget]
          exact hattrs (by simpa [Veir.Operation.empty] using hae)
        · -- `props`: the property slot reads back what `writePropertyAt` wrote
          have hrp := Sim.OperationPtr.allocEmptyImpl_readProperty heqImpl
          have hgp : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).getProperties! ctxSpec opType = props := by
            rw [Veir.OperationPtr.getProperties!_OperationPtr_allocEmptyAt heqSpec, ite_eq_left rfl]
          rw [Erased.out_mk, hgetTy, hnewToM, hgp]
          exact hrp
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · grind
        · intro bo boIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          exact absurd boIb (Veir.BlockOperandPtr.allocEmptyAt_no_operands heqSpec heq)
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · grind
        · intro idx idxIn
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          grind
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · grind
        · intro oper operIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          exact absurd operIb (Veir.OpOperandPtr.allocEmptyAt_no_operands heqSpec heq)
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · grind
        · intro res resIb heq
          try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
          exact absurd resIb (Veir.OpResultPtr.allocEmptyAt_no_results heqSpec heq)
  · -- `encoding_block`: every block is old; frame each record over the untouched prefix.
    intro blk blkIb
    try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
    have hold : blk.InBounds ctx.spec := by
      have := (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff (.block blk) heqSpec).mp (by grind)
      grind
    have henc := ctx.sim.encoding_block blk hold
    have hrange := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk hold
    have hget2 : Veir.BlockPtr.get! blk ctxSpec = Veir.BlockPtr.get! blk ctx.spec := by
      grind [Veir.BlockPtr.get!_OperationPtr_allocEmptyAt]
    constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
    · refine BlockPtr.matchesBase_frame ctx blk hold henc.toMatchesBase
        (hagree.mono (Nat.zero_le _) (by grind)) hlp (by rw [hget2]) (by rw [hget2])
        (by rw [hget2]) (by rw [hget2]) (by rw [hget2]) (by rw [hget2]) blkIb
    · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · exact BlockPtr.numArguments_frame ctx blk hold henc.numArguments
          (hagree.mono (Nat.zero_le _) (by grind)) (by rw [hget2])
      · intro arg argIn heq
        try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
        have hargIb : arg.InBounds ctx.spec := by grind [Veir.BlockArgumentPtr.inBounds_def]
        have hincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargIb
        have hpib := Veir.Sim.BlockArgumentPtr.block_inBounds hargIb
        have hprangeS := Veir.Sim.BlockPtr.range_linear (ctx := ctx) arg.block hpib
        refine BlockArgumentPtr.matches_frame ctx arg hargIb (henc.arguments arg hargIb heq)
          (hagree.mono (Nat.zero_le _) (by grind [IsIncludedI])) hlp (by grind [layout_grind]) argIn
  · -- `encoding_region`: every region is old; frame the 24-byte record.
    intro rg rgIb
    try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
    have hold : rg.InBounds ctx.spec := by
      have := (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff (.region rg) heqSpec).mp (by grind)
      grind
    have henc := ctx.sim.encoding_region rg hold
    have hrange := Veir.Sim.RegionPtr.range_linear (ctx := ctx) rg hold
    refine RegionPtr.matches_frame ctx rg hold henc
      (hagree.mono (Nat.zero_le _) (by grind)) hlp (by grind [layout_grind]) rgIb
  · -- `attr_empty`
    exact hattrs ctx.sim.attr_empty

  · rw [hfree]
    apply ctx.sim.free_valid.mono
    change ctx.buf.mem.size ≤ ctxBuf.mem.size
    omega
  · intro size address hm p hp
    try simp only [Sim.RawIRContext.spec, Erased.out_mk] at *
    rw [hfree] at hm
    rcases (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff p heqSpec).mp hp with hold | rfl
    · rw [hrgOld p hold]
      exact ctx.sim.free_disjoint size address hm p hold
    · have hb := (ctx.sim.free_valid.bounds size address hm).2
      right
      simp only [TopLevelPtr.range, Veir.OperationPtr.range_ideal hrepr' hnewIb,
        Veir.OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def,
        Veir.OperationPtr.toFlat]
      grind

@[inline]
def Sim.OperationPtr.allocEmpty (ctx : Sim.IRContext OpInfo) (opType : OpInfo)
    (properties : HasOpInfo.propertiesOf opType)
    (numResults numOperands numBlockOperands numRegions : UInt64)
    (h₁ : numResults.toNat ≤ countCard) (h₂ : numOperands.toNat ≤ countCard)
    (h₃ : numBlockOperands.toNat ≤ countCard) (h₄ : numRegions.toNat ≤ countCard) :
    Option (Sim.OperationPtr × Sim.IRContext OpInfo) :=
  match heqImpl : allocEmptyImpl ctx.buf numResults numOperands numBlockOperands numRegions
        (SerializableOpInfo.encode opType)
        (properties : HasDialectOpInfo.propertiesOf opType)
        h₁ h₂ h₃ h₄ with
    | none => none
    | some (ctxBuf, ptrImpl) =>
      -- The spec-side allocation succeeds: the new pointer lies at/past the old buffer end, so its address is free in the spec.
      have hsome : (allocEmptySpec ctx.spec ptrImpl.toNat opType properties
          numResults.toNat numBlockOperands.toNat numRegions.toNat numOperands.toNat).isSome := by
        have hge := Sim.OperationPtr.allocEmptyImpl_ptr_ge heqImpl
        have hfree := Sim.OperationPtr.slot_free ctx hge
        simp only [Veir.OperationPtr.inBounds_def] at hfree
        exact Veir.OperationPtr.allocEmptyAt_isSome_of_not_mem hfree
      let specRes := ctx.spec'.map (fun spec => (allocEmptySpec spec ptrImpl.toNat opType properties
        numResults.toNat numBlockOperands.toNat numRegions.toNat numOperands.toNat).get!)
      some ⟨⟨ptrImpl, specRes.map Prod.snd⟩, ⟨ctxBuf, specRes.map Prod.fst, by
        rw [Erased.map_eq_mk]
        refine Sim.OperationPtr.allocEmpty_sim (props := properties) (ptrSpec := specRes.out.2) heqImpl ?_
        -- The successful spec allocation supplies both the context and the pointer.
        simpa only [specRes, Erased.map_out, Sim.IRContext.spec, Option.get!, allocEmptySpec] using
          (Option.some_get! _ hsome).symm⟩⟩

/-- Strengthening of `allocEmpty_spec`: the spec-level operation is allocated exactly at the address of the returned impl pointer. -/
theorem Sim.OperationPtr.allocEmpty_spec' {ctx : Sim.IRContext OpInfo} :
    allocEmpty ctx opType props c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some ⟨ptr, ctx'⟩ →
    Veir.OperationPtr.allocEmptyAt ctx.spec opType props c₁.toNat c₃.toNat c₄.toNat c₂.toNat ptr.impl.toNat = some ⟨ctx'.spec, ptr.spec⟩ := by
  unfold Sim.OperationPtr.allocEmpty allocEmptySpec
  split
  · intro h; exact absurd h (by simp)
  · rename_i ptrImpl heqImpl
    intro h
    have hge := Sim.OperationPtr.allocEmptyImpl_ptr_ge heqImpl
    have hfree := Sim.OperationPtr.slot_free ctx hge
    simp only [Veir.OperationPtr.inBounds_def] at hfree
    have hsome := Veir.OperationPtr.allocEmptyAt_isSome_of_not_mem
      (opType := opType) (properties := props) (capResults := c₁.toNat)
      (capBlockOperands := c₃.toNat) (capRegions := c₄.toNat) (capOperands := c₂.toNat) hfree
    simp_all only [Option.some.injEq, Prod.mk.injEq]
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    simp only [Option.get!]
    grind

@[grind! .]
theorem Sim.OperationPtr.allocEmpty_spec {ctx : Sim.IRContext OpInfo} :
    allocEmpty ctx opType props c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some ⟨ptr, ctx'⟩ →
    ∃ addr, Veir.OperationPtr.allocEmptyAt ctx.spec opType props c₁.toNat c₃.toNat c₄.toNat c₂.toNat addr = some ⟨ctx'.spec, ptr.spec⟩:=
  fun h => ⟨ptr.impl.toNat, Sim.OperationPtr.allocEmpty_spec' h⟩
