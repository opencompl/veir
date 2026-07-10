module

public meta import Veir.IR.Buffed.Meta
public import Veir.IR.Buffed.Sim
public import Veir.IR.Basic
public import Veir.IR.WellFormed
import Veir.IR.InBounds
import Veir.IR.LayoutUnchanged
import Veir.IR.GetSet
import Veir.IR.Buffed.Meta
import Veir.IR.Buffed.RawAccessorsLemmas
import Veir.IR.Buffed.RawReadWriteLemmas

import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs
import all Veir.IR.Buffed.Sim
-- Exposes the body of `dbgTrace` so the `dump*` printers (which use `dbg_trace`)
-- can be proved to leave the context unchanged (`dbgTrace s (fun _ => x)` reduces to `x`).
import all Init.Util


public section

namespace Veir

open Buffed (countCard)

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]

/- Shared `Sim` proof for `OperationPtr` setters that write a single link field
(`setNextOpSim`, `setPrevOpSim`, …). The only thing that varies between them is the
`Buffed.OperationMPtr.write*` lemma unfolded by `grind`, passed as `$w`.

`hygiene false` so the global grind lemma-set name `layout_grind` (and the other
lemma idents) resolve at the use site instead of being tagged with macro scopes. -/
set_option hygiene false in
macro "prove_setLinkSim" ctx:ident w:Lean.Parser.Tactic.grindParam : tactic => `(tactic|
  (constructor
   · grind
   · grind [layout_grind]
   · simp only
     intros gptr gptrIb
     have := ($ctx).sim.in_bounds gptr (by grind)
     grind [TopLevelPtr]
   · simp only
     have := ($ctx).sim.disjoint_allocs
     grind [TopLevelPtr]
   · simp only
     intros op opIb
     have := ($ctx).sim.encoding_op op (by grind)
     constructor
     · constructor
       · have := this.prev
         grind [layout_grind]
       · have := this.next
         grind [layout_grind]
       · have := this.parent
         grind [layout_grind]
       · have := this.opType
         grind [layout_grind]
       · have := this.attrs
         grind [layout_grind, $w]
     · constructor
       · have := this.numBlockOperands
         grind [layout_grind]
       · intros bo boIb heq
         have := this.blockOperands bo (by grind) (by grind)
         constructor
         · have := this.nextUse
           grind [layout_grind]
         · have := this.back
           grind [layout_grind]
         · have := this.owner
           grind [layout_grind]
         · have := this.value
           grind [layout_grind]
     · constructor
       · grind [layout_grind, OperationPtr.Matches, OperationPtr.MatchesRegions]
       · intros idx idxIn
         have := ctx.sim.encoding_op op (by grind) |>.regions idx (by grind)
         have := ctx.sim.repr.operations_indices op (by grind) |>.capRegions
         grind [layout_grind, UInt64.toNat_ofNat', OperationPtr.Matches, OperationPtr.MatchesRegions]
     · constructor
       · grind [layout_grind, OperationPtr.Matches, OperationPtr.MatchesOperands]
       · intros oper operIb heq
         have := ctx.sim.encoding_op op (by grind) |>.operands oper (by grind) (by grind)
         constructor
         · have := this.nextUse
           grind [layout_grind]
         · have := this.back
           grind [layout_grind]
         · have := this.owner
           grind [layout_grind]
         · have := this.value
           grind [layout_grind]
     · constructor
       · grind [layout_grind, OperationPtr.Matches, OperationPtr.MatchesResults]
       · intros res resIb heq
         have := ctx.sim.encoding_op op (by grind) |>.results res (by grind) (by grind)
         constructor
         · have := this.kind
           grind [layout_grind]
         · have := this.typee -- todo lol
           grind [layout_grind, $w]
         · have := this.firstUse
           grind [layout_grind]
         · have := this.index
           grind [layout_grind]
         · have := this.owner
           grind [layout_grind]
   · simp only
     intros blk blkIb
     have := ($ctx).sim.encoding_block blk (by grind)
     constructor
     · constructor <;> grind [layout_grind, BlockPtr.Matches, BlockPtr.MatchesBase]
     · constructor
       · grind [layout_grind, BlockPtr.Matches, BlockPtr.MatchesArguments]
       · intros arg argIn heq
         have := this.arguments arg (by grind) (by grind)
         constructor
         · have := this.kind
           grind [layout_grind]
         · have := this.type
           grind [layout_grind, $w]
         · have := this.firstUse
           grind [layout_grind]
         · have := this.index
           grind [layout_grind]
         · have := this.owner
           grind [layout_grind]
   · simp only
     intros rg rgIb
     have := ($ctx).sim.encoding_region rg (by grind)
     constructor
     · have := this.firstBlock
       grind [layout_grind]
     · have := this.lastBlock
       grind [layout_grind]
     · have := this.parent
       grind [layout_grind]
   · have := ($ctx).sim.attr_empty
     grind [$w]))

/- Shared bounds proofs passed to the `Buffed.*MPtr.write*` calls in the setters.
Each discharges the goal `(ptr.impl + offset).toInt + size.toInt ≤ ↑ctx.buf.size`
by establishing that the pointer's whole range lies in the buffer, then bounding the
size. `$ctx` and `$ptr` are the setter's context and pointer.

There is one macro per pointer type because the range-inclusion argument differs:
top-level pointers (`OperationPtr`, `BlockPtr`, `RegionPtr`, `ValuePtr`) are
directly `in_bounds`, while sub-pointers (`OpOperandPtr`, `OpResultPtr`,
`BlockOperandPtr`, `BlockArgumentPtr`) chain through their containing op/block via
the corresponding `range_included_*` lemma.

`hygiene false` so `IsIncludedIN` and the `grind` lemma idents resolve at the use
site (matches `prove_setLinkSim`). -/
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

/- Bounds proof for reading the `$index`-th region *slot* of an operation
(`readNthRegion`'s `h₂`): the slot lies inside the op's byte range
(`nthRegion_range_included_op_range`), which in turn lies in the buffer
(`sim.in_bounds`). Expects `hindex : ($index).toNat < ($ptr).spec.getNumRegions! ($ctx).spec`
(or enough for `grind` to derive it) in scope; `capRegions` bounds `getNumRegions!`
via `ReprIndices`. -/
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

/- Bounds proofs for writing the `$index`-th result/operand/block-operand slot of an operation
(the `hslot` argument of `Rewriter.set{Result,Operand,BlockOperand}`), and the `$index`-th
argument slot of a block (`Rewriter.setBlockArgument`'s `hslot`). Each follows the
`prove_setLinkBoundsRegionSlot` recipe: the slot lies inside the owner's byte range
(`nth*_range_included_*_range`, capacity-based), which lies in the buffer (`sim.in_bounds`).
Expects `hcap : ($index).toNat < (($ptr).spec.get! ($ctx).spec).cap<Kind>` (or enough for
`grind` to derive it) in scope — at the `Rewriter.push*At` sites this is the threaded
capacity precondition. -/
set_option hygiene false in
macro "prove_setLinkBoundsResultSlot" ctx:ident ptr:ident index:ident : tactic => `(tactic|
  (have hcap : ($index).toNat < (($ptr).spec.get! ($ctx).spec).capResults := by grind
   have hincl := OperationPtr.nthResult_range_included_op_range $ctx ($ptr).spec $index hcap (by grind)
   have hin := ($ctx).sim.in_bounds (.operation ($ptr).spec) (by grind)
   have : ($ctx).buf.mem.size < 2^63 := by grind
   -- Pin the nonlinear pieces grind won't derive itself: the ideal form of the base offset,
   -- `idx < 2^32` (via `ReprIndices`), and the `UInt64` multiplication in `Nat` form.
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

/- Bounds proof for the `Buffed.*MPtr.write*` calls inside the `allocEmptyImpl`
functions. Unlike the setters above these operate on a raw `Buffed.IRBufContext`
just after `$ctx₀.alloc size`, so there is no `Sim` structure to appeal to. Instead
the field's `[offset, offset+size)` range fits because it lies inside the freshly
allocated block: the goal is `(ptr + off).toInt + fsize.toInt ≤ ctx.size`, where the
caller has a `hsize : ctx.size = ($ctx₀).size + size.toNat` in scope. The pointer is
`($ctx₀).usize`, so `ptr.toNat = ($ctx₀).size` (`usize_toNat`), the buffer size is
bounded by `fits_in_memory`, and the pointer-arithmetic decomposition
`uint64_add_int64_toInt_lt` turns the goal into linear arithmetic that `grind`
finishes once the field constants (all reducible) unfold. -/
set_option hygiene false in
macro "prove_allocBounds" ctx₀:ident : tactic => `(tactic|
  (have hb := ($ctx₀).mem.fits_in_memory
   have hu := ($ctx₀).usize_toNat
   -- Collapse `.size` to `.mem.size` and use the `write*_size` lemmas to peel the chain of
   -- writes down to the just-allocated buffer, exposing the `hsize`/`hbsize` size facts. The
   -- pointer arithmetic (`uint64_add_int64_toInt_lt`) then reduces the goal to linear
   -- arithmetic over `Nat`.
   simp only [Buffed.IRBufContext.size_def] at *
   grind (instances := 4000) [UInt64.uint64_add_int64_toInt_lt, Buffed.BlockMPtr.writeNumArguments_size,
     Buffed.BlockMPtr.writeFirstUse_size, Buffed.BlockMPtr.writePrev_size, Buffed.BlockMPtr.writeNext_size,
     Buffed.BlockMPtr.writeParent_size, Buffed.BlockMPtr.writeFirstOp_size, Buffed.BlockMPtr.writeLastOp_size,
     Buffed.RegionMPtr.writeParent_size, Buffed.RegionMPtr.writeFirstBlock_size, Buffed.RegionMPtr.writeLastBlock_size,
     Buffed.OperationMPtr.writeNumResults_size, Buffed.OperationMPtr.writeNumOperands_size,
     Buffed.OperationMPtr.writeNumBlockOperands_size, Buffed.OperationMPtr.writeNumRegions_size,
     Buffed.OperationMPtr.writeParent_size, Buffed.OperationMPtr.writeNext_size, Buffed.OperationMPtr.writePrev_size]))

/- Variant of `prove_allocBounds` for `OperationPtr.allocEmptyImpl`. The operation pointer is
`($ctx₀).usize + OpResult.size * numResults` (it points past the back-allocated results array),
so the goal has an extra `UInt64` addition to unfold; `$nres` is `numResults`, and the caller
has both `hsize` and the `computeOperationSize` decomposition `hopsize` in scope. The
`OpResult.size * numResults` term in the pointer cancels against the same term in the size, so
grind closes the resulting linear-arithmetic goal. -/
set_option hygiene false in
macro "prove_allocBoundsOp" ctx₀:ident : tactic => `(tactic|
  (have hb := ($ctx₀).mem.fits_in_memory
   -- The caller established `hptr` (closed form of the operation pointer's address) and
   -- `hptrlt` (its `< 2^63` bound); grind unfolds the `let`-bound pointer uniformly in both the
   -- goal and these facts, so the pointer-arithmetic decomposition applies and the goal reduces
   -- to linear arithmetic over the just-allocated size (`hsize`/`hopsize`/`hprefix`).
   simp only [Buffed.IRBufContext.size_def] at *
   grind (instances := 4000) [UInt64.uint64_add_int64_toInt_lt,
     Buffed.OperationMPtr.writeNumResults_size, Buffed.OperationMPtr.writeNumOperands_size,
     Buffed.OperationMPtr.writeNumBlockOperands_size, Buffed.OperationMPtr.writeNumRegions_size,
     Buffed.OperationMPtr.writeParent_size, Buffed.OperationMPtr.writeNext_size,
     Buffed.OperationMPtr.writePrev_size, Buffed.OperationMPtr.writeOpType_size]))

/- Bounds proof for the field `write*` calls inside the raw `Rewriter.set{Result,Operand,
BlockOperand}` setters. These write into a slot pointer (an `OpResult`/`OpOperand`/`BlockOperand`
`MPtr`) of an *existing* operation, built with the proof-free `!` offset so the caller supplies
only `hslot` — the whole slot `[slot, slot + <slot>.size)` fits in the buffer — plus, in
`setResult`, `hsz`, that the intervening `insertAttrs` left the size unchanged. Each field
write's `(slot + off).toInt + fsize ≤ size` follows because the field lies inside the slot;
`fits_in_memory` rules out address wrap and `uint64_add_int64_toInt_lt` decomposes the pointer
arithmetic. The `write*_size` lemmas collapse `.size` through the chain of earlier writes. -/
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
/-
@[inline]
def dumpOp (_op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpRegion (_region : Sim.RegionPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpBlock (_block : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpValue (_value : Sim.ValuePtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOpResult (_result : Sim.OpResultPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpBlockArgument (_arg : Sim.BlockArgumentPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOpOperand (_operand : Sim.OpOperandPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpBlockOperand (_operand : Sim.BlockOperandPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

/-! ### Nullable (`Option*Ptr`) dumpers — print `null` for the sentinel. -/

@[inline]
def dumpOptionOp (_op : Sim.OptionOperationPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOptionBlock (_block : Sim.OptionBlockPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOptionRegion (_region : Sim.OptionRegionPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOptionOpOperand (_operand : Sim.OptionOpOperandPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOptionBlockOperand (_operand : Sim.OptionBlockOperandPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx
-/

buffed
def dumpOpSim (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨op.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.OperationMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOp_eq (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOp op ctx pref = ctx := by
  simp only [dumpOp, Buffed.OperationMPtr.debugPrint]; congr 1

buffed
def dumpRegionSim (region : Sim.RegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨region.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.RegionMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpRegion_eq (region : Sim.RegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpRegion region ctx pref = ctx := by
  simp only [dumpRegion, Buffed.RegionMPtr.debugPrint]; congr 1

buffed
def dumpBlockSim (block : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨block.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.BlockMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpBlock_eq (block : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpBlock block ctx pref = ctx := by
  simp only [dumpBlock, Buffed.BlockMPtr.debugPrint]; congr 1

buffed
def dumpValueSim (value : Sim.ValuePtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨value.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.ValueImplMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpValue_eq (value : Sim.ValuePtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpValue value ctx pref = ctx := by
  simp only [dumpValue, Buffed.ValueImplMPtr.debugPrint]; congr 1

buffed
def dumpOpResultSim (result : Sim.OpResultPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨result.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.OpResultMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOpResult_eq (result : Sim.OpResultPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOpResult result ctx pref = ctx := by
  simp only [dumpOpResult, Buffed.OpResultMPtr.debugPrint]; congr 1

buffed
def dumpBlockArgumentSim (arg : Sim.BlockArgumentPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨arg.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.BlockArgumentMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpBlockArgument_eq (arg : Sim.BlockArgumentPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpBlockArgument arg ctx pref = ctx := by
  simp only [dumpBlockArgument, Buffed.BlockArgumentMPtr.debugPrint]; congr 1

buffed
def dumpOpOperandSim (operand : Sim.OpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.OpOperandMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOpOperand_eq (operand : Sim.OpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOpOperand operand ctx pref = ctx := by
  simp only [dumpOpOperand, Buffed.OpOperandMPtr.debugPrint]; congr 1

buffed
def dumpBlockOperandSim (operand : Sim.BlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.BlockOperandMPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpBlockOperand_eq (operand : Sim.BlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpBlockOperand operand ctx pref = ctx := by
  simp only [dumpBlockOperand, Buffed.BlockOperandMPtr.debugPrint]; congr 1

/-! ### Nullable (`Option*Ptr`) dumpers — print `null` for the sentinel. -/

buffed
def dumpOptionOpSim (op : Sim.OptionOperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨op.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.OperationOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionOp_eq (op : Sim.OptionOperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionOp op ctx pref = ctx := by
  simp only [dumpOptionOp, Buffed.OperationOPtr.debugPrint]; congr 1

buffed
def dumpOptionBlockSim (block : Sim.OptionBlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨block.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.BlockOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionBlock_eq (block : Sim.OptionBlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionBlock block ctx pref = ctx := by
  simp only [dumpOptionBlock, Buffed.BlockOPtr.debugPrint]; congr 1

buffed
def dumpOptionRegionSim (region : Sim.OptionRegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨region.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.RegionOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionRegion_eq (region : Sim.OptionRegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionRegion region ctx pref = ctx := by
  simp only [dumpOptionRegion, Buffed.RegionOPtr.debugPrint]; congr 1

buffed
def dumpOptionOpOperandSim (operand : Sim.OptionOpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.OpOperandOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionOpOperand_eq (operand : Sim.OptionOpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionOpOperand operand ctx pref = ctx := by
  simp only [dumpOptionOpOperand, Buffed.OpOperandOPtr.debugPrint]; congr 1

buffed
def dumpOptionBlockOperandSim (operand : Sim.OptionBlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec, by rw [Buffed.BlockOperandOPtr.debugPrint_eq]; exact ctx.sim⟩

@[simp, grind =]
theorem dumpOptionBlockOperand_eq (operand : Sim.OptionBlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String) :
    dumpOptionBlockOperand operand ctx pref = ctx := by
  simp only [dumpOptionBlockOperand, Buffed.BlockOperandOPtr.debugPrint]; congr 1


/-! ## Setters and getters -/


buffed
def Sim.OperationPtr.setNextOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNext ctx.buf next.impl (by prove_setLinkBoundsOp ctx ptr),
    ptr.spec.setNextOp ctx.spec next.spec (by grind), by
    prove_setLinkSim ctx Buffed.OperationMPtr.writeNext⟩

open Classical in
noncomputable def Sim.OperationPtr.setNextOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Operation.Offsets.next).toInt + Buffed.Operation.Sizes.next.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OperationMPtr.writeNext ctx.buf ptr.impl next.impl h₁,
      spec := ptr.spec.setNextOp! ctx.spec next.spec } then
    ⟨ptr.impl.writeNext ctx.buf next.impl h₁, ptr.spec.setNextOp! ctx.spec next.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.setNextOp_eq_setNextOp! (ctx : IRContext OpInfo) ptr next ib nextIb :
    setNextOp ctx ptr next ib nextIb = setNextOp! ctx ptr next := by
  simp [setNextOp_def, setNextOpSim, setNextOp!]
  split
  · grind
  · prove_setLinkBoundsOp ctx ptr

buffed
def Sim.OperationPtr.getNextOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readNext ctx.buf (by prove_setLinkBoundsOp ctx ptr), (ptr.spec.get ctx.spec).next⟩

@[grind .]
theorem Sim.OperationPtr.getNextOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getNextOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).next
  grind [getNextOpSim, getNextOp_def]

@[simp, grind =]
theorem Sim.OperationPtr.getNextOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getNextOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).next := by
  rfl

buffed
def Sim.OperationPtr.getNextOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readNext! ctx.buf, (ptr.spec.get! ctx.spec).next⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNextOp_eq_getNextOp! (ctx : IRContext OpInfo) ptr ib :
    getNextOp ctx ptr ib = getNextOp! ctx ptr := by
  simp [getNextOp_def, getNextOpSim, getNextOp!_def, getNextOp!Sim]
  grind

@[inline]
def Sim.OperationPtr.getOpType (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : OpInfo :=
  SerializableOpInfo.decode (ptr.impl.readOpType ctx.buf (by prove_setLinkBoundsOp ctx ptr))

@[inline]
def Sim.OperationPtr.getOpType! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : OpInfo :=
  SerializableOpInfo.decode (ptr.impl.readOpType! ctx.buf)

buffed
def Sim.OperationPtr.setPrevOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writePrev ctx.buf prev.impl (by prove_setLinkBoundsOp ctx ptr), ptr.spec.setPrevOp ctx.spec prev.spec (by grind), by
    prove_setLinkSim ctx Buffed.OperationMPtr.writePrev ⟩

open Classical in
noncomputable def Sim.OperationPtr.setPrevOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Operation.Offsets.prev).toInt + Buffed.Operation.Sizes.prev.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OperationMPtr.writePrev ctx.buf ptr.impl prev.impl h₁,
      spec := ptr.spec.setPrevOp! ctx.spec prev.spec } then
    ⟨ptr.impl.writePrev ctx.buf prev.impl h₁, ptr.spec.setPrevOp! ctx.spec prev.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.setPrevOp_eq_setPrevOp! (ctx : IRContext OpInfo) ptr prev ib prevIb :
    setPrevOp ctx ptr prev ib prevIb = setPrevOp! ctx ptr prev := by
  simp [setPrevOp_def, setPrevOpSim, setPrevOp!]
  split
  · grind
  · prove_setLinkBoundsOp ctx ptr

@[simp, grind =]
theorem Sim.OperationPtr.setNextOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextOp ctx ptr next ib nextIb).spec = ptr.spec.setNextOp ctx.spec next.spec := by
  rfl

@[simp, grind =]
theorem Sim.OperationPtr.setNextOp!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextOp! ctx ptr next).spec = ptr.spec.setNextOp! ctx.spec next.spec := by
  grind

buffed
def Sim.OperationPtr.getPrevOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readPrev ctx.buf (by prove_setLinkBoundsOp ctx ptr), (ptr.spec.get ctx.spec).prev⟩

@[simp, grind =]
theorem Sim.OperationPtr.getPrevOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).prev := by
  rfl

@[grind .]
theorem Sim.OperationPtr.getPrevOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).prev
  grind [getPrevOpSim, getPrevOp_def]

buffed
def Sim.OperationPtr.getPrevOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readPrev! ctx.buf, (ptr.spec.get! ctx.spec).prev⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getPrevOp_eq_getPrevOp! (ctx : IRContext OpInfo) ptr ib :
    getPrevOp ctx ptr ib = getPrevOp! ctx ptr := by
  simp [getPrevOp_def, getPrevOpSim, getPrevOp!_def, getPrevOp!Sim]
  grind

buffed
def Sim.OperationPtr.setParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl (by prove_setLinkBoundsOp ctx ptr), ptr.spec.setParent ctx.spec parent.spec (by grind), by prove_setLinkSim ctx Buffed.OperationMPtr.writeParent⟩

open Classical in
noncomputable def Sim.OperationPtr.setParent! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Operation.Offsets.parent).toInt + Buffed.Operation.Sizes.parent.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OperationMPtr.writeParent ctx.buf ptr.impl parent.impl h₁,
      spec := ptr.spec.setParent! ctx.spec parent.spec } then
    ⟨ptr.impl.writeParent ctx.buf parent.impl h₁, ptr.spec.setParent! ctx.spec parent.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.setParent_eq_setParent! (ctx : IRContext OpInfo) ptr parent ib parentIb :
    setParent ctx ptr parent ib parentIb = setParent! ctx ptr parent := by
  simp [setParent_def, setParentSim, setParent!]
  split
  · grind
  · prove_setLinkBoundsOp ctx ptr

@[simp, grind =]
theorem Sim.OperationPtr.setPrevOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevOp ctx ptr prev ib prevIb).spec = ptr.spec.setPrevOp ctx.spec prev.spec := by
  rfl

@[simp, grind =]
theorem Sim.OperationPtr.setPrevOp!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevOp! ctx ptr prev).spec = ptr.spec.setPrevOp! ctx.spec prev.spec := by
  grind

buffed
def Sim.OperationPtr.getParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readParent ctx.buf (by prove_setLinkBoundsOp ctx ptr), (ptr.spec.get ctx.spec).parent⟩

@[simp, grind =]
theorem Sim.OperationPtr.getParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).spec = (ptr.spec.get ctx.spec).parent := by
  rfl

@[grind .]
theorem Sim.OperationPtr.getParent_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).parent
  grind [getParentSim, getParent_def]

buffed
def Sim.OperationPtr.getParent!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readParent! ctx.buf, (ptr.spec.get! ctx.spec).parent⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getParent_eq_getParent! (ctx : IRContext OpInfo) ptr ib :
    getParent ctx ptr ib = getParent! ctx ptr := by
  simp [getParent_def, getParentSim, getParent!_def, getParent!Sim]
  grind

@[simp, grind =]
theorem Sim.OperationPtr.setParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent ctx ptr parent ib parentIb).spec = ptr.spec.setParent ctx.spec parent.spec := by
  rfl

@[simp, grind =]
theorem Sim.OperationPtr.setParent!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent! ctx ptr parent).spec = ptr.spec.setParent! ctx.spec parent.spec := by
  grind

set_option maxHeartbeats 1000000000 in
buffed
def Sim.OperationPtr.setAttributesSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (attrs : DictionaryAttr) (_ib : ptr.InBounds ctx) : Option (Sim.IRContext OpInfo) := do
  match _ : ctx with
  | ⟨ctxBuf', ctxSpec, ctxSim⟩ =>
    rlet ⟨ctxBuf, idx⟩ ← ctxBuf'.insertAttrs attrs
    some ⟨ptr.impl.writeAttrs ctxBuf idx (by
      have incl : IsIncludedIN ((ptr).spec.range (ctx).spec) (ctx).buf.mem.range := by
        have := ctx.sim.in_bounds (.operation (ptr).spec)
        grind
      have : ctxBuf.mem.size < 2^63 := by grind
      grind [layout_grind, Buffed.IRBufContext.insertAttrs]),
    ptr.spec.setAttributes ctxSpec attrs (by grind), by
   have := ctx.sim.in_bounds (.operation ptr.spec) (by grind)
   have : ctx.buf.mem.size < 2^63 := by grind
   constructor
   · grind
   · grind [layout_grind]
   · simp only
     intros gptr gptrIb
     have := ctx.sim.in_bounds gptr (by grind)
     grind [TopLevelPtr]
   · simp only
     have := ctx.sim.disjoint_allocs
     grind [TopLevelPtr]
   · simp only
     intros op opIb
     have := ctx.sim.in_bounds (.operation op) (by grind)
     have := ctx.sim.disjoint_allocs (.operation op) (.operation ptr.spec) (by grind) (by grind)
     have := ctx.sim.encoding_op op (by grind)
     constructor
     · constructor
       · have := this.prev
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OperationMPtr.readPrev!]
       · have := this.next
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OperationMPtr.readNext!]
       · have := this.parent
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OperationMPtr.readParent!]
       · have := this.opType
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OperationMPtr.readOpType!]
       · have := this.attrs
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OperationMPtr.readAttrs!]
     · constructor
       · have := this.numBlockOperands
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OperationMPtr.readNumBlockOperands!]
       · intros bo boIb heq
         have hrange := @BlockOperandPtr.range_included_op_range
         have := this.blockOperands bo (by grind) (by grind)
         constructor
         · have := this.nextUse
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockOperandMPtr.readNextUse!]
         · have := this.back
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockOperandMPtr.readBack!]
         · have := this.owner
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockOperandMPtr.readOwner!]
         · have := this.value
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockOperandMPtr.readValue!]
     · constructor
       · have := this.numRegions
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OperationMPtr.readNumRegions!]
       · intros idx idxIn
         have := ctx.sim.encoding_op op (by grind) |>.regions idx (by grind)
         simp only [RegionPtr.Sim, RegionPtr.toM, RegionPtr.toFlat,
           OperationPtr.getRegion!_OperationPtr_setAttributes, Nat.toUInt64_eq]
         have hcap := ctx.sim.repr.operations_indices op (by grind) |>.capRegions
         have hmem : ctxBuf.mem = ctx.buf.mem := by grind [Buffed.IRBufContext.insertAttrs]
         have hcong : ∀ (a : UInt64) h h',
             Buffed.OperationMPtr.readNthRegion!
               (Buffed.OperationMPtr.writeAttrs ctxBuf ptr.impl a h) op.toM (UInt64.ofNat idx)
             = Buffed.OperationMPtr.readNthRegion!
               (Buffed.OperationMPtr.writeAttrs ctx.buf ptr.impl a h') op.toM (UInt64.ofNat idx) := by
           intro a h h'
           simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!,
             Buffed.OperationMPtr.computeRegionsOffset!, Buffed.OperationMPtr.computeBlockOperandsOffset!,
             Buffed.OperationMPtr.computeOperandsOffset!, Buffed.OperationMPtr.readNumBlockOperands!,
             Buffed.OperationMPtr.readNumOperands!, Buffed.OperationMPtr.readOpType!,
             Buffed.OperationMPtr.writeAttrs, hmem]
         grind [layout_grind]
     · constructor
       · have := this.numOperands
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OperationMPtr.readNumOperands!]
       · intros oper operIb heq
         have := ctx.sim.encoding_op op (by grind) |>.operands oper (by grind) (by grind)
         have hrange := @OpOperandPtr.range_included_op_range
         constructor
         · have := this.nextUse
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OpOperandMPtr.readNextUse!]
         · have := this.back
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OpOperandMPtr.readBack!]
         · have := this.owner
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OpOperandMPtr.readOwner!]
         · have := this.value
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OpOperandMPtr.readValue!]
     · constructor
       · have := this.numResults
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OperationMPtr.readNumResults!]
       · intros res resIb heq
         have := ctx.sim.encoding_op op (by grind) |>.results res (by grind) (by grind)
         have hrange := @OpResultPtr.range_included_op_range
         constructor
         · have := this.kind
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OpResultMPtr.readKind!]
         · have := this.typee
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OpResultMPtr.readType!]
         · have := this.firstUse
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OpResultMPtr.readFirstUse!]
         · have := this.index
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OpResultMPtr.readIndex!]
         · have := this.owner
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.OpResultMPtr.readOwner!]
   · simp only
     intros blk blkIb
     have := ctx.sim.in_bounds (.block blk) (by grind)
     have := ctx.sim.disjoint_allocs (.block blk) (.operation ptr.spec) (by grind) (by grind)
     have := ctx.sim.encoding_block blk (by grind)
     constructor
     · constructor
       · have := this.firstUse
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockMPtr.readFirstUse!]
       · have := this.prev
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockMPtr.readPrev!]
       · have := this.next
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockMPtr.readNext!]
       · have := this.parent
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockMPtr.readParent!]
       · have := this.firstOp
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockMPtr.readFirstOp!]
       · have := this.lastOp
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockMPtr.readLastOp!]
     · constructor
       · have := this.numArguments
         grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockMPtr.readNumArguments!]
       · intros arg argIn heq
         have := this.arguments arg (by grind) (by grind)
         have hrange := @BlockArgumentPtr.range_included_block_range
         constructor
         · have := this.kind
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockArgumentMPtr.readKind!]
         · have := this.type
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockArgumentMPtr.readType!]
         · have := this.firstUse
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockArgumentMPtr.readFirstUse!]
         · have := this.index
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockArgumentMPtr.readIndex!]
         · have := this.owner
           grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.BlockArgumentMPtr.readOwner!]
   · simp only
     intros rg rgIb
     have := ctx.sim.in_bounds (.region rg) (by grind)
     have := ctx.sim.disjoint_allocs (.region rg) (.operation ptr.spec) (by grind) (by grind)
     have := ctx.sim.encoding_region rg (by grind)
     constructor
     · have := this.firstBlock
       grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.RegionMPtr.readFirstBlock!]
     · have := this.lastBlock
       grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.RegionMPtr.readLastBlock!]
     · have := this.parent
       grind [layout_grind, Buffed.OperationMPtr.writeAttrs, Buffed.RegionMPtr.readParent!]
   · -- `insertAttrs` only pushes onto the attribute table, and slot 0 is occupied
     -- (the old `attr_empty`), so the push leaves it unchanged.
     have := ctx.sim.attr_empty
     grind [Buffed.OperationMPtr.writeAttrs, Buffed.IRBufContext.insertAttrs]⟩

@[simp, grind →]
theorem Sim.OperationPtr.setAttributes_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (attrs : DictionaryAttr) (ib : ptr.InBounds ctx) :
    setAttributes ctx ptr attrs ib = some ctx →
    ctx.spec = ptr.spec.setAttributes ctx.spec attrs := by
  simp only [setAttributes_def, setAttributesSim]; grind

@[inline]
def Sim.OperationPtr.getAttributes (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : DictionaryAttr :=
  let idx := ptr.impl.readAttrs ctx.buf (by prove_setLinkBoundsOp ctx ptr)
  -- The `Sim` encoding invariant `attrs` says the stored attribute index points into the
  -- attribute table (`attributes[readAttrs!]? = some _`), which is exactly the array bound.
  (ctx.buf.attributes[idx.toNat]'(by
    have hattr := ctx.sim.encoding_op ptr.spec (by grind) |>.attrs
    grind)).asDict (by
    have hattr := ctx.sim.encoding_op ptr.spec (by grind) |>.attrs
    grind)

@[inline]
def Sim.OperationPtr.getAttributes! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : DictionaryAttr :=
  let idx := ptr.impl.readAttrs! ctx.buf
  -- Without an `InBounds` hypothesis nothing guarantees the read index lands on a
  -- dictionary in the attribute table, so fall back to `.empty` on garbage input.
  match ctx.buf.attributes[idx.toNat]! with
  | .dictionaryAttr dict => dict
  | _ => .empty

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getAttributes_eq_getAttributes! (ctx : IRContext OpInfo) ptr ib :
    getAttributes ctx ptr ib = getAttributes! ctx ptr := by
  have hattr := ctx.sim.encoding_op ptr.spec (by grind) |>.attrs
  simp [getAttributes, getAttributes!]
  grind

buffed
def Sim.OperationPtr.getOperandPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.OpOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeOperandOffset ctx.buf index (by prove_setLinkBoundsOp ctx ptr),
   ptr.spec.getOpOperand index.toNat⟩


buffed
def Sim.OperationPtr.getOperandPtr!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.OpOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeOperandOffset! ctx.buf index,
   ptr.spec.getOpOperand index.toNat⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getOperandPtr_eq_getOperandPtr! (ctx : IRContext OpInfo) ptr index ib :
    getOperandPtr ctx ptr index ib = getOperandPtr! ctx ptr index := by
  simp [getOperandPtr_def, getOperandPtrSim, getOperandPtr!_def, getOperandPtr!Sim]

buffed
def Sim.OperationPtr.getResultPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.OpResultPtr :=
  ⟨ptr.impl + ptr.impl.computeResultOffset ctx.buf index (by prove_setLinkBoundsOp ctx ptr),
   ptr.spec.getResult index.toNat⟩

buffed
def Sim.OperationPtr.getResultPtr!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.OpResultPtr :=
  ⟨ptr.impl + ptr.impl.computeResultOffset! ctx.buf index,
   ptr.spec.getResult index.toNat⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getResultPtr_eq_getResultPtr! (ctx : IRContext OpInfo) ptr index ib :
    getResultPtr ctx ptr index ib = getResultPtr! ctx ptr index := by
  simp [getResultPtr_def, getResultPtrSim, getResultPtr!_def, getResultPtr!Sim]

buffed
def Sim.OperationPtr.getRegionPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) (hindex : index.toNat < ptr.spec.getNumRegions! ctx.spec) : Sim.RegionPtr :=
  ⟨ptr.impl.readNthRegion ctx.buf index (by prove_setLinkBoundsOp ctx ptr) (by prove_setLinkBoundsRegionSlot ctx ptr index),
   ptr.spec.getRegion ctx.spec index.toNat (by grind) (by grind)⟩

buffed
def Sim.OperationPtr.getRegionPtr!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.RegionPtr :=
  ⟨ptr.impl.readNthRegion! ctx.buf index,
   ptr.spec.getRegion! ctx.spec index.toNat⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getRegionPtr_eq_getRegionPtr! (ctx : IRContext OpInfo) ptr index ib hindex :
    getRegionPtr ctx ptr index ib hindex = getRegionPtr! ctx ptr index := by
  grind [getRegionPtr_def, getRegionPtrSim, getRegionPtr!_def, getRegionPtr!Sim]

buffed
def Sim.OperationPtr.getBlockOperandPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.BlockOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeBlockOperandOffset ctx.buf index (by prove_setLinkBoundsOp ctx ptr),
   ptr.spec.getBlockOperand index.toNat⟩

buffed
def Sim.OperationPtr.getBlockOperandPtr!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.BlockOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeBlockOperandOffset! ctx.buf index,
   ptr.spec.getBlockOperand index.toNat⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getBlockOperandPtr_eq_getBlockOperandPtr! (ctx : IRContext OpInfo) ptr index ib :
    getBlockOperandPtr ctx ptr index ib = getBlockOperandPtr! ctx ptr index := by
  simp [getBlockOperandPtr_def, getBlockOperandPtrSim, getBlockOperandPtr!_def, getBlockOperandPtr!Sim]

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
  simp [getNumOperands!]
  grind

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
  simp [getNumSuccessors!]
  grind

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
  simp [getNumResults!]
  grind

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
  simp [getNumRegions!]
  grind

@[grind =]
theorem Sim.OperationPtr.getNumRegions!_spec_of_wf (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} (wf : ctx.spec.WellFormed) :
    (getNumRegions! ctx ptr) = (ptr.spec.getNumRegions! ctx.spec).toUInt64 := by
  grind [IRContext.WellFormed.operations]

buffed
def Sim.OpOperandPtr.setNextUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl (by prove_setLinkBoundsOpOperand ctx ptr), ptr.spec.setNextUse ctx.spec nextUse.spec (by grind), by prove_setLinkSim ctx Buffed.OpOperandMPtr.writeNextUse⟩

open Classical in
noncomputable def Sim.OpOperandPtr.setNextUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpOperand.Offsets.nextUse).toInt + Buffed.OpOperand.Sizes.nextUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandMPtr.writeNextUse ctx.buf ptr.impl nextUse.impl h₁,
      spec := ptr.spec.setNextUse! ctx.spec nextUse.spec } then
    ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl h₁, ptr.spec.setNextUse! ctx.spec nextUse.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setNextUse_eq_setNextUse! (ctx : IRContext OpInfo) ptr nextUse ib nextUseIb :
    setNextUse ctx ptr nextUse ib nextUseIb = setNextUse! ctx ptr nextUse := by
  simp [setNextUse_def, setNextUseSim, setNextUse!]
  split
  · grind
  · prove_setLinkBoundsOpOperand ctx ptr

@[simp, grind =]
theorem Sim.OpOperandPtr.setNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse ctx ptr nextUse ib nextUseIb).spec = ptr.spec.setNextUse ctx.spec nextUse.spec := by
  rfl

@[simp, grind =]
theorem Sim.OpOperandPtr.setNextUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse! ctx ptr nextUse).spec = ptr.spec.setNextUse! ctx.spec nextUse.spec := by
  grind

buffed
def Sim.OpOperandPtr.getNextUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readNextUse ctx.buf (by prove_setLinkBoundsOpOperand ctx ptr), (ptr.spec.get ctx.spec).nextUse⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).nextUse := by
  rfl

@[grind .]
theorem Sim.OpOperandPtr.getNextUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind)
    |>.nextUse
  grind [getNextUseSim, getNextUse_def]

buffed
def Sim.OpOperandPtr.getNextUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readNextUse! ctx.buf, (ptr.spec.get! ctx.spec).nextUse⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getNextUse_eq_getNextUse! (ctx : IRContext OpInfo) ptr ib :
    getNextUse ctx ptr ib = getNextUse! ctx ptr := by
  simp [getNextUse_def, getNextUseSim, getNextUse!_def, getNextUse!Sim]
  grind

buffed
def Sim.OpOperandPtr.setBackSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeBack ctx.buf back.impl (by prove_setLinkBoundsOpOperand ctx ptr),
  ptr.spec.setBack ctx.spec back.spec (by grind), by prove_setLinkSim ctx Buffed.OpOperandMPtr.writeBack⟩

open Classical in
noncomputable def Sim.OpOperandPtr.setBack! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpOperand.Offsets.back).toInt + Buffed.OpOperand.Sizes.back.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandMPtr.writeBack ctx.buf ptr.impl back.impl h₁,
      spec := ptr.spec.setBack! ctx.spec back.spec } then
    ⟨ptr.impl.writeBack ctx.buf back.impl h₁, ptr.spec.setBack! ctx.spec back.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setBack_eq_setBack! (ctx : IRContext OpInfo) ptr back ib backIb :
    setBack ctx ptr back ib backIb = setBack! ctx ptr back := by
  simp [setBack_def, setBackSim, setBack!]
  split
  · grind
  · prove_setLinkBoundsOpOperand ctx ptr

@[simp, grind =]
theorem Sim.OpOperandPtr.setBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack ctx ptr back ib backIb).spec = ptr.spec.setBack ctx.spec back.spec := by
  rfl

@[simp, grind =]
theorem Sim.OpOperandPtr.setBack!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack! ctx ptr back).spec = ptr.spec.setBack! ctx.spec back.spec := by
  grind

buffed
def Sim.OpOperandPtr.getBackSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OpOperandPtrPtr :=
  ⟨ptr.impl.readBack ctx.buf (by prove_setLinkBoundsOpOperand ctx ptr), (ptr.spec.get ctx.spec).back⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).spec = (ptr.spec.get ctx.spec).back := by
  rfl

@[grind .]
theorem Sim.OpOperandPtr.getBack_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind)
    |>.back
  grind [getBackSim, getBack_def]

buffed
def Sim.OpOperandPtr.getBack!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.OpOperandPtrPtr :=
  ⟨ptr.impl.readBack! ctx.buf, (ptr.spec.get! ctx.spec).back⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getBack_eq_getBack! (ctx : IRContext OpInfo) ptr ib :
    getBack ctx ptr ib = getBack! ctx ptr := by
  simp [getBack_def, getBackSim, getBack!_def, getBack!Sim]
  grind

buffed
def Sim.OpOperandPtr.setOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl (by prove_setLinkBoundsOpOperand ctx ptr), ptr.spec.setOwner ctx.spec owner.spec (by grind), by prove_setLinkSim ctx Buffed.OpOperandMPtr.writeOwner⟩

open Classical in
noncomputable def Sim.OpOperandPtr.setOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpOperand.Offsets.owner).toInt + Buffed.OpOperand.Sizes.owner.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandMPtr.writeOwner ctx.buf ptr.impl owner.impl h₁,
      spec := ptr.spec.setOwner! ctx.spec owner.spec } then
    ⟨ptr.impl.writeOwner ctx.buf owner.impl h₁, ptr.spec.setOwner! ctx.spec owner.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner_def, setOwnerSim, setOwner!]
  split
  · grind
  · prove_setLinkBoundsOpOperand ctx ptr

@[simp, grind =]
theorem Sim.OpOperandPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  rfl

@[simp, grind =]
theorem Sim.OpOperandPtr.setOwner!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner! ctx ptr owner).spec = ptr.spec.setOwner! ctx.spec owner.spec := by
  grind

buffed
def Sim.OpOperandPtr.getOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner ctx.buf (by prove_setLinkBoundsOpOperand ctx ptr), (ptr.spec.get ctx.spec).owner⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  rfl

@[grind .]
theorem Sim.OpOperandPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind)
    |>.owner
  grind [getOwnerSim, getOwner_def]

buffed
def Sim.OpOperandPtr.getOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (ptr.spec.get! ctx.spec).owner⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner_def, getOwnerSim, getOwner!_def, getOwner!Sim]
  grind

buffed
def Sim.OpOperandPtr.setValueSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeValue ctx.buf value.impl (by prove_setLinkBoundsOpOperand ctx ptr), ptr.spec.setValue ctx.spec value.spec (by grind), by prove_setLinkSim ctx Buffed.OpOperandMPtr.writeValue⟩

open Classical in
noncomputable def Sim.OpOperandPtr.setValue! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpOperand.Offsets.value).toInt + Buffed.OpOperand.Sizes.value.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandMPtr.writeValue ctx.buf ptr.impl value.impl h₁,
      spec := ptr.spec.setValue! ctx.spec value.spec } then
    ⟨ptr.impl.writeValue ctx.buf value.impl h₁, ptr.spec.setValue! ctx.spec value.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setValue_eq_setValue! (ctx : IRContext OpInfo) ptr value ib valueIb :
    setValue ctx ptr value ib valueIb = setValue! ctx ptr value := by
  simp [setValue_def, setValueSim, setValue!]
  split
  · grind
  · prove_setLinkBoundsOpOperand ctx ptr

@[simp, grind =]
theorem Sim.OpOperandPtr.setValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue ctx ptr value ib valueIb).spec = ptr.spec.setValue ctx.spec value.spec := by
  rfl

@[simp, grind =]
theorem Sim.OpOperandPtr.setValue!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue! ctx ptr value).spec = ptr.spec.setValue! ctx.spec value.spec := by
  grind

buffed
def Sim.OpOperandPtr.getValueSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.ValuePtr :=
  ⟨ptr.impl.readValue ctx.buf (by prove_setLinkBoundsOpOperand ctx ptr), (ptr.spec.get ctx.spec).value⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).spec = (ptr.spec.get ctx.spec).value := by
  rfl

@[grind .]
theorem Sim.OpOperandPtr.getValue_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind) |>.value
  grind [getValueSim, getValue_def]

buffed
def Sim.OpOperandPtr.getValue!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.ValuePtr :=
  ⟨ptr.impl.readValue! ctx.buf, (ptr.spec.get! ctx.spec).value⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getValue_eq_getValue! (ctx : IRContext OpInfo) ptr ib :
    getValue ctx ptr ib = getValue! ctx ptr := by
  simp [getValue_def, getValueSim, getValue!_def, getValue!Sim]
  grind

buffed
def Sim.OpResultPtr.setFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl (by prove_setLinkBoundsOpResult ctx ptr), ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind), by prove_setLinkSim ctx Buffed.OpResultMPtr.writeFirstUse⟩

open Classical in
noncomputable def Sim.OpResultPtr.setFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.ValueImpl.Offsets.firstUse).toInt + Buffed.ValueImpl.Sizes.firstUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpResultMPtr.writeFirstUse ctx.buf ptr.impl firstUse.impl h₁,
      spec := ptr.spec.setFirstUse! ctx.spec firstUse.spec } then
    ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl h₁, ptr.spec.setFirstUse! ctx.spec firstUse.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse_def, setFirstUseSim, setFirstUse!]
  split
  · grind
  · prove_setLinkBoundsOpResult ctx ptr

@[simp, grind =]
theorem Sim.OpResultPtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  rfl

@[simp, grind =]
theorem Sim.OpResultPtr.setFirstUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse! ctx ptr firstUse).spec = ptr.spec.setFirstUse! ctx.spec firstUse.spec := by
  grind

buffed
def Sim.OpResultPtr.getFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf (by prove_setLinkBoundsOpResult ctx ptr), (ptr.spec.get ctx.spec).firstUse⟩

@[simp, grind =]
theorem Sim.OpResultPtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstUse := by
  rfl

@[grind .]
theorem Sim.OpResultPtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpResultPtr.inBounds_def])
    |>.results ptr.spec (by grind) (by grind) |>.firstUse
  grind [getFirstUseSim, getFirstUse_def]

buffed
def Sim.OpResultPtr.getFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (ptr.spec.get! ctx.spec).firstUse⟩

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse_def, getFirstUseSim, getFirstUse!_def, getFirstUse!Sim]
  grind

buffed
def Sim.OpResultPtr.setOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl (by prove_setLinkBoundsOpResult ctx ptr), ptr.spec.setOwner ctx.spec owner.spec (by grind), by prove_setLinkSim ctx Buffed.OpResultMPtr.writeOwner⟩

open Classical in
noncomputable def Sim.OpResultPtr.setOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.OpResult.Offsets.owner).toInt + Buffed.OpResult.Sizes.owner.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpResultMPtr.writeOwner ctx.buf ptr.impl owner.impl h₁,
      spec := ptr.spec.setOwner! ctx.spec owner.spec } then
    ⟨ptr.impl.writeOwner ctx.buf owner.impl h₁, ptr.spec.setOwner! ctx.spec owner.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner_def, setOwnerSim, setOwner!]
  split
  · grind
  · prove_setLinkBoundsOpResult ctx ptr

@[simp, grind =]
theorem Sim.OpResultPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  rfl

@[simp, grind =]
theorem Sim.OpResultPtr.setOwner!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner! ctx ptr owner).spec = ptr.spec.setOwner! ctx.spec owner.spec := by
  grind

buffed
def Sim.OpResultPtr.getOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner ctx.buf (by prove_setLinkBoundsOpResult ctx ptr), (ptr.spec.get ctx.spec).owner⟩

@[simp, grind =]
theorem Sim.OpResultPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  rfl

@[grind .]
theorem Sim.OpResultPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpResultPtr.inBounds_def])
    |>.results ptr.spec (by grind) (by grind) |>.owner
  grind [getOwnerSim, getOwner_def]

buffed
def Sim.OpResultPtr.getOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (ptr.spec.get! ctx.spec).owner⟩

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner_def, getOwnerSim, getOwner!_def, getOwner!Sim]
  grind

buffed
def Sim.BlockArgumentPtr.setFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl (by prove_setLinkBoundsBlockArgument ctx ptr), ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind), by prove_setLinkSim ctx Buffed.BlockArgumentMPtr.writeFirstUse⟩

open Classical in
noncomputable def Sim.BlockArgumentPtr.setFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.ValueImpl.Offsets.firstUse).toInt + Buffed.ValueImpl.Sizes.firstUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockArgumentMPtr.writeFirstUse ctx.buf ptr.impl firstUse.impl h₁,
      spec := ptr.spec.setFirstUse! ctx.spec firstUse.spec } then
    ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl h₁, ptr.spec.setFirstUse! ctx.spec firstUse.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse_def, setFirstUseSim, setFirstUse!]
  split
  · grind
  · prove_setLinkBoundsBlockArgument ctx ptr

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setFirstUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse! ctx ptr firstUse).spec = ptr.spec.setFirstUse! ctx.spec firstUse.spec := by
  grind

buffed
def Sim.BlockArgumentPtr.getFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf (by prove_setLinkBoundsBlockArgument ctx ptr), (ptr.spec.get ctx.spec).firstUse⟩

@[simp, grind =]
theorem Sim.BlockArgumentPtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstUse := by
  rfl

@[grind .]
theorem Sim.BlockArgumentPtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_block ptr.spec.block (by grind [Veir.BlockArgumentPtr.inBounds_def])
   |>.arguments ptr.spec (by grind) (by grind) |>.firstUse
  grind [getFirstUseSim, getFirstUse_def]

buffed
def Sim.BlockArgumentPtr.getFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (ptr.spec.get! ctx.spec).firstUse⟩

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse_def, getFirstUseSim, getFirstUse!_def, getFirstUse!Sim]
  grind

buffed
def Sim.BlockArgumentPtr.setIndexSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : UInt64) (ib : ptr.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeIndex ctx.buf index (by prove_setLinkBoundsBlockArgument ctx ptr), ptr.spec.setIndex ctx.spec index.toNat (by grind), by prove_setLinkSim ctx Buffed.BlockArgumentMPtr.writeIndex⟩

open Classical in
noncomputable def Sim.BlockArgumentPtr.setIndex! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : UInt64) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockArgument.Offsets.index).toInt + Buffed.BlockArgument.Sizes.index.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockArgumentMPtr.writeIndex ctx.buf ptr.impl index h₁,
      spec := ptr.spec.setIndex! ctx.spec index.toNat } then
    ⟨ptr.impl.writeIndex ctx.buf index h₁, ptr.spec.setIndex! ctx.spec index.toNat, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.setIndex_eq_setIndex! (ctx : IRContext OpInfo) ptr index ib :
    setIndex ctx ptr index ib = setIndex! ctx ptr index := by
  simp [setIndex_def, setIndexSim, setIndex!]
  split
  · grind
  · prove_setLinkBoundsBlockArgument ctx ptr

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setIndex_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : UInt64)
    (ib : ptr.InBounds ctx) :
    (setIndex ctx ptr index ib).spec = ptr.spec.setIndex ctx.spec index.toNat := by
  rfl

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setIndex!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : UInt64)
    (ib : ptr.InBounds ctx) :
    (setIndex! ctx ptr index).spec = ptr.spec.setIndex! ctx.spec index.toNat := by
  grind

@[inline]
def Sim.BlockArgumentPtr.getIndexSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
  (_index : Nat)
    (ib : ptr.InBounds ctx) : Nat :=
  (ptr.spec.get ctx.spec).index

@[inline]
def Sim.BlockArgumentPtr.getIndex!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (_index : Nat) : Nat :=
  (ptr.spec.get! ctx.spec).index

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.getIndex_eq_getIndex! (ctx : IRContext OpInfo) ptr index ib :
    getIndexSim ctx ptr index ib = getIndex!Sim ctx ptr index := by
  simp [getIndexSim, getIndex!Sim]
  grind

buffed
def Sim.BlockArgumentPtr.setOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl (by prove_setLinkBoundsBlockArgument ctx ptr), ptr.spec.setOwner ctx.spec owner.spec (by grind), by prove_setLinkSim ctx Veir.Buffed.BlockArgumentMPtr.writeOwner⟩

open Classical in
noncomputable def Sim.BlockArgumentPtr.setOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockArgument.Offsets.owner).toInt + Buffed.BlockArgument.Sizes.owner.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockArgumentMPtr.writeOwner ctx.buf ptr.impl owner.impl h₁,
      spec := ptr.spec.setOwner! ctx.spec owner.spec } then
    ⟨ptr.impl.writeOwner ctx.buf owner.impl h₁, ptr.spec.setOwner! ctx.spec owner.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner_def, setOwnerSim, setOwner!]
  split
  · grind
  · prove_setLinkBoundsBlockArgument ctx ptr

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setOwner!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner! ctx ptr owner).spec = ptr.spec.setOwner! ctx.spec owner.spec := by
  grind

buffed
def Sim.BlockArgumentPtr.getOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) : Sim.BlockPtr :=
  ⟨ptr.impl.readOwner ctx.buf (by prove_setLinkBoundsBlockArgument ctx ptr), (ptr.spec.get ctx.spec).owner⟩

@[simp, grind =]
theorem Sim.BlockArgumentPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  rfl

@[grind .]
theorem Sim.BlockArgumentPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_block ptr.spec.block (by simp; grind [Veir.BlockArgumentPtr.inBounds_def])
    |>.arguments ptr.spec (by grind) (by grind) |>.owner
  grind [getOwnerSim, getOwner_def]

buffed
def Sim.BlockArgumentPtr.getOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr) : Sim.BlockPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (ptr.spec.get! ctx.spec).owner⟩

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner_def, getOwnerSim, getOwner!_def, getOwner!Sim]
  grind

buffed
def Sim.BlockOperandPtr.setNextUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl (by prove_setLinkBoundsBlockOperand ctx ptr), ptr.spec.setNextUse ctx.spec nextUse.spec (by grind), by prove_setLinkSim ctx Buffed.BlockOperandMPtr.writeNextUse⟩

open Classical in
noncomputable def Sim.BlockOperandPtr.setNextUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockOperand.Offsets.nextUse).toInt + Buffed.BlockOperand.Sizes.nextUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandMPtr.writeNextUse ctx.buf ptr.impl nextUse.impl h₁,
      spec := ptr.spec.setNextUse! ctx.spec nextUse.spec } then
    ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl h₁, ptr.spec.setNextUse! ctx.spec nextUse.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setNextUse_eq_setNextUse! (ctx : IRContext OpInfo) ptr nextUse ib nextUseIb :
    setNextUse ctx ptr nextUse ib nextUseIb = setNextUse! ctx ptr nextUse := by
  simp [setNextUse_def, setNextUseSim, setNextUse!]
  split
  · grind
  · prove_setLinkBoundsBlockOperand ctx ptr

@[simp, grind =]
theorem Sim.BlockOperandPtr.setNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse ctx ptr nextUse ib nextUseIb).spec = ptr.spec.setNextUse ctx.spec nextUse.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockOperandPtr.setNextUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse! ctx ptr nextUse).spec = ptr.spec.setNextUse! ctx.spec nextUse.spec := by
  grind

buffed
def Sim.BlockOperandPtr.getNextUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readNextUse ctx.buf (by prove_setLinkBoundsBlockOperand ctx ptr), (ptr.spec.get ctx.spec).nextUse⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).nextUse := by
  rfl

@[grind .]
theorem Sim.BlockOperandPtr.getNextUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.nextUse
  grind [getNextUseSim, getNextUse_def]

buffed
def Sim.BlockOperandPtr.getNextUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readNextUse! ctx.buf, (ptr.spec.get! ctx.spec).nextUse⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getNextUse_eq_getNextUse! (ctx : IRContext OpInfo) ptr ib :
    getNextUse ctx ptr ib = getNextUse! ctx ptr := by
  simp [getNextUse_def, getNextUseSim, getNextUse!_def, getNextUse!Sim]
  grind

buffed
def Sim.BlockOperandPtr.setBackSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeBack ctx.buf back.impl (by prove_setLinkBoundsBlockOperand ctx ptr), ptr.spec.setBack ctx.spec back.spec (by grind), by prove_setLinkSim ctx Buffed.BlockOperandMPtr.writeBack⟩

open Classical in
noncomputable def Sim.BlockOperandPtr.setBack! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockOperand.Offsets.back).toInt + Buffed.BlockOperand.Sizes.back.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandMPtr.writeBack ctx.buf ptr.impl back.impl h₁,
      spec := ptr.spec.setBack! ctx.spec back.spec } then
    ⟨ptr.impl.writeBack ctx.buf back.impl h₁, ptr.spec.setBack! ctx.spec back.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setBack_eq_setBack! (ctx : IRContext OpInfo) ptr back ib backIb :
    setBack ctx ptr back ib backIb = setBack! ctx ptr back := by
  simp [setBack_def, setBackSim, setBack!]
  split
  · grind
  · prove_setLinkBoundsBlockOperand ctx ptr

@[simp, grind =]
theorem Sim.BlockOperandPtr.setBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack ctx ptr back ib backIb).spec = ptr.spec.setBack ctx.spec back.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockOperandPtr.setBack!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack! ctx ptr back).spec = ptr.spec.setBack! ctx.spec back.spec := by
  grind

buffed
def Sim.BlockOperandPtr.getBackSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.BlockOperandPtrPtr :=
  ⟨ptr.impl.readBack ctx.buf (by prove_setLinkBoundsBlockOperand ctx ptr), (ptr.spec.get ctx.spec).back⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).spec = (ptr.spec.get ctx.spec).back := by
  rfl

@[grind .]
theorem Sim.BlockOperandPtr.getBack_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.back
  grind [getBackSim, getBack_def]

buffed
def Sim.BlockOperandPtr.getBack!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.BlockOperandPtrPtr :=
  ⟨ptr.impl.readBack! ctx.buf, (ptr.spec.get! ctx.spec).back⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getBack_eq_getBack! (ctx : IRContext OpInfo) ptr ib :
    getBack ctx ptr ib = getBack! ctx ptr := by
  simp [getBack_def, getBackSim, getBack!_def, getBack!Sim]
  grind

buffed
def Sim.BlockOperandPtr.setOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl (by prove_setLinkBoundsBlockOperand ctx ptr), ptr.spec.setOwner ctx.spec owner.spec (by grind), by prove_setLinkSim ctx Buffed.BlockOperandMPtr.writeOwner⟩

open Classical in
noncomputable def Sim.BlockOperandPtr.setOwner! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockOperand.Offsets.owner).toInt + Buffed.BlockOperand.Sizes.owner.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandMPtr.writeOwner ctx.buf ptr.impl owner.impl h₁,
      spec := ptr.spec.setOwner! ctx.spec owner.spec } then
    ⟨ptr.impl.writeOwner ctx.buf owner.impl h₁, ptr.spec.setOwner! ctx.spec owner.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner_def, setOwnerSim, setOwner!]
  split
  · grind
  · prove_setLinkBoundsBlockOperand ctx ptr

@[simp, grind =]
theorem Sim.BlockOperandPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockOperandPtr.setOwner!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner! ctx ptr owner).spec = ptr.spec.setOwner! ctx.spec owner.spec := by
  grind

buffed
def Sim.BlockOperandPtr.getOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner ctx.buf (by prove_setLinkBoundsBlockOperand ctx ptr), (ptr.spec.get ctx.spec).owner⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  rfl

@[grind .]
theorem Sim.BlockOperandPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.owner
  grind [getOwnerSim, getOwner_def]

buffed
def Sim.BlockOperandPtr.getOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (ptr.spec.get! ctx.spec).owner⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner_def, getOwnerSim, getOwner!_def, getOwner!Sim]
  grind

buffed
def Sim.BlockOperandPtr.setValueSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeValue ctx.buf value.impl (by prove_setLinkBoundsBlockOperand ctx ptr), ptr.spec.setValue ctx.spec value.spec (by grind), by prove_setLinkSim ctx Buffed.BlockOperandMPtr.writeValue⟩

open Classical in
noncomputable def Sim.BlockOperandPtr.setValue! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.BlockOperand.Offsets.value).toInt + Buffed.BlockOperand.Sizes.value.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandMPtr.writeValue ctx.buf ptr.impl value.impl h₁,
      spec := ptr.spec.setValue! ctx.spec value.spec } then
    ⟨ptr.impl.writeValue ctx.buf value.impl h₁, ptr.spec.setValue! ctx.spec value.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setValue_eq_setValue! (ctx : IRContext OpInfo) ptr value ib valueIb :
    setValue ctx ptr value ib valueIb = setValue! ctx ptr value := by
  simp [setValue_def, setValueSim, setValue!]
  split
  · grind
  · prove_setLinkBoundsBlockOperand ctx ptr

@[simp, grind =]
theorem Sim.BlockOperandPtr.setValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue ctx ptr value ib valueIb).spec = ptr.spec.setValue ctx.spec value.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockOperandPtr.setValue!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue! ctx ptr value).spec = ptr.spec.setValue! ctx.spec value.spec := by
  grind

buffed
def Sim.BlockOperandPtr.getValueSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.BlockPtr :=
  ⟨ptr.impl.readValue ctx.buf (by prove_setLinkBoundsBlockOperand ctx ptr), (ptr.spec.get ctx.spec).value⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).spec = (ptr.spec.get ctx.spec).value := by
  rfl

@[grind .]
theorem Sim.BlockOperandPtr.getValue_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.value
  grind [getValueSim, getValue_def]

buffed
def Sim.BlockOperandPtr.getValue!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.BlockPtr :=
  ⟨ptr.impl.readValue! ctx.buf, (ptr.spec.get! ctx.spec).value⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getValue_eq_getValue! (ctx : IRContext OpInfo) ptr ib :
    getValue ctx ptr ib = getValue! ctx ptr := by
  simp [getValue_def, getValueSim, getValue!_def, getValue!Sim]
  grind

@[inline]
def Sim.BlockPtr.allocEmptyImpl (ctx₀ : Buffed.IRBufContext OpInfo) (numArgs : UInt64)
    (hnumArgs : numArgs.toNat ≤ Buffed.countCard) : Option (Buffed.IRBufContext OpInfo × Buffed.BlockMPtr) :=
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
    {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.BlockMPtr}
    (heq : Sim.BlockPtr.allocEmptyImpl ctx.buf numArgs hnumArgs = some (ctxBuf, ptrImpl))
    {ctxSpec : Veir.IRContext OpInfo} {ptrSpec : Veir.BlockPtr}
    (hspec : Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptrImpl.toNat = some (ctxSpec, ptrSpec)) :
    Veir.Sim (OpInfo := OpInfo) ⟨ctxBuf, ctxSpec⟩ := by
  simp only [Sim.BlockPtr.allocEmptyImpl] at heq
  split at heq
  · exact absurd heq (by simp)
  · rename_i buf halloc
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    -- Keep `ctxBuf` abstract (do NOT substitute the giant 7-write tower): bind the tower to
    -- `hctxBuf` so `prove_allocBounds` is elaborated ONCE here, not re-run per read-bridge.
    obtain ⟨hctxBuf, rfl⟩ := heq
    -- Size bookkeeping: the buffer grows by `computeBlockSize numArgs = 56 + numArgs*32` bytes.
    have hu := ctx.buf.usize_toNat
    have hs := ctx.buf.size_def
    have hgrow := ctx.buf.alloc_size halloc
    have hfits := buf.mem.fits_in_memory
    have hbsize := Buffed.BlockMPtr.computeBlockSize_toNat numArgs hnumArgs
    have hsize : ctx.buf.mem.size < 2 ^ 63 := by
      simp only [Buffed.IRBufContext.size_def, Int64.maxNatValue] at *; omega
    -- Spec characterization: the new block is at the old buffer end.
    have hptr := Veir.BlockPtr.allocEmptyAtAddress_ptr hspec
    have hlay := Veir.BlockPtr.allocEmptyAtAddress_preservesLayout hspec
    -- Uniform preservation: reads entirely below the old buffer end are unchanged.
    have hsizeAlloc : buf.size = ctx.buf.size + (Buffed.BlockMPtr.computeBlockSize numArgs).toUInt64.toNat := hgrow
    have hread : ∀ (a : UInt64), a.toNat + 8 ≤ ctx.buf.mem.size →
        ctxBuf.mem.read64! a
        = ctx.buf.mem.read64! a := by
      intro a ha
      rw [← hctxBuf]; clear hctxBuf
      -- Every blit is at `usize + off` (off ≥ 0) ≥ old buffer end, so disjoint from `[a, a+8) ⊆ [0, mem.size)`.
      have hab : a.toNat + 8 ≤ ctx.buf.usize.toNat := by grind
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp,
          Buffed.BlockMPtr.writeParent, Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev,
          Buffed.BlockMPtr.writeFirstUse, Buffed.BlockMPtr.writeNumArguments]
        rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; grind),
          ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; grind),
          ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; grind),
          ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; grind),
          ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; grind),
          ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; grind),
          ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; grind),
          ExArray.read64!_extend]
        grind
      · exact absurd halloc (by simp)
    have hread32 : ∀ (a : UInt64), a.toNat + 4 ≤ ctx.buf.mem.size →
        ctxBuf.mem.read32! a
        = ctx.buf.mem.read32! a := by
      intro a ha
      rw [← hctxBuf]; clear hctxBuf
      have hab : a.toNat + 4 ≤ ctx.buf.usize.toNat := by grind
      have husz63 : ctx.buf.usize.toNat < 2 ^ 63 := by grind
      -- `.toNat` of every write address `usize + off` (off an Int64 in [0,48], no wraparound).
      have ek : ∀ (off : Int64), 0 ≤ off.toInt → off.toInt ≤ 48 →
          a.toNat + 4 ≤ (ctx.buf.usize + off).toNat := by
        intro off h0 h48
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
      have hincl : IsIncluded (a.toNat...(a.toNat + 4)) ctx.buf.mem.range := by
        simp only [IsIncluded]; grind [ExArray.range_lower, ExArray.range_upper]
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp,
          Buffed.BlockMPtr.writeParent, Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev,
          Buffed.BlockMPtr.writeFirstUse, Buffed.BlockMPtr.writeNumArguments]
        rw [ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.lastOp (by decide) (by decide); omega),
          ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.firstOp (by decide) (by decide); omega),
          ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.parent (by decide) (by decide); omega),
          ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.next (by decide) (by decide); omega),
          ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.prev (by decide) (by decide); omega),
          ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.firstUse (by decide) (by decide); omega),
          ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have := ek Buffed.Block.Offsets.numArguments (by decide) (by decide); omega),
          ExArray.read32!_extend _ _ _ _ hincl]
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
    -- `ctxSpec.IsRepr`: the pre-context is representable and inserting an empty block preserves it.
    -- Proven once here so that `in_bounds` (new-block case) can reuse it via `after_ideal`.
    -- The new block's own `IsRepr` (`toFlat ≤ maxNatValue`): its address is the old buffer end.
    have hptrrepr : ptrSpec.IsRepr := by
      simp only [Veir.BlockPtr.IsRepr, Veir.BlockPtr.toFlat, hptr, Int64.maxNatValue] at *
      omega
    have hnewrepr : ctxSpec.IsRepr :=
      BlockPtr.allocEmptyAtAddress_fieldsIsRepr hspec (by simpa using hnumArgs) hptrrepr ctx.sim.repr
    constructor
    · -- fieldsInBounds (spec only)
      exact Veir.BlockPtr.allocEmptyAtAddress_fieldsInBounds hspec ctx.sim.fieldsInBounds
    · -- repr (spec only)
      exact hnewrepr
    · -- in_bounds
      intro ptr hib
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
          -- The new block is in bounds in the new context, and is `Block.empty numArgs.toNat`,
          -- so its `after` offset equals `computeBlockSize numArgs = 56 + numArgs*32`.
          have hnewib : ptrSpec.InBounds ctxSpec := by
            have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block ptrSpec) hspec).mpr
              (Or.inr (Or.inl rfl))
            simpa using this
          have hget : ptrSpec.get! ctxSpec = Block.empty numArgs.toNat := by
            have := BlockPtr.get!_BlockPtr_allocEmptyAtAddress (block := ptrSpec) hspec
            simpa using this
          have hcap : (ptrSpec.get! ctxSpec).capArguments = numArgs.toNat := by
            simp only [hget, Veir.Block.empty]
          -- `afterInt = argumentsInt(=56) + capArguments*40 = 56 + numArgs*40 = computeBlockSize`.
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
          -- The new block's ideal upper bound: usize + (56 + numArgs*32) = usize + computeBlockSize.
          -- Rewrite `afterInt` (via hafterInt) BEFORE unfolding `ptrSpec` (hptr), else the LHS won't match.
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
      -- Old ptrs keep their ranges (LayoutPreserved) and sit in `[0, size)`; the new block
      -- sits at `[size, size + computeBlockSize)`, hence disjoint from every old range.
      have hrange : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
          p.range ctxSpec = p.range ctx.spec := by
        intro p hp
        cases p with
        | operation op => exact LayoutPreserved.same_operationPtr_range op (by simpa using hp) hlay |>.symm
        | block bl => exact LayoutPreserved.same_blockPtr_range bl (by simpa using hp) hlay |>.symm
        | region rg => rfl
      have hupper : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
          (p.range ctxSpec).upper ≤ ctx.buf.mem.size := by
        intro p hp
        have hin := ctx.sim.in_bounds p hp
        rw [hrange p hp]
        simp only [IsIncludedIN] at hin
        simp only [ExArray.range_lower, ExArray.range_upper] at hin
        omega
      -- Membership in the new context: an old top-level ptr, or the fresh block.
      have hmem : ∀ (p : TopLevelPtr), p.InBounds ctxSpec →
          p.InBounds ctx.spec ∨ p = .block ptrSpec := by
        intro p hp
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
      -- The fresh block's range lower bound is `usize.toNat = size`.
      have hnewlow : (Veir.BlockPtr.range ptrSpec ctxSpec).lower = (ctx.buf.mem.size : Int) := by
        simp only [Veir.BlockPtr.range, Veir.BlockPtr.toFlat, Buffed.Block.range, hptr,
          add_nat_range_def]
        grind
      intro p1 p2 hib1 hib2 hne
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
    · -- encoding_op
      clear hctxBuf
      intro op opIb
      have holdib : op.InBounds ctx.spec := by
        have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.operation op) hspec).mp (by simpa using opIb)
        grind
      have henc := ctx.sim.encoding_op op holdib
      have hinb := ctx.sim.in_bounds (.operation op) (by simpa using holdib)
      simp only [TopLevelPtr.range, Veir.OperationPtr.range, IsIncludedIN, ExArray.range_upper] at hinb
      have hopM : op.toM.toNat = op.toFlat := by
        simp only [Veir.OperationPtr.toM]
        grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      have hro8 : ∀ (off : Int64), 0 ≤ off.toInt →
          op.toFlat + off.toInt + 8 ≤ (op.toFlat + Buffed.Operation.range op ctx.spec).upper →
          ctxBuf.mem.read64!
            (op.toM + off)
          = ctx.buf.mem.read64! (op.toM + off) := by
        intro off hoff hoff2
        apply hread
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
      have hro4 : ∀ (off : Int64), 0 ≤ off.toInt →
          op.toFlat + off.toInt + 4 ≤ (op.toFlat + Buffed.Operation.range op ctx.spec).upper →
          ctxBuf.mem.read32!
            (op.toM + off)
          = ctx.buf.mem.read32! (op.toM + off) := by
        intro off hoff hoff2
        apply hread32
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
      have hget : Veir.OperationPtr.get! op ctxSpec = Veir.OperationPtr.get! op ctx.spec := by grind
      constructor
      · -- MatchesBase
        constructor
        · have := henc.prev
          simp only [Buffed.OperationMPtr.readPrev!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.prev (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.next
          simp only [Buffed.OperationMPtr.readNext!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.next (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.parent
          simp only [Buffed.OperationMPtr.readParent!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.parent (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.opType
          simp only [Buffed.OperationMPtr.readOpType!] at this ⊢
          rw [hro4 Buffed.Operation.Offsets.opType (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.attrs
          simp only [Buffed.OperationMPtr.readAttrs!, hattr] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.attrs (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
      · -- MatchesBlockOperands
        constructor
        · have := henc.numBlockOperands
          simp only [Buffed.OperationMPtr.readNumBlockOperands!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.numBlockOperands (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · intro bo boIb heq
          have boIb' : bo.InBounds ctx.spec := by
            have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.blockOperand bo) hspec).mp (by simpa using boIb)
            grind
          have := henc.blockOperands bo boIb' heq
          have hboMeq : bo.toM ctxSpec = bo.toM ctx.spec := by
            simp only [Veir.BlockOperandPtr.toM, Veir.BlockOperandPtr.toFlat]
            grind [layout_grind]
          have hbogeteq : bo.get! ctxSpec = bo.get! ctx.spec := by grind
          have haft := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) bo boIb'
          have hboM : (bo.toM ctx.spec).toNat = bo.toFlat ctx.spec := by
            simp only [Veir.BlockOperandPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.BlockOperandPtr.toFlat]
          have hbo : ∀ (off : Int64), 0 ≤ off.toInt →
              off.toInt + 8 ≤ Buffed.BlockOperand.Offsets.afterInt →
              ctxBuf.mem.read64!
                ((bo.toM ctx.spec) + off)
              = ctx.buf.mem.read64! ((bo.toM ctx.spec) + off) := by
            intro off hoff hoff2
            apply hread
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              simp only [Buffed.IRBufContext.size_def] at haft <;> grind
          constructor
          · have := this.nextUse
            simp only [Buffed.BlockOperandMPtr.readNextUse!, hboMeq, hbogeteq] at this ⊢
            rw [hbo Buffed.BlockOperand.Offsets.nextUse (by decide) (by decide)]
            grind [layout_grind]
          · have := this.back
            simp only [Buffed.BlockOperandMPtr.readBack!, hboMeq, hbogeteq] at this ⊢
            rw [hbo Buffed.BlockOperand.Offsets.back (by decide) (by decide)]
            grind [layout_grind]
          · have := this.owner
            simp only [Buffed.BlockOperandMPtr.readOwner!, hboMeq, hbogeteq] at this ⊢
            rw [hbo Buffed.BlockOperand.Offsets.owner (by decide) (by decide)]
            grind [layout_grind]
          · have := this.value
            simp only [Buffed.BlockOperandMPtr.readValue!, hboMeq, hbogeteq] at this ⊢
            rw [hbo Buffed.BlockOperand.Offsets.value (by decide) (by decide)]
            grind [layout_grind]
      · -- MatchesRegions
        have hoff8n : Buffed.OperationMPtr.readNumOperands!
            ctxBuf op.toM
            = Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.readNumOperands!]
          rw [hro8 Buffed.Operation.Offsets.numOperands (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
        have hoff8b : Buffed.OperationMPtr.readNumBlockOperands!
            ctxBuf op.toM
            = Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.readNumBlockOperands!]
          rw [hro8 Buffed.Operation.Offsets.numBlockOperands (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
        have hoff4t : Buffed.OperationMPtr.readOpType!
            ctxBuf op.toM
            = Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.readOpType!]
          rw [hro4 Buffed.Operation.Offsets.opType (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
        have hcro : Buffed.OperationMPtr.computeRegionsOffset!
            ctxBuf op.toM
            = Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.computeRegionsOffset!,
            Buffed.OperationMPtr.computeBlockOperandsOffset!, Buffed.OperationMPtr.computeOperandsOffset!,
            hoff8n, hoff8b, hoff4t]
        constructor
        · have := henc.numRegions
          simp only [Buffed.OperationMPtr.readNumRegions!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.numRegions (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · intro idx idxIn
          have := henc.regions idx (by grind)
          have hgetreg : op.getRegion! ctxSpec idx = op.getRegion! ctx.spec idx := by grind
          have hnth : Buffed.OperationMPtr.readNthRegion!
              ctxBuf op.toM idx.toUInt64
              = Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx.toUInt64 := by
            simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!, hcro]
            have hii := ctx.sim.repr.operations_indices op holdib |>.capRegions
            have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op holdib
            apply hread
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              grind [layout_grind, OperationPtr.computeRegionsOffset!_ideal, UInt64.toNat_mul]
          rw [hnth, hgetreg]
          exact this
      · -- MatchesOperands
        constructor
        · have := henc.numOperands
          simp only [Buffed.OperationMPtr.readNumOperands!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.numOperands (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · intro oper operIb heq
          have operIb' : oper.InBounds ctx.spec := by
            have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.opOperand oper) hspec).mp (by simpa using operIb)
            grind
          have := henc.operands oper operIb' heq
          have hoMeq : oper.toM ctxSpec = oper.toM ctx.spec := by
            simp only [Veir.OpOperandPtr.toM, Veir.OpOperandPtr.toFlat]; grind [layout_grind]
          have hogeteq : oper.get! ctxSpec = oper.get! ctx.spec := by grind
          have haft := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper operIb'
          have hoM : (oper.toM ctx.spec).toNat = oper.toFlat ctx.spec := by
            simp only [Veir.OpOperandPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.OpOperandPtr.toFlat]
          have ho : ∀ (off : Int64), 0 ≤ off.toInt →
              off.toInt + 8 ≤ Buffed.OpOperand.Offsets.afterInt →
              ctxBuf.mem.read64!
                ((oper.toM ctx.spec) + off)
              = ctx.buf.mem.read64! ((oper.toM ctx.spec) + off) := by
            intro off hoff hoff2
            apply hread
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              simp only [Buffed.IRBufContext.size_def] at haft <;> grind
          constructor
          · have := this.nextUse
            simp only [Buffed.OpOperandMPtr.readNextUse!, hoMeq, hogeteq] at this ⊢
            rw [ho Buffed.OpOperand.Offsets.nextUse (by decide) (by decide)]
            grind [layout_grind]
          · have := this.back
            simp only [Buffed.OpOperandMPtr.readBack!, hoMeq, hogeteq] at this ⊢
            rw [ho Buffed.OpOperand.Offsets.back (by decide) (by decide)]
            grind [layout_grind]
          · have := this.owner
            simp only [Buffed.OpOperandMPtr.readOwner!, hoMeq, hogeteq] at this ⊢
            rw [ho Buffed.OpOperand.Offsets.owner (by decide) (by decide)]
            grind [layout_grind]
          · have := this.value
            simp only [Buffed.OpOperandMPtr.readValue!, hoMeq, hogeteq] at this ⊢
            rw [ho Buffed.OpOperand.Offsets.value (by decide) (by decide)]
            grind [layout_grind]
      · -- MatchesResults
        constructor
        · have := henc.numResults
          simp only [Buffed.OperationMPtr.readNumResults!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.numResults (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · intro res resIb heq
          have resIb' : res.InBounds ctx.spec := by
            have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.opResult res) hspec).mp (by simpa using resIb)
            grind
          have := henc.results res resIb' heq
          have hrMeq : res.toM ctxSpec = res.toM ctx.spec := by
            simp only [Veir.OpResultPtr.toM, Veir.OpResultPtr.toFlat]; grind [layout_grind]
          have hrgeteq : res.get! ctxSpec = res.get! ctx.spec := by grind
          have haft := Sim.OpResultPtr.after_lt_ctx (ctx := ctx) res resIb'
          have hrM : (res.toM ctx.spec).toNat = res.toFlat ctx.spec := by
            simp only [Veir.OpResultPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.OpResultPtr.toFlat]
          have hr : ∀ (off : Int64), 0 ≤ off.toInt →
              off.toInt + 8 ≤ Buffed.OpResult.Offsets.afterInt →
              ctxBuf.mem.read64!
                ((res.toM ctx.spec) + off)
              = ctx.buf.mem.read64! ((res.toM ctx.spec) + off) := by
            intro off hoff hoff2
            apply hread
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
          have hr0 : ctxBuf.mem.read64!
                (res.toM ctx.spec)
              = ctx.buf.mem.read64! (res.toM ctx.spec) := by
            have := hr 0 (by decide) (by decide)
            simpa using this
          constructor
          · have := this.kind
            simp only [Buffed.OpResultMPtr.readKind!, hrMeq] at this ⊢
            rw [hr0]; exact this
          · have := this.typee
            simp only [Buffed.OpResultMPtr.readType!, hrMeq, hrgeteq, hattr] at this ⊢
            rw [hr Buffed.ValueImpl.Offsets.type (by decide) (by decide)]; exact this
          · have := this.firstUse
            simp only [Buffed.OpResultMPtr.readFirstUse!, hrMeq, hrgeteq] at this ⊢
            rw [hr Buffed.ValueImpl.Offsets.firstUse (by decide) (by decide)]
            grind [layout_grind]
          · have := this.index
            simp only [Buffed.OpResultMPtr.readIndex!, hrMeq, hrgeteq] at this ⊢
            rw [hr Buffed.OpResult.Offsets.index (by decide) (by decide)]
            grind [layout_grind]
          · have := this.owner
            simp only [Buffed.OpResultMPtr.readOwner!, hrMeq, hrgeteq] at this ⊢
            rw [hr Buffed.OpResult.Offsets.owner (by decide) (by decide)]
            grind [layout_grind]
    · -- encoding_block
      intro blk blkIb
      rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block blk) hspec).mp (by simpa using blkIb)
        with hold | hnew | hfu
      · -- Old block: reads unchanged (hread) and get! preserved.
        clear hctxBuf
        have holdib : blk.InBounds ctx.spec := by simpa using hold
        have henc := ctx.sim.encoding_block blk holdib
        have hblkgeteq : blk.get! ctxSpec = blk.get! ctx.spec := by grind
        have haft := Sim.BlockPtr.after_lt_ctx (ctx := ctx) blk holdib
        have hblkM : blk.toM.toNat = blk.toFlat := by
          simp only [Veir.BlockPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.BlockPtr.toFlat]
        have hb : ∀ (off : Int64), 0 ≤ off.toInt →
            blk.toFlat + off.toInt + 8 ≤ blk.id + Buffed.Block.Offsets.afterInt blk ctx.spec →
            ctxBuf.mem.read64!
              (blk.toM + off)
            = ctx.buf.mem.read64! (blk.toM + off) := by
          intro off hoff hoff2
          apply hread
          rw [UInt64.uint64_add_int64_toNat_lt] <;>
            simp only [Buffed.IRBufContext.size_def] at haft <;>
            simp only [Veir.BlockPtr.toFlat] at * <;> grind
        constructor
        · -- MatchesBase
          constructor
          · have := henc.firstUse
            simp only [Buffed.BlockMPtr.readFirstUse!, hblkgeteq] at this ⊢
            rw [hb Buffed.Block.Offsets.firstUse (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
            grind [layout_grind]
          · have := henc.prev
            simp only [Buffed.BlockMPtr.readPrev!, hblkgeteq] at this ⊢
            rw [hb Buffed.Block.Offsets.prev (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
            grind [layout_grind]
          · have := henc.next
            simp only [Buffed.BlockMPtr.readNext!, hblkgeteq] at this ⊢
            rw [hb Buffed.Block.Offsets.next (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
            grind [layout_grind]
          · have := henc.parent
            simp only [Buffed.BlockMPtr.readParent!, hblkgeteq] at this ⊢
            rw [hb Buffed.Block.Offsets.parent (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
            grind [layout_grind]
          · have := henc.firstOp
            simp only [Buffed.BlockMPtr.readFirstOp!, hblkgeteq] at this ⊢
            rw [hb Buffed.Block.Offsets.firstOp (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
            grind [layout_grind]
          · have := henc.lastOp
            simp only [Buffed.BlockMPtr.readLastOp!, hblkgeteq] at this ⊢
            rw [hb Buffed.Block.Offsets.lastOp (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
            grind [layout_grind]
        · -- MatchesArguments
          constructor
          · have := henc.numArguments
            simp only [Buffed.BlockMPtr.readNumArguments!, hblkgeteq] at this ⊢
            rw [hb Buffed.Block.Offsets.numArguments (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
            grind [layout_grind]
          · intro arg argIn heq
            have argIb' : arg.InBounds ctx.spec := by
              have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.blockArgument arg) hspec).mp (by simpa using argIn)
              grind
            have := henc.arguments arg argIb' heq
            have hageteq : arg.get! ctxSpec = arg.get! ctx.spec := by grind
            have haaft := Sim.BlockArgumentPtr.after_lt_ctx (ctx := ctx) arg argIb'
            have haM : arg.toM.toNat = arg.toFlat := by
              simp only [Veir.BlockArgumentPtr.toM]
              grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.BlockArgumentPtr.toFlat]
            have ha : ∀ (off : Int64), 0 ≤ off.toInt →
                off.toInt + 8 ≤ Buffed.BlockArgument.Offsets.afterInt →
                ctxBuf.mem.read64!
                  (arg.toM + off)
                = ctx.buf.mem.read64! (arg.toM + off) := by
              intro off hoff hoff2
              apply hread
              rw [UInt64.uint64_add_int64_toNat_lt] <;>
                simp only [Buffed.IRBufContext.size_def] at haaft <;> grind
            have ha0 : ctxBuf.mem.read64!
                  arg.toM
                = ctx.buf.mem.read64! arg.toM := by
              have := ha 0 (by decide) (by decide)
              simpa using this
            constructor
            · have := this.kind
              simp only [Buffed.BlockArgumentMPtr.readKind!] at this ⊢
              rw [ha0]; exact this
            · have := this.type
              simp only [Buffed.BlockArgumentMPtr.readType!, hageteq, hattr] at this ⊢
              rw [ha Buffed.ValueImpl.Offsets.type (by decide) (by decide)]; exact this
            · have := this.firstUse
              simp only [Buffed.BlockArgumentMPtr.readFirstUse!, hageteq] at this ⊢
              rw [ha Buffed.ValueImpl.Offsets.firstUse (by decide) (by decide)]
              grind [layout_grind]
            · have := this.index
              simp only [Buffed.BlockArgumentMPtr.readIndex!, hageteq] at this ⊢
              rw [ha Buffed.BlockArgument.Offsets.index (by decide) (by decide)]
              grind [layout_grind]
            · have := this.owner
              simp only [Buffed.BlockArgumentMPtr.readOwner!, hageteq] at this ⊢
              rw [ha Buffed.BlockArgument.Offsets.owner (by decide) (by decide)]
              grind [layout_grind]
      · -- New block = ptrSpec: all 7 fields read the fresh writes (each returning `none`/numArgs).
        simp only [GenericPtr.block.injEq] at hnew
        subst blk
        have hget : Veir.BlockPtr.get! ptrSpec ctxSpec = Block.empty numArgs.toNat := by
          have := BlockPtr.get!_BlockPtr_allocEmptyAtAddress (block := ptrSpec) hspec
          simpa using this
        have htoM : ptrSpec.toM = ctx.buf.usize := by
          simp only [hptr, BlockPtr.toM, BlockPtr.toFlat]; clear hctxBuf; grind
        -- Write offsets: firstUse=0, prev=8, next=16, parent=24, firstOp=32, lastOp=40, numArguments=48.
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
        constructor
        · -- MatchesBase: firstUse/prev/next/parent/firstOp/lastOp all read `none`.
          constructor
          · -- firstUse: read at usize+0, hits writeFirstUse (passing writeNumArguments; the tower is
            -- writeLastOp(...(writeFirstUse(writeNumArguments ...)))), so firstUse is the 2nd-innermost.
            simp only [← hctxBuf, Sim.OptionBlockOperandPtr.Sim, hget, Block.empty, Buffed.BlockMPtr.readFirstUse!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            rfl
          · -- prev: read at usize+8, hits writePrev.
            simp only [← hctxBuf, Sim.OptionBlockPtr.Sim, hget, Block.empty, Buffed.BlockMPtr.readPrev!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            rfl
          · -- next: read at usize+16, hits writeNext.
            simp only [← hctxBuf, Sim.OptionBlockPtr.Sim, hget, Block.empty, Buffed.BlockMPtr.readNext!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            rfl
          · -- parent: read at usize+24, hits writeParent (a region pointer).
            simp only [← hctxBuf, Sim.OptionRegionPtr.Sim, hget, Block.empty, Buffed.BlockMPtr.readParent!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            rfl
          · -- firstOp: read at usize+32, hits writeFirstOp.
            simp only [← hctxBuf, Sim.OptionOperationPtr.Sim, hget, Block.empty, Buffed.BlockMPtr.readFirstOp!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
            rfl
          · -- lastOp: read at usize+40, hits writeLastOp (outermost).
            simp only [← hctxBuf, Sim.OptionOperationPtr.Sim, hget, Block.empty, Buffed.BlockMPtr.readLastOp!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            rw [ExArray.read64!_blit64_self]
            rfl
        · -- MatchesArguments: numArguments reads numArgs; the arguments loop is vacuous (empty block).
          constructor
          · -- numArguments: read at usize+48, hits writeNumArguments (innermost).
            simp only [← hctxBuf, hget, Block.empty, Buffed.BlockMPtr.readNumArguments!,
              Buffed.BlockMPtr.writeLastOp, Buffed.BlockMPtr.writeFirstOp, Buffed.BlockMPtr.writeParent,
              Buffed.BlockMPtr.writeNext, Buffed.BlockMPtr.writePrev, Buffed.BlockMPtr.writeFirstUse,
              Buffed.BlockMPtr.writeNumArguments, htoM]
            -- The stored value is `numArgs`; the spec's numArguments = capArguments = numArgs.toNat.
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
              ExArray.read64!_blit64_self]
          · -- arguments loop: no in-bounds argument exists in an empty block.
            intro arg argIn heq
            exfalso
            -- `arg.InBounds ctxSpec` forces `arg.InBounds ctx.spec` (the insert adds no arguments), but
            -- `arg.block = ptrSpec` is the fresh block, absent from `ctx.spec` — contradiction.
            have hold : arg.InBounds ctx.spec := by
              rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.blockArgument arg) hspec).mp
                (by simpa using argIn) with h | h | h
              · simpa using h
              · exact absurd h (by simp)
              · exact absurd h (by simp)
            -- `arg.block ∈ ctx.spec.blocks` (from `arg.InBounds ctx.spec`), but `arg.block = ptrSpec` fresh.
            rw [Veir.BlockArgumentPtr.inBounds_def] at hold
            obtain ⟨hbib, _⟩ := hold
            rw [heq] at hbib
            -- `ptrSpec = ⟨usize.toNat⟩ = ⟨mem.size⟩`, contradicting `slot_free`.
            have hpeq : ptrSpec = (⟨ctx.buf.mem.size⟩ : Veir.BlockPtr) := by
              rw [hptr]; grind
            rw [hpeq] at hbib
            exact (Sim.BlockPtr.slot_free ctx) hbib
      · exact absurd hfu (by simp)
    · -- encoding_region
      clear hctxBuf
      intro rg rgIb
      have holdib : rg.InBounds ctx.spec := by
        have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.region rg) hspec).mp (by simpa using rgIb)
        grind
      have hgetp : Veir.RegionPtr.get! rg ctxSpec = Veir.RegionPtr.get! rg ctx.spec := by grind
      have henc := ctx.sim.encoding_region rg holdib
      have hinb := ctx.sim.in_bounds (.region rg) (by simpa using holdib)
      simp only [TopLevelPtr.range, Veir.RegionPtr.range, Veir.RegionPtr.toFlat,
        IsIncludedIN, ExArray.range_upper, Buffed.Region.range] at hinb
      have hrgM : rg.toM.toNat = rg.id := by
        simp only [Veir.RegionPtr.toM, Veir.RegionPtr.toFlat]
        grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      have hafter : (Buffed.Region.Offsets.after.toInt : Int) = 24 := by decide
      have hrf : ∀ (off : Int64), 0 ≤ off.toInt → off.toInt + 8 ≤ 24 →
          ctxBuf.mem.read64!
            (rg.toM + off)
          = ctx.buf.mem.read64! (rg.toM + off) := by
        intro off hoff hoff2
        apply hread
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
      constructor
      · have := henc.firstBlock
        simp only [Buffed.RegionMPtr.readFirstBlock!, hgetp]
        rw [hrf Buffed.Region.Offsets.firstBlock (by decide) (by decide)] at *
        simpa [Buffed.RegionMPtr.readFirstBlock!] using this
      · have := henc.lastBlock
        simp only [Buffed.RegionMPtr.readLastBlock!, hgetp]
        rw [hrf Buffed.Region.Offsets.lastBlock (by decide) (by decide)] at *
        simpa [Buffed.RegionMPtr.readLastBlock!] using this
      · have := henc.parent
        simp only [Buffed.RegionMPtr.readParent!, hgetp]
        rw [hrf Buffed.Region.Offsets.parent (by decide) (by decide)] at *
        simpa [Buffed.RegionMPtr.readParent!] using this
    · -- attr_empty
      rw [hattr]
      exact ctx.sim.attr_empty

@[inline]
def Sim.BlockPtr.allocEmpty (ctx : Sim.IRContext OpInfo) (numArgs : UInt64) : Option (Sim.BlockPtr × Sim.IRContext OpInfo) :=
  -- `numArgs` bound needed by `allocEmptyImpl`.
  if hnumArgs : numArgs.toNat ≤ Buffed.countCard then
    match himpl : allocEmptyImpl ctx.buf numArgs hnumArgs with
    | none => none
    | some (ctxBuf, ptrImpl) =>
      let specRes := (Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptrImpl.toNat).specGet!
      have hspec : Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptrImpl.toNat = some specRes := by
        have hptr : ptrImpl = ctx.buf.usize := by
          simp only [allocEmptyImpl] at himpl
          split at himpl <;> grind
        have hfree := Sim.BlockPtr.slot_free ctx
        simp only [Veir.BlockPtr.inBounds_def] at hfree
        have husz := ctx.buf.usize_toNat
        have hs := ctx.buf.size_def
        have hsome := Veir.BlockPtr.allocEmptyAtAddress_isSome_of_not_mem
          (ctx := ctx.spec) (capArguments := numArgs.toNat) (address := ptrImpl.toNat) (by grind)
        simp only [specRes, Option.specGet!]
        exact (Option.some_get! _ hsome).symm
      some ⟨⟨ptrImpl, specRes.2⟩, ⟨ctxBuf, specRes.1, allocEmpty_sim ctx numArgs hnumArgs himpl hspec⟩⟩
  else
    none

/-- Strengthening of `allocEmpty_spec`: the spec-level block is allocated exactly at the
address of the returned impl pointer. -/
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
      -- The remaining goal is `allocEmptyAtAddress … = some (specGet!.fst, specGet!.snd)`.
      have hptr : ptrImpl = ctx.buf.usize := by
        simp only [allocEmptyImpl] at himpl
        split at himpl <;> grind
      have hfree := Sim.BlockPtr.slot_free ctx
      simp only [Veir.BlockPtr.inBounds_def] at hfree
      have husz := ctx.buf.usize_toNat
      have hs := ctx.buf.size_def
      have hsome := Veir.BlockPtr.allocEmptyAtAddress_isSome_of_not_mem
        (ctx := ctx.spec) (capArguments := numArgs.toNat) (address := ptrImpl.toNat) (by grind)
      simp only [Option.specGet!]
      rw [← Option.some_get! _ hsome]
      simp
  · exact absurd h (by simp)

@[grind! .]
theorem Sim.BlockPtr.allocEmpty_spec {ctx : Sim.IRContext OpInfo} numArgs :
    allocEmpty ctx numArgs = some ⟨ptr, ctx'⟩ →
    ∃ addr, Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat addr = some ⟨ctx'.spec, ptr.spec⟩:=
  fun h => ⟨ptr.impl.toNat, Sim.BlockPtr.allocEmpty_spec' numArgs h⟩

buffed
def Sim.BlockPtr.setParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl (by prove_setLinkBoundsBlock ctx ptr), ptr.spec.setParent ctx.spec parent.spec (by grind), by prove_setLinkSim ctx Buffed.BlockMPtr.writeParent⟩

open Classical in
noncomputable def Sim.BlockPtr.setParent! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.parent).toInt + Buffed.Block.Sizes.parent.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeParent ctx.buf ptr.impl parent.impl h₁,
      spec := ptr.spec.setParent! ctx.spec parent.spec } then
    ⟨ptr.impl.writeParent ctx.buf parent.impl h₁, ptr.spec.setParent! ctx.spec parent.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setParent_eq_setParent! (ctx : IRContext OpInfo) ptr parent ib parentIb :
    setParent ctx ptr parent ib parentIb = setParent! ctx ptr parent := by
  simp [setParent_def, setParentSim, setParent!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent ctx ptr parent ib parentIb).spec = ptr.spec.setParent ctx.spec parent.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockPtr.setParent!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent! ctx ptr parent).spec = ptr.spec.setParent! ctx.spec parent.spec := by
  grind

buffed
def Sim.BlockPtr.getParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionRegionPtr :=
  ⟨ptr.impl.readParent ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (ptr.spec.get ctx.spec).parent⟩

@[simp, grind =]
theorem Sim.BlockPtr.getParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).spec = (ptr.spec.get ctx.spec).parent := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getParent_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).parent
  grind [getParentSim, getParent_def]

buffed
def Sim.BlockPtr.getParent!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionRegionPtr :=
  ⟨ptr.impl.readParent! ctx.buf, (ptr.spec.get! ctx.spec).parent⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getParent_eq_getParent! (ctx : IRContext OpInfo) ptr ib :
    getParent ctx ptr ib = getParent! ctx ptr := by
  simp [getParent_def, getParentSim, getParent!_def, getParent!Sim]
  grind

buffed
def Sim.BlockPtr.setFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl (by prove_setLinkBoundsBlock ctx ptr), ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind), by prove_setLinkSim ctx Buffed.BlockMPtr.writeFirstUse⟩

open Classical in
noncomputable def Sim.BlockPtr.setFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.firstUse).toInt + Buffed.Block.Sizes.firstUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeFirstUse ctx.buf ptr.impl firstUse.impl h₁,
      spec := ptr.spec.setFirstUse! ctx.spec firstUse.spec } then
    ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl h₁, ptr.spec.setFirstUse! ctx.spec firstUse.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse_def, setFirstUseSim, setFirstUse!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockPtr.setFirstUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse! ctx ptr firstUse).spec = ptr.spec.setFirstUse! ctx.spec firstUse.spec := by
  grind

buffed
def Sim.BlockPtr.getFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (ptr.spec.get ctx.spec).firstUse⟩

@[simp, grind =]
theorem Sim.BlockPtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstUse := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).firstUse
  grind [getFirstUseSim, getFirstUse_def]

buffed
def Sim.BlockPtr.getFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (ptr.spec.get! ctx.spec).firstUse⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse_def, getFirstUseSim, getFirstUse!_def, getFirstUse!Sim]
  grind

buffed
def Sim.BlockPtr.setFirstOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (firstOpIb : firstOp.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstOp ctx.buf firstOp.impl (by prove_setLinkBoundsBlock ctx ptr), ptr.spec.setFirstOp ctx.spec firstOp.spec (by grind), by prove_setLinkSim ctx Buffed.BlockMPtr.writeFirstOp⟩

open Classical in
noncomputable def Sim.BlockPtr.setFirstOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.firstOp).toInt + Buffed.Block.Sizes.firstOp.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeFirstOp ctx.buf ptr.impl firstOp.impl h₁,
      spec := ptr.spec.setFirstOp! ctx.spec firstOp.spec } then
    ⟨ptr.impl.writeFirstOp ctx.buf firstOp.impl h₁, ptr.spec.setFirstOp! ctx.spec firstOp.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setFirstOp_eq_setFirstOp! (ctx : IRContext OpInfo) ptr firstOp ib firstOpIb :
    setFirstOp ctx ptr firstOp ib firstOpIb = setFirstOp! ctx ptr firstOp := by
  simp [setFirstOp_def, setFirstOpSim, setFirstOp!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setFirstOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (firstOpIb : firstOp.InBounds ctx) :
    (setFirstOp ctx ptr firstOp ib firstOpIb).spec = ptr.spec.setFirstOp ctx.spec firstOp.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockPtr.setFirstOp!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (firstOpIb : firstOp.InBounds ctx) :
    (setFirstOp! ctx ptr firstOp).spec = ptr.spec.setFirstOp! ctx.spec firstOp.spec := by
  grind

buffed
def Sim.BlockPtr.getFirstOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readFirstOp ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (ptr.spec.get ctx.spec).firstOp⟩

@[simp, grind =]
theorem Sim.BlockPtr.getFirstOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstOp := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getFirstOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).firstOp
  grind [getFirstOpSim, getFirstOp_def]

buffed
def Sim.BlockPtr.getFirstOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readFirstOp! ctx.buf, (ptr.spec.get! ctx.spec).firstOp⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getFirstOp_eq_getFirstOp! (ctx : IRContext OpInfo) ptr ib :
    getFirstOp ctx ptr ib = getFirstOp! ctx ptr := by
  simp [getFirstOp_def, getFirstOpSim, getFirstOp!_def, getFirstOp!Sim]
  grind

buffed
def Sim.BlockPtr.setLastOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (lastOpIb : lastOp.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeLastOp ctx.buf lastOp.impl (by prove_setLinkBoundsBlock ctx ptr), ptr.spec.setLastOp ctx.spec lastOp.spec (by grind), by prove_setLinkSim ctx Buffed.BlockMPtr.writeLastOp⟩

open Classical in
noncomputable def Sim.BlockPtr.setLastOp! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.lastOp).toInt + Buffed.Block.Sizes.lastOp.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeLastOp ctx.buf ptr.impl lastOp.impl h₁,
      spec := ptr.spec.setLastOp! ctx.spec lastOp.spec } then
    ⟨ptr.impl.writeLastOp ctx.buf lastOp.impl h₁, ptr.spec.setLastOp! ctx.spec lastOp.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setLastOp_eq_setLastOp! (ctx : IRContext OpInfo) ptr lastOp ib lastOpIb :
    setLastOp ctx ptr lastOp ib lastOpIb = setLastOp! ctx ptr lastOp := by
  simp [setLastOp_def, setLastOpSim, setLastOp!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setLastOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (lastOpIb : lastOp.InBounds ctx) :
    (setLastOp ctx ptr lastOp ib lastOpIb).spec = ptr.spec.setLastOp ctx.spec lastOp.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockPtr.setLastOp!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (lastOpIb : lastOp.InBounds ctx) :
    (setLastOp! ctx ptr lastOp).spec = ptr.spec.setLastOp! ctx.spec lastOp.spec := by
  grind

buffed
def Sim.BlockPtr.getLastOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readLastOp ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (ptr.spec.get ctx.spec).lastOp⟩

@[simp, grind =]
theorem Sim.BlockPtr.getLastOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getLastOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).lastOp := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getLastOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getLastOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).lastOp
  grind [getLastOpSim, getLastOp_def]

buffed
def Sim.BlockPtr.getLastOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readLastOp! ctx.buf, (ptr.spec.get! ctx.spec).lastOp⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getLastOp_eq_getLastOp! (ctx : IRContext OpInfo) ptr ib :
    getLastOp ctx ptr ib = getLastOp! ctx ptr := by
  simp [getLastOp_def, getLastOpSim, getLastOp!_def, getLastOp!Sim]
  grind

buffed
def Sim.BlockPtr.setNextBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNext ctx.buf next.impl (by prove_setLinkBoundsBlock ctx ptr), ptr.spec.setNextBlock ctx.spec next.spec (by grind), by prove_setLinkSim ctx Buffed.BlockMPtr.writeNext⟩

open Classical in
noncomputable def Sim.BlockPtr.setNextBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.next).toInt + Buffed.Block.Sizes.next.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writeNext ctx.buf ptr.impl next.impl h₁,
      spec := ptr.spec.setNextBlock! ctx.spec next.spec } then
    ⟨ptr.impl.writeNext ctx.buf next.impl h₁, ptr.spec.setNextBlock! ctx.spec next.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setNextBlock_eq_setNextBlock! (ctx : IRContext OpInfo) ptr next ib nextIb :
    setNextBlock ctx ptr next ib nextIb = setNextBlock! ctx ptr next := by
  simp [setNextBlock_def, setNextBlockSim, setNextBlock!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setNextBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextBlock ctx ptr next ib nextIb).spec = ptr.spec.setNextBlock ctx.spec next.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockPtr.setNextBlock!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextBlock! ctx ptr next).spec = ptr.spec.setNextBlock! ctx.spec next.spec := by
  grind

buffed
def Sim.BlockPtr.getNextBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readNext ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (ptr.spec.get ctx.spec).next⟩

@[simp, grind =]
theorem Sim.BlockPtr.getNextBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getNextBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).next := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getNextBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getNextBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).next
  grind [getNextBlockSim, getNextBlock_def]

buffed
def Sim.BlockPtr.getNextBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readNext! ctx.buf, (ptr.spec.get! ctx.spec).next⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getNextBlock_eq_getNextBlock! (ctx : IRContext OpInfo) ptr ib :
    getNextBlock ctx ptr ib = getNextBlock! ctx ptr := by
  simp [getNextBlock_def, getNextBlockSim, getNextBlock!_def, getNextBlock!Sim]
  grind

buffed
def Sim.BlockPtr.setPrevBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writePrev ctx.buf prev.impl (by prove_setLinkBoundsBlock ctx ptr), ptr.spec.setPrevBlock ctx.spec prev.spec (by grind), by prove_setLinkSim ctx Buffed.BlockMPtr.writePrev⟩

open Classical in
noncomputable def Sim.BlockPtr.setPrevBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Block.Offsets.prev).toInt + Buffed.Block.Sizes.prev.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockMPtr.writePrev ctx.buf ptr.impl prev.impl h₁,
      spec := ptr.spec.setPrevBlock! ctx.spec prev.spec } then
    ⟨ptr.impl.writePrev ctx.buf prev.impl h₁, ptr.spec.setPrevBlock! ctx.spec prev.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setPrevBlock_eq_setPrevBlock! (ctx : IRContext OpInfo) ptr prev ib prevIb :
    setPrevBlock ctx ptr prev ib prevIb = setPrevBlock! ctx ptr prev := by
  simp [setPrevBlock_def, setPrevBlockSim, setPrevBlock!]
  split
  · grind
  · prove_setLinkBoundsBlock ctx ptr

@[simp, grind =]
theorem Sim.BlockPtr.setPrevBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevBlock ctx ptr prev ib prevIb).spec = ptr.spec.setPrevBlock ctx.spec prev.spec := by
  rfl

@[simp, grind =]
theorem Sim.BlockPtr.setPrevBlock!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevBlock! ctx ptr prev).spec = ptr.spec.setPrevBlock! ctx.spec prev.spec := by
  grind

buffed
def Sim.BlockPtr.getPrevBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readPrev ctx.buf (by prove_setLinkBoundsBlock ctx ptr), (ptr.spec.get ctx.spec).prev⟩

@[simp, grind =]
theorem Sim.BlockPtr.getPrevBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).prev := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getPrevBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).prev
  grind [getPrevBlockSim, getPrevBlock_def]

buffed
def Sim.BlockPtr.getPrevBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readPrev! ctx.buf, (ptr.spec.get! ctx.spec).prev⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getPrevBlock_eq_getPrevBlock! (ctx : IRContext OpInfo) ptr ib :
    getPrevBlock ctx ptr ib = getPrevBlock! ctx ptr := by
  simp [getPrevBlock_def, getPrevBlockSim, getPrevBlock!_def, getPrevBlock!Sim]
  grind

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

buffed
def Sim.BlockPtr.getArgumentPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.BlockArgumentPtr :=
  ⟨ptr.impl + Buffed.BlockMPtr.computeArgumentOffset index,
   ptr.spec.getArgument index.toNat⟩

buffed
def Sim.BlockPtr.getArgumentPtr!Sim (_ctx : IRContext OpInfo) (ptr : Sim.BlockPtr)
    (index : UInt64) : Sim.BlockArgumentPtr :=
  ⟨ptr.impl + Buffed.BlockMPtr.computeArgumentOffset! index,
   ptr.spec.getArgument index.toNat⟩

@[simp, grind =]
theorem Sim.BlockPtr.getArgumentPtr_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (index : UInt64) (ib : ptr.InBounds ctx) :
    (getArgumentPtr ctx ptr index ib).spec = ptr.spec.getArgument index.toNat := by
  rfl

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getArgumentPtr_eq_getArgumentPtr! (ctx : IRContext OpInfo) ptr index ib :
    getArgumentPtr ctx ptr index ib = getArgumentPtr! ctx ptr index := by
  simp [getArgumentPtr_def, getArgumentPtrSim, getArgumentPtr!_def, getArgumentPtr!Sim]

buffed
def Sim.RegionPtr.setParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl (by prove_setLinkBoundsRegion ctx ptr), ptr.spec.setParent ctx.spec parent.spec (by grind), by prove_setLinkSim ctx Buffed.RegionMPtr.writeParent⟩

open Classical in
noncomputable def Sim.RegionPtr.setParent! (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Region.Offsets.parent).toInt + Buffed.Region.Sizes.parent.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.RegionMPtr.writeParent ctx.buf ptr.impl parent.impl h₁,
      spec := ptr.spec.setParent! ctx.spec parent.spec } then
    ⟨ptr.impl.writeParent ctx.buf parent.impl h₁, ptr.spec.setParent! ctx.spec parent.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.setParent_eq_setParent! (ctx : IRContext OpInfo) ptr parent ib parentIb :
    setParent ctx ptr parent ib parentIb = setParent! ctx ptr parent := by
  simp [setParent_def, setParentSim, setParent!]
  split
  · grind
  · prove_setLinkBoundsRegion ctx ptr

@[simp, grind =]
theorem Sim.RegionPtr.setParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent ctx ptr parent ib parentIb).spec = ptr.spec.setParent ctx.spec parent.spec := by
  rfl

@[simp, grind =]
theorem Sim.RegionPtr.setParent!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent! ctx ptr parent).spec = ptr.spec.setParent! ctx.spec parent.spec := by
  grind

buffed
def Sim.RegionPtr.getParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readParent ctx.buf (by prove_setLinkBoundsRegion ctx ptr), (ptr.spec.get ctx.spec).parent⟩

@[simp, grind =]
theorem Sim.RegionPtr.getParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).spec = (ptr.spec.get ctx.spec).parent := by
  rfl

@[grind .]
theorem Sim.RegionPtr.getParent_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_region ptr.spec (by grind)).parent
  grind [getParentSim, getParent_def]

buffed
def Sim.RegionPtr.getParent!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readParent! ctx.buf, (ptr.spec.get! ctx.spec).parent⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.getParent_eq_getParent! (ctx : IRContext OpInfo) ptr ib :
    getParent ctx ptr ib = getParent! ctx ptr := by
  simp [getParent_def, getParentSim, getParent!_def, getParent!Sim]
  grind

buffed
def Sim.RegionPtr.setFirstBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (firstBlockIb : firstBlock.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstBlock ctx.buf firstBlock.impl (by prove_setLinkBoundsRegion ctx ptr), ptr.spec.setFirstBlock ctx.spec firstBlock.spec (by grind), by prove_setLinkSim ctx Buffed.RegionMPtr.writeFirstBlock⟩

open Classical in
noncomputable def Sim.RegionPtr.setFirstBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Region.Offsets.firstBlock).toInt + Buffed.Region.Sizes.firstBlock.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.RegionMPtr.writeFirstBlock ctx.buf ptr.impl firstBlock.impl h₁,
      spec := ptr.spec.setFirstBlock! ctx.spec firstBlock.spec } then
    ⟨ptr.impl.writeFirstBlock ctx.buf firstBlock.impl h₁, ptr.spec.setFirstBlock! ctx.spec firstBlock.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.setFirstBlock_eq_setFirstBlock! (ctx : IRContext OpInfo) ptr firstBlock ib firstBlockIb :
    setFirstBlock ctx ptr firstBlock ib firstBlockIb = setFirstBlock! ctx ptr firstBlock := by
  simp [setFirstBlock_def, setFirstBlockSim, setFirstBlock!]
  split
  · grind
  · prove_setLinkBoundsRegion ctx ptr

@[simp, grind =]
theorem Sim.RegionPtr.setFirstBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (firstBlockIb : firstBlock.InBounds ctx) :
    (setFirstBlock ctx ptr firstBlock ib firstBlockIb).spec = ptr.spec.setFirstBlock ctx.spec firstBlock.spec := by
  rfl

@[simp, grind =]
theorem Sim.RegionPtr.setFirstBlock!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (firstBlockIb : firstBlock.InBounds ctx) :
    (setFirstBlock! ctx ptr firstBlock).spec = ptr.spec.setFirstBlock! ctx.spec firstBlock.spec := by
  grind

buffed
def Sim.RegionPtr.getFirstBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readFirstBlock ctx.buf (by prove_setLinkBoundsRegion ctx ptr), (ptr.spec.get ctx.spec).firstBlock⟩

@[simp, grind =]
theorem Sim.RegionPtr.getFirstBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstBlock := by
  rfl

@[grind .]
theorem Sim.RegionPtr.getFirstBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_region ptr.spec (by grind)).firstBlock
  grind [getFirstBlockSim, getFirstBlock_def]

buffed
def Sim.RegionPtr.getFirstBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readFirstBlock! ctx.buf, (ptr.spec.get! ctx.spec).firstBlock⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.getFirstBlock_eq_getFirstBlock! (ctx : IRContext OpInfo) ptr ib :
    getFirstBlock ctx ptr ib = getFirstBlock! ctx ptr := by
  simp [getFirstBlock_def, getFirstBlockSim, getFirstBlock!_def, getFirstBlock!Sim]
  grind

buffed
def Sim.RegionPtr.setLastBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (lastBlockIb : lastBlock.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeLastBlock ctx.buf lastBlock.impl (by prove_setLinkBoundsRegion ctx ptr), ptr.spec.setLastBlock ctx.spec lastBlock.spec (by grind), by prove_setLinkSim ctx Buffed.RegionMPtr.writeLastBlock⟩

open Classical in
noncomputable def Sim.RegionPtr.setLastBlock! (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.Region.Offsets.lastBlock).toInt + Buffed.Region.Sizes.lastBlock.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.RegionMPtr.writeLastBlock ctx.buf ptr.impl lastBlock.impl h₁,
      spec := ptr.spec.setLastBlock! ctx.spec lastBlock.spec } then
    ⟨ptr.impl.writeLastBlock ctx.buf lastBlock.impl h₁, ptr.spec.setLastBlock! ctx.spec lastBlock.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.setLastBlock_eq_setLastBlock! (ctx : IRContext OpInfo) ptr lastBlock ib lastBlockIb :
    setLastBlock ctx ptr lastBlock ib lastBlockIb = setLastBlock! ctx ptr lastBlock := by
  simp [setLastBlock_def, setLastBlockSim, setLastBlock!]
  split
  · grind
  · prove_setLinkBoundsRegion ctx ptr

@[simp, grind =]
theorem Sim.RegionPtr.setLastBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (lastBlockIb : lastBlock.InBounds ctx) :
    (setLastBlock ctx ptr lastBlock ib lastBlockIb).spec = ptr.spec.setLastBlock ctx.spec lastBlock.spec := by
  rfl

@[simp, grind =]
theorem Sim.RegionPtr.setLastBlock!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (lastBlockIb : lastBlock.InBounds ctx) :
    (setLastBlock! ctx ptr lastBlock).spec = ptr.spec.setLastBlock! ctx.spec lastBlock.spec := by
  grind

buffed
def Sim.RegionPtr.getLastBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readLastBlock ctx.buf (by prove_setLinkBoundsRegion ctx ptr), (ptr.spec.get ctx.spec).lastBlock⟩

@[simp, grind =]
theorem Sim.RegionPtr.getLastBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getLastBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).lastBlock := by
  rfl

@[grind .]
theorem Sim.RegionPtr.getLastBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getLastBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_region ptr.spec (by grind)).lastBlock
  grind [getLastBlockSim, getLastBlock_def]

buffed
def Sim.RegionPtr.getLastBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readLastBlock! ctx.buf, (ptr.spec.get! ctx.spec).lastBlock⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.getLastBlock_eq_getLastBlock! (ctx : IRContext OpInfo) ptr ib :
    getLastBlock ctx ptr ib = getLastBlock! ctx ptr := by
  simp [getLastBlock_def, getLastBlockSim, getLastBlock!_def, getLastBlock!Sim]
  grind

buffed
def Sim.ValuePtr.setFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl (by prove_setLinkBoundsValue), ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind), by prove_setLinkSim ctx Buffed.ValueImplMPtr.writeFirstUse⟩

open Classical in
noncomputable def Sim.ValuePtr.setFirstUse! (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : (ptr.impl + Buffed.ValueImpl.Offsets.firstUse).toInt + Buffed.ValueImpl.Sizes.firstUse.toInt ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.ValueImplMPtr.writeFirstUse ctx.buf ptr.impl firstUse.impl h₁,
      spec := ptr.spec.setFirstUse! ctx.spec firstUse.spec } then
    ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl h₁, ptr.spec.setFirstUse! ctx.spec firstUse.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.ValuePtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse_def, setFirstUseSim, setFirstUse!]
  split
  · grind
  · prove_setLinkBoundsValue

@[simp, grind =]
theorem Sim.ValuePtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  rfl

@[simp, grind =]
theorem Sim.ValuePtr.setFirstUse!_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse! ctx ptr firstUse).spec = ptr.spec.setFirstUse! ctx.spec firstUse.spec := by
  grind

buffed
def Sim.ValuePtr.getFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf (by prove_setLinkBoundsValue), ptr.spec.getFirstUse ctx.spec (by grind)⟩

@[simp, grind =]
theorem Sim.ValuePtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = ptr.spec.getFirstUse ctx.spec (by grind) := by
  rfl

@[grind .]
theorem Sim.ValuePtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  cases heq : ptr.spec
  case opResult res =>
    have := ctx.sim.encoding_op res.op (by grind [Veir.OpResultPtr.inBounds_def])
      |>.results res (by grind) (by grind) |>.firstUse
    simp_all [getFirstUseSim, getFirstUse_def, eq_bang]
    unfold Buffed.OpResultMPtr.readFirstUse! at this
    unfold Buffed.ValueImplMPtr.readFirstUse!
    grind
  case blockArgument arg =>
    have := ctx.sim.encoding_block arg.block (by grind [Veir.BlockArgumentPtr.inBounds_def])
      |>.arguments arg (by grind) (by grind) |>.firstUse
    simp_all [getFirstUseSim, getFirstUse_def, eq_bang]
    unfold Buffed.BlockArgumentMPtr.readFirstUse! at this
    unfold Buffed.ValueImplMPtr.readFirstUse!
    grind

buffed
def Sim.ValuePtr.getFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, ptr.spec.getFirstUse! ctx.spec⟩

@[eq_bang, grind _=_]
theorem Sim.ValuePtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse_def, getFirstUseSim, getFirstUse!_def, getFirstUse!Sim]
  grind

buffed
def Sim.OpOperandPtrPtr.setSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtrPtr)
    (value : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.write ctx.buf value.impl (by
    have : ctx.buf.mem.size < 2^63 := by grind
    have := Sim.OpOperandPtrPtr.after_lt_ctx (ctx := ctx) ptr.spec (by grind)
    grind [layout_grind]),
   ptr.spec.set ctx.spec value.spec (by grind), by prove_setLinkSim ctx Buffed.OpOperandPtrMPtr.write⟩

open Classical in
noncomputable def Sim.OpOperandPtrPtr.set! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtrPtr)
    (value : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : ptr.impl.toNat + Buffed.ptrSize.toNat ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.OpOperandPtrMPtr.write ctx.buf ptr.impl value.impl h₁,
      spec := ptr.spec.set! ctx.spec value.spec } then
    ⟨ptr.impl.write ctx.buf value.impl h₁, ptr.spec.set! ctx.spec value.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtrPtr.set_eq_set! (ctx : IRContext OpInfo) ptr value ib valueIb :
    set ctx ptr value ib valueIb = set! ctx ptr value := by
  simp [set_def, setSim, set!]
  split
  · grind
  · have : ctx.buf.mem.size < 2^63 := by grind
    have := Sim.OpOperandPtrPtr.after_lt_ctx (ctx := ctx) ptr.spec (by grind)
    grind [layout_grind]

@[simp, grind =]
theorem Sim.OpOperandPtrPtr.setSim_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtrPtr)
    (value : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (set ctx ptr value ib valueIb).spec = ptr.spec.set ctx.spec value.spec := by
  rfl

buffed
def Sim.BlockOperandPtrPtr.setSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr)
    (value : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.write ctx.buf value.impl (by
    have : ctx.buf.mem.size < 2^63 := by grind
    have := Sim.BlockOperandPtrPtr.after_lt_ctx (ctx := ctx) ptr.spec (by grind)
    grind [layout_grind]),
   ptr.spec.set ctx.spec value.spec (by grind), by prove_setLinkSim ctx Buffed.BlockOperandPtrMPtr.write⟩

open Classical in
noncomputable def Sim.BlockOperandPtrPtr.set! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr)
    (value : Sim.OptionBlockOperandPtr) : Sim.IRContext OpInfo :=
  if h₁ : ptr.impl.toNat + Buffed.ptrSize.toNat ≤ ↑ctx.buf.size then
    if h₂ : Veir.Sim
    { buf := Buffed.BlockOperandPtrMPtr.write ctx.buf ptr.impl value.impl h₁,
      spec := ptr.spec.set! ctx.spec value.spec } then
    ⟨ptr.impl.write ctx.buf value.impl h₁, ptr.spec.set! ctx.spec value.spec, h₂⟩
    else
      default
  else
    default

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtrPtr.set_eq_set! (ctx : IRContext OpInfo) ptr value ib valueIb :
    set ctx ptr value ib valueIb = set! ctx ptr value := by
  simp [set_def, setSim, set!]
  split
  · grind
  · have : ctx.buf.mem.size < 2^63 := by grind
    have := Sim.BlockOperandPtrPtr.after_lt_ctx (ctx := ctx) ptr.spec (by grind)
    grind [layout_grind]

@[simp, grind =]
theorem Sim.BlockOperandPtrPtr.setSim_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr)
    (value : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (set ctx ptr value ib valueIb).spec = ptr.spec.set ctx.spec value.spec := by
  rfl

/-! ## Allocation of empty regions and operations.

Like `Sim.BlockPtr.allocEmpty`, these reserve buffer space (with preallocated arrays for the
operation) and allocate the corresponding pointer in the specification. -/

@[inline]
def Sim.RegionPtr.allocEmptyImpl (ctx₀ : Buffed.IRBufContext OpInfo) : Option (Buffed.IRBufContext OpInfo × Buffed.RegionMPtr) :=
  let size := Buffed.Region.size
  let ptr : Buffed.RegionMPtr := ctx₀.usize
  rlet halloc : ctx ← ctx₀.alloc size
  have hsize : ctx.size = ctx₀.size + size.toNat := ctx₀.alloc_size halloc
  let ctx := ptr.writeParent ctx .none (by prove_allocBounds ctx₀)
  let ctx := ptr.writeFirstBlock ctx .none (by prove_allocBounds ctx₀)
  let ctx := ptr.writeLastBlock ctx .none (by prove_allocBounds ctx₀)
  some (ctx, ptr)

def Sim.RegionPtr.allocEmptySpec (ctx : Veir.IRContext OpInfo) (addr : UInt64) : Option (Veir.IRContext OpInfo × Veir.RegionPtr) :=
  RegionPtr.allocEmptyAt ctx addr.toNat

/-- The address at the end of the buffer is free in the spec: a region there would have its
range escape the buffer, contradicting `in_bounds`. -/
theorem Sim.RegionPtr.slot_free (ctx : Sim.IRContext OpInfo) :
    ¬ (⟨ctx.buf.mem.size⟩ : Veir.RegionPtr).InBounds ctx.spec := by
  intro hin
  have := ctx.sim.in_bounds (.region ⟨ctx.buf.mem.size⟩) (by grind)
  simp only [TopLevelPtr.range, Veir.RegionPtr.range, Veir.RegionPtr.toFlat, IsIncludedIN] at this
  grind

set_option maxHeartbeats 4000000 in
/-- The `Sim` relation survives an empty-region allocation: given that `allocEmptyImpl`
produced `ctxBuf`/`ptrImpl` and the spec allocated the matching region at `ptrImpl.toNat`,
the resulting buffer and spec still simulate each other. Discharges the `admitted_sim` that
`Sim.RegionPtr.allocEmpty` previously used. -/
theorem Sim.RegionPtr.allocEmpty_sim (ctx : Sim.IRContext OpInfo)
    {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.RegionMPtr}
    (heq : Sim.RegionPtr.allocEmptyImpl ctx.buf = some (ctxBuf, ptrImpl))
    {ctxSpec : Veir.IRContext OpInfo} {ptrSpec : Veir.RegionPtr}
    (hspec : Veir.RegionPtr.allocEmptyAt ctx.spec ptrImpl.toNat = some (ctxSpec, ptrSpec)) :
    Veir.Sim (OpInfo := OpInfo) ⟨ctxBuf, ctxSpec⟩ := by
  -- Extract the impl shape: ctxBuf = 3 writes on the extended buffer, ptrImpl = old usize.
  simp only [Sim.RegionPtr.allocEmptyImpl] at heq
  split at heq
  · exact absurd heq (by simp)
  · rename_i buf halloc
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    -- Size bookkeeping: the buffer grows by exactly `Region.size = 24` bytes.
    have hu := ctx.buf.usize_toNat
    have hs := ctx.buf.size_def
    have hgrow := ctx.buf.alloc_size halloc
    have hfits := buf.mem.fits_in_memory
    have hsize : ctx.buf.mem.size < 2 ^ 63 := by
      simp only [Buffed.IRBufContext.size_def, Int64.maxNatValue] at *; omega
    -- Spec characterization: the new region is at the old buffer end, `Region.empty`.
    have hptr := Veir.RegionPtr.allocEmptyAt_ptr hspec
    have hlay := (Veir.RegionPtr.allocEmptyAt_preservesLayout hspec).preserves
    -- Uniform preservation: reads entirely below the old buffer end are unchanged.
    have hread : ∀ (a : UInt64), a.toNat + 8 ≤ ctx.buf.mem.size →
        (Buffed.RegionMPtr.writeLastBlock
          (Buffed.RegionMPtr.writeFirstBlock
            (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
            ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
          ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64! a
        = ctx.buf.mem.read64! a := by
      intro a ha
      -- Expose `buf.mem = ctx.buf.mem.extend 24`, then the three blits are disjoint from `[a, a+8)`.
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
          Buffed.RegionMPtr.writeParent]
        grind [IsDisjoint, IsIncluded]
      · exact absurd halloc (by simp)
    -- read32! preservation: same argument as `hread` but for 4-byte reads (`readOpType!`).
    have hread32 : ∀ (a : UInt64), a.toNat + 4 ≤ ctx.buf.mem.size →
        (Buffed.RegionMPtr.writeLastBlock
          (Buffed.RegionMPtr.writeFirstBlock
            (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
            ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
          ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read32! a
        = ctx.buf.mem.read32! a := by
      intro a ha
      simp only [Buffed.IRBufContext.alloc] at halloc
      split at halloc
      · simp only [Option.some.injEq] at halloc
        subst halloc
        simp only [Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
          Buffed.RegionMPtr.writeParent]
        grind [IsDisjoint, IsIncluded]
      · exact absurd halloc (by simp)
    -- The region writes only touch `mem`, never `attributes`.
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
    constructor
    · -- fieldsInBounds (spec only)
      exact Veir.RegionPtr.allocEmptyAt_fieldsInBounds hspec ctx.sim.fieldsInBounds
    · -- repr (spec only)
      have hrepr := ctx.sim.repr
      constructor
      · intro op hin
        grind
      · intro op hin
        grind
      · intro blk hin
        grind
      · intro blk hin
        grind
      · intro rg hin
        grind
    · -- in_bounds
      intro ptr hib
      simp only [Buffed.RegionMPtr.writeLastBlock_range, Buffed.RegionMPtr.writeFirstBlock_range,
        Buffed.RegionMPtr.writeParent_range] at hib ⊢
      -- Goal: IsIncludedIN (ptr.range ctxSpec) buf.mem.range, with buf = ctx.buf extended by 24.
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
        -- Operations are unaffected by a region insert; range preserved, buffer only grew.
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
        -- Either an old region (unchanged range) or the freshly allocated one at [size, size+24).
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
      -- Range of any top-level ptr is `buf`-independent, so the write-tower drops out.
      -- Old ptrs keep their ranges (LayoutPreserved) and sit in `[0, size)`; the new region
      -- sits at `[size, size+24)`, hence disjoint from every old range.
      have hrange : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
          p.range ctxSpec = p.range ctx.spec := by
        intro p hp
        cases p with
        | operation op => exact LayoutPreserved.same_operationPtr_range op (by simpa using hp) hlay |>.symm
        | block bl => exact LayoutPreserved.same_blockPtr_range bl (by simpa using hp) hlay |>.symm
        | region rg => rfl
      -- Every old range's upper bound is at most the old buffer size = the new region's lower.
      have hupper : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
          (p.range ctxSpec).upper ≤ ctx.buf.mem.size := by
        intro p hp
        have hin := ctx.sim.in_bounds p hp
        rw [hrange p hp]
        simp only [IsIncludedIN] at hin
        simp only [ExArray.range_lower, ExArray.range_upper] at hin
        omega
      -- Membership in the new context: an old top-level ptr, or the fresh region.
      have hmem : ∀ (p : TopLevelPtr), p.InBounds ctxSpec →
          p.InBounds ctx.spec ∨ p = .region ptrSpec := by
        intro p hp
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
      -- The fresh region's range is `[size, size+24)`.
      have hnewrange : ∀ (rg : Veir.RegionPtr), rg = ptrSpec →
          (rg.range).lower = (ctx.buf.mem.size : Int) ∧
          (rg.range).upper = (ctx.buf.mem.size : Int) + Buffed.Region.size.toNat := by
        intro rg hrg
        subst hrg
        simp only [RegionPtr.range, RegionPtr.toFlat, hptr]
        refine ⟨by grind, by grind⟩
      intro p1 p2 hib1 hib2 hne
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
    · -- encoding_op
      intro op opIb
      have holdib : op.InBounds ctx.spec := by
        have := (RegionPtr.allocEmptyAt_genericPtr_iff (.operation op) hspec).mp (by simpa using opIb)
        grind
      have henc := ctx.sim.encoding_op op holdib
      -- op.range ⊆ [0, mem.size): every op field read lands below the old buffer end.
      have hinb := ctx.sim.in_bounds (.operation op) (by simpa using holdib)
      simp only [TopLevelPtr.range, Veir.OperationPtr.range, IsIncludedIN, ExArray.range_upper] at hinb
      -- `op.toM` is `op.id` as a UInt64 (id below buffer size, no truncation).
      have hopM : op.toM.toNat = op.toFlat := by
        simp only [Veir.OperationPtr.toM]
        grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      -- Read bridges specialised to this op: any 8-/4-byte field within `op.range` is preserved.
      have hro8 : ∀ (off : Int64), 0 ≤ off.toInt →
          op.toFlat + off.toInt + 8 ≤ (op.toFlat + Buffed.Operation.range op ctx.spec).upper →
          (Buffed.RegionMPtr.writeLastBlock
            (Buffed.RegionMPtr.writeFirstBlock
              (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
              ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
            ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64!
            (op.toM + off)
          = ctx.buf.mem.read64! (op.toM + off) := by
        intro off hoff hoff2
        apply hread
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
      have hro4 : ∀ (off : Int64), 0 ≤ off.toInt →
          op.toFlat + off.toInt + 4 ≤ (op.toFlat + Buffed.Operation.range op ctx.spec).upper →
          (Buffed.RegionMPtr.writeLastBlock
            (Buffed.RegionMPtr.writeFirstBlock
              (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
              ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
            ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read32!
            (op.toM + off)
          = ctx.buf.mem.read32! (op.toM + off) := by
        intro off hoff hoff2
        apply hread32
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
      have hget : Veir.OperationPtr.get! op ctxSpec = Veir.OperationPtr.get! op ctx.spec := by grind
      constructor
      · -- MatchesBase
        constructor
        · have := henc.prev
          simp only [Buffed.OperationMPtr.readPrev!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.prev (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.next
          simp only [Buffed.OperationMPtr.readNext!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.next (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.parent
          simp only [Buffed.OperationMPtr.readParent!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.parent (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.opType
          simp only [Buffed.OperationMPtr.readOpType!] at this ⊢
          rw [hro4 Buffed.Operation.Offsets.opType (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.attrs
          simp only [Buffed.OperationMPtr.readAttrs!, hattr] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.attrs (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
      · -- MatchesBlockOperands
        constructor
        · have := henc.numBlockOperands
          simp only [Buffed.OperationMPtr.readNumBlockOperands!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.numBlockOperands (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · intro bo boIb heq
          have boIb' : bo.InBounds ctx.spec := by
            have := (RegionPtr.allocEmptyAt_genericPtr_iff (.blockOperand bo) hspec).mp (by simpa using boIb)
            grind
          have := henc.blockOperands bo boIb' heq
          -- `bo`'s flat address and stored value are unchanged by the region insert (layout preserved).
          have hboMeq : bo.toM ctxSpec = bo.toM ctx.spec := by
            simp only [Veir.BlockOperandPtr.toM, Veir.BlockOperandPtr.toFlat]
            grind [layout_grind]
          have hbogeteq : bo.get! ctxSpec = bo.get! ctx.spec := by grind
          -- Address bound for `bo`: `bo.toFlat + BlockOperand.after ≤ mem.size` (Sim helper).
          have haft := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) bo boIb'
          have hboM : (bo.toM ctx.spec).toNat = bo.toFlat ctx.spec := by
            simp only [Veir.BlockOperandPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.BlockOperandPtr.toFlat]
          have hbo : ∀ (off : Int64), 0 ≤ off.toInt →
              off.toInt + 8 ≤ Buffed.BlockOperand.Offsets.afterInt →
              (Buffed.RegionMPtr.writeLastBlock
                (Buffed.RegionMPtr.writeFirstBlock
                  (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                  ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64!
                ((bo.toM ctx.spec) + off)
              = ctx.buf.mem.read64! ((bo.toM ctx.spec) + off) := by
            intro off hoff hoff2
            apply hread
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              simp only [Buffed.IRBufContext.size_def] at haft <;> grind
          constructor
          · have := this.nextUse
            simp only [Buffed.BlockOperandMPtr.readNextUse!, hboMeq, hbogeteq] at this ⊢
            rw [hbo Buffed.BlockOperand.Offsets.nextUse (by decide) (by decide)]
            grind [layout_grind]
          · have := this.back
            simp only [Buffed.BlockOperandMPtr.readBack!, hboMeq, hbogeteq] at this ⊢
            rw [hbo Buffed.BlockOperand.Offsets.back (by decide) (by decide)]
            grind [layout_grind]
          · have := this.owner
            simp only [Buffed.BlockOperandMPtr.readOwner!, hboMeq, hbogeteq] at this ⊢
            rw [hbo Buffed.BlockOperand.Offsets.owner (by decide) (by decide)]
            grind [layout_grind]
          · have := this.value
            simp only [Buffed.BlockOperandMPtr.readValue!, hboMeq, hbogeteq] at this ⊢
            rw [hbo Buffed.BlockOperand.Offsets.value (by decide) (by decide)]
            grind [layout_grind]
      · -- MatchesRegions
        -- The regions offset reads numOperands/numBlockOperands/opType, all preserved by hro8/hro4,
        -- so the whole computed offset — and thus every Nth-region read — is unchanged.
        have hoff8n : Buffed.OperationMPtr.readNumOperands!
            (Buffed.RegionMPtr.writeLastBlock
              (Buffed.RegionMPtr.writeFirstBlock
                (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
              ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])) op.toM
            = Buffed.OperationMPtr.readNumOperands! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.readNumOperands!]
          rw [hro8 Buffed.Operation.Offsets.numOperands (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
        have hoff8b : Buffed.OperationMPtr.readNumBlockOperands!
            (Buffed.RegionMPtr.writeLastBlock
              (Buffed.RegionMPtr.writeFirstBlock
                (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
              ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])) op.toM
            = Buffed.OperationMPtr.readNumBlockOperands! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.readNumBlockOperands!]
          rw [hro8 Buffed.Operation.Offsets.numBlockOperands (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
        have hoff4t : Buffed.OperationMPtr.readOpType!
            (Buffed.RegionMPtr.writeLastBlock
              (Buffed.RegionMPtr.writeFirstBlock
                (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
              ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])) op.toM
            = Buffed.OperationMPtr.readOpType! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.readOpType!]
          rw [hro4 Buffed.Operation.Offsets.opType (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
        have hcro : Buffed.OperationMPtr.computeRegionsOffset!
            (Buffed.RegionMPtr.writeLastBlock
              (Buffed.RegionMPtr.writeFirstBlock
                (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
              ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])) op.toM
            = Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.computeRegionsOffset!,
            Buffed.OperationMPtr.computeBlockOperandsOffset!, Buffed.OperationMPtr.computeOperandsOffset!,
            hoff8n, hoff8b, hoff4t]
        constructor
        · have := henc.numRegions
          simp only [Buffed.OperationMPtr.readNumRegions!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.numRegions (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · intro idx idxIn
          have := henc.regions idx (by grind)
          have hgetreg : op.getRegion! ctxSpec idx = op.getRegion! ctx.spec idx := by grind
          -- The Nth-region read commutes: the offset is unchanged (hcro) and the read is below mem.size.
          have hnth : Buffed.OperationMPtr.readNthRegion!
              (Buffed.RegionMPtr.writeLastBlock
                (Buffed.RegionMPtr.writeFirstBlock
                  (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                  ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])) op.toM idx.toUInt64
              = Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx.toUInt64 := by
            simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!, hcro]
            have hii := ctx.sim.repr.operations_indices op holdib |>.capRegions
            have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op holdib
            apply hread
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              grind [layout_grind, OperationPtr.computeRegionsOffset!_ideal, UInt64.toNat_mul]
          rw [hnth, hgetreg]
          exact this
      · -- MatchesOperands
        constructor
        · have := henc.numOperands
          simp only [Buffed.OperationMPtr.readNumOperands!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.numOperands (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · intro oper operIb heq
          have operIb' : oper.InBounds ctx.spec := by
            have := (RegionPtr.allocEmptyAt_genericPtr_iff (.opOperand oper) hspec).mp (by simpa using operIb)
            grind
          have := henc.operands oper operIb' heq
          have hoMeq : oper.toM ctxSpec = oper.toM ctx.spec := by
            simp only [Veir.OpOperandPtr.toM, Veir.OpOperandPtr.toFlat]; grind [layout_grind]
          have hogeteq : oper.get! ctxSpec = oper.get! ctx.spec := by grind
          have haft := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper operIb'
          have hoM : (oper.toM ctx.spec).toNat = oper.toFlat ctx.spec := by
            simp only [Veir.OpOperandPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.OpOperandPtr.toFlat]
          have ho : ∀ (off : Int64), 0 ≤ off.toInt →
              off.toInt + 8 ≤ Buffed.OpOperand.Offsets.afterInt →
              (Buffed.RegionMPtr.writeLastBlock
                (Buffed.RegionMPtr.writeFirstBlock
                  (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                  ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64!
                ((oper.toM ctx.spec) + off)
              = ctx.buf.mem.read64! ((oper.toM ctx.spec) + off) := by
            intro off hoff hoff2
            apply hread
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              simp only [Buffed.IRBufContext.size_def] at haft <;> grind
          constructor
          · have := this.nextUse
            simp only [Buffed.OpOperandMPtr.readNextUse!, hoMeq, hogeteq] at this ⊢
            rw [ho Buffed.OpOperand.Offsets.nextUse (by decide) (by decide)]
            grind [layout_grind]
          · have := this.back
            simp only [Buffed.OpOperandMPtr.readBack!, hoMeq, hogeteq] at this ⊢
            rw [ho Buffed.OpOperand.Offsets.back (by decide) (by decide)]
            grind [layout_grind]
          · have := this.owner
            simp only [Buffed.OpOperandMPtr.readOwner!, hoMeq, hogeteq] at this ⊢
            rw [ho Buffed.OpOperand.Offsets.owner (by decide) (by decide)]
            grind [layout_grind]
          · have := this.value
            simp only [Buffed.OpOperandMPtr.readValue!, hoMeq, hogeteq] at this ⊢
            rw [ho Buffed.OpOperand.Offsets.value (by decide) (by decide)]
            grind [layout_grind]
      · -- MatchesResults
        constructor
        · have := henc.numResults
          simp only [Buffed.OperationMPtr.readNumResults!] at this ⊢
          rw [hro8 Buffed.Operation.Offsets.numResults (by decide) (by simp only [Buffed.Operation.range]; grind [layout_grind])]
          grind [layout_grind]
        · intro res resIb heq
          have resIb' : res.InBounds ctx.spec := by
            have := (RegionPtr.allocEmptyAt_genericPtr_iff (.opResult res) hspec).mp (by simpa using resIb)
            grind
          have := henc.results res resIb' heq
          have hrMeq : res.toM ctxSpec = res.toM ctx.spec := by
            simp only [Veir.OpResultPtr.toM, Veir.OpResultPtr.toFlat]; grind [layout_grind]
          have hrgeteq : res.get! ctxSpec = res.get! ctx.spec := by grind
          have haft := Sim.OpResultPtr.after_lt_ctx (ctx := ctx) res resIb'
          have hrM : (res.toM ctx.spec).toNat = res.toFlat ctx.spec := by
            simp only [Veir.OpResultPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.OpResultPtr.toFlat]
          have hr : ∀ (off : Int64), 0 ≤ off.toInt →
              off.toInt + 8 ≤ Buffed.OpResult.Offsets.afterInt →
              (Buffed.RegionMPtr.writeLastBlock
                (Buffed.RegionMPtr.writeFirstBlock
                  (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                  ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64!
                ((res.toM ctx.spec) + off)
              = ctx.buf.mem.read64! ((res.toM ctx.spec) + off) := by
            intro off hoff hoff2
            apply hread
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
          -- The type read sits at offset 0 (`res.toM` itself); need it as `res.toM + 0`.
          have hr0 : (Buffed.RegionMPtr.writeLastBlock
                (Buffed.RegionMPtr.writeFirstBlock
                  (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                  ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64!
                (res.toM ctx.spec)
              = ctx.buf.mem.read64! (res.toM ctx.spec) := by
            have := hr 0 (by decide) (by decide)
            simpa using this
          constructor
          · have := this.kind
            simp only [Buffed.OpResultMPtr.readKind!, hrMeq] at this ⊢
            rw [hr0]; exact this
          · have := this.typee
            simp only [Buffed.OpResultMPtr.readType!, hrMeq, hrgeteq, hattr] at this ⊢
            rw [hr Buffed.ValueImpl.Offsets.type (by decide) (by decide)]; exact this
          · have := this.firstUse
            simp only [Buffed.OpResultMPtr.readFirstUse!, hrMeq, hrgeteq] at this ⊢
            rw [hr Buffed.ValueImpl.Offsets.firstUse (by decide) (by decide)]
            grind [layout_grind]
          · have := this.index
            simp only [Buffed.OpResultMPtr.readIndex!, hrMeq, hrgeteq] at this ⊢
            rw [hr Buffed.OpResult.Offsets.index (by decide) (by decide)]
            grind [layout_grind]
          · have := this.owner
            simp only [Buffed.OpResultMPtr.readOwner!, hrMeq, hrgeteq] at this ⊢
            rw [hr Buffed.OpResult.Offsets.owner (by decide) (by decide)]
            grind [layout_grind]
    · -- encoding_block
      intro blk blkIb
      have holdib : blk.InBounds ctx.spec := by
        have := (RegionPtr.allocEmptyAt_genericPtr_iff (.block blk) hspec).mp (by simpa using blkIb)
        grind
      have henc := ctx.sim.encoding_block blk holdib
      have hblkgeteq : blk.get! ctxSpec = blk.get! ctx.spec := by grind
      have haft := Sim.BlockPtr.after_lt_ctx (ctx := ctx) blk holdib
      have hblkM : blk.toM.toNat = blk.toFlat := by
        simp only [Veir.BlockPtr.toM]
        grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.BlockPtr.toFlat]
      -- Read bridge for the block's own fields (all within `[blk.id, blk.id + Block.after)`).
      have hb : ∀ (off : Int64), 0 ≤ off.toInt →
          blk.toFlat + off.toInt + 8 ≤ blk.id + Buffed.Block.Offsets.afterInt blk ctx.spec →
          (Buffed.RegionMPtr.writeLastBlock
            (Buffed.RegionMPtr.writeFirstBlock
              (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
              ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
            ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64!
            (blk.toM + off)
          = ctx.buf.mem.read64! (blk.toM + off) := by
        intro off hoff hoff2
        apply hread
        rw [UInt64.uint64_add_int64_toNat_lt] <;>
          simp only [Buffed.IRBufContext.size_def] at haft <;>
          simp only [Veir.BlockPtr.toFlat] at * <;> grind
      constructor
      · -- MatchesBase
        constructor
        · have := henc.firstUse
          simp only [Buffed.BlockMPtr.readFirstUse!, hblkgeteq] at this ⊢
          rw [hb Buffed.Block.Offsets.firstUse (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.prev
          simp only [Buffed.BlockMPtr.readPrev!, hblkgeteq] at this ⊢
          rw [hb Buffed.Block.Offsets.prev (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.next
          simp only [Buffed.BlockMPtr.readNext!, hblkgeteq] at this ⊢
          rw [hb Buffed.Block.Offsets.next (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.parent
          simp only [Buffed.BlockMPtr.readParent!, hblkgeteq] at this ⊢
          rw [hb Buffed.Block.Offsets.parent (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.firstOp
          simp only [Buffed.BlockMPtr.readFirstOp!, hblkgeteq] at this ⊢
          rw [hb Buffed.Block.Offsets.firstOp (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
          grind [layout_grind]
        · have := henc.lastOp
          simp only [Buffed.BlockMPtr.readLastOp!, hblkgeteq] at this ⊢
          rw [hb Buffed.Block.Offsets.lastOp (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
          grind [layout_grind]
      · -- MatchesArguments
        constructor
        · have := henc.numArguments
          simp only [Buffed.BlockMPtr.readNumArguments!, hblkgeteq] at this ⊢
          rw [hb Buffed.Block.Offsets.numArguments (by decide) (by simp only [Veir.BlockPtr.toFlat]; grind [layout_grind])]
          grind [layout_grind]
        · intro arg argIn heq
          have argIb' : arg.InBounds ctx.spec := by
            have := (RegionPtr.allocEmptyAt_genericPtr_iff (.blockArgument arg) hspec).mp (by simpa using argIn)
            grind
          have := henc.arguments arg argIb' heq
          have hageteq : arg.get! ctxSpec = arg.get! ctx.spec := by grind
          have haaft := Sim.BlockArgumentPtr.after_lt_ctx (ctx := ctx) arg argIb'
          have haM : arg.toM.toNat = arg.toFlat := by
            simp only [Veir.BlockArgumentPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', Veir.BlockArgumentPtr.toFlat]
          have ha : ∀ (off : Int64), 0 ≤ off.toInt →
              off.toInt + 8 ≤ Buffed.BlockArgument.Offsets.afterInt →
              (Buffed.RegionMPtr.writeLastBlock
                (Buffed.RegionMPtr.writeFirstBlock
                  (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                  ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64!
                (arg.toM + off)
              = ctx.buf.mem.read64! (arg.toM + off) := by
            intro off hoff hoff2
            apply hread
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              simp only [Buffed.IRBufContext.size_def] at haaft <;> grind
          have ha0 : (Buffed.RegionMPtr.writeLastBlock
                (Buffed.RegionMPtr.writeFirstBlock
                  (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                  ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64!
                arg.toM
              = ctx.buf.mem.read64! arg.toM := by
            have := ha 0 (by decide) (by decide)
            simpa using this
          constructor
          · have := this.kind
            simp only [Buffed.BlockArgumentMPtr.readKind!] at this ⊢
            rw [ha0]; exact this
          · have := this.type
            simp only [Buffed.BlockArgumentMPtr.readType!, hageteq, hattr] at this ⊢
            rw [ha Buffed.ValueImpl.Offsets.type (by decide) (by decide)]; exact this
          · have := this.firstUse
            simp only [Buffed.BlockArgumentMPtr.readFirstUse!, hageteq] at this ⊢
            rw [ha Buffed.ValueImpl.Offsets.firstUse (by decide) (by decide)]
            grind [layout_grind]
          · have := this.index
            simp only [Buffed.BlockArgumentMPtr.readIndex!, hageteq] at this ⊢
            rw [ha Buffed.BlockArgument.Offsets.index (by decide) (by decide)]
            grind [layout_grind]
          · have := this.owner
            simp only [Buffed.BlockArgumentMPtr.readOwner!, hageteq] at this ⊢
            rw [ha Buffed.BlockArgument.Offsets.owner (by decide) (by decide)]
            grind [layout_grind]
    · -- encoding_region
      intro rg rgIb
      rcases (RegionPtr.allocEmptyAt_genericPtr_iff (.region rg) hspec).mp (by simpa using rgIb)
        with hold | hnew
      · -- Old region: reads unchanged (hread) and get! preserved by the insert.
        have holdib : rg.InBounds ctx.spec := by simpa using hold
        have hgetp : Veir.RegionPtr.get! rg ctxSpec = Veir.RegionPtr.get! rg ctx.spec := by grind
        have henc := ctx.sim.encoding_region rg holdib
        -- The region's three fields sit in `[rg.toFlat, rg.toFlat+24) ⊆ [0, ctx.buf.mem.size)`.
        have hinb := ctx.sim.in_bounds (.region rg) (by simpa using holdib)
        simp only [TopLevelPtr.range, Veir.RegionPtr.range, Veir.RegionPtr.toFlat,
          IsIncludedIN, ExArray.range_upper, Buffed.Region.range] at hinb
        -- `rg.toM` is `rg.id` as a UInt64 (id is below the buffer size, so no truncation).
        have hrgM : rg.toM.toNat = rg.id := by
          simp only [Veir.RegionPtr.toM, Veir.RegionPtr.toFlat]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
        -- The region's `after` offset is 24 bytes.
        have hafter : (Buffed.Region.Offsets.after.toInt : Int) = 24 := by decide
        -- Read preservation for all three region fields.
        have hrf : ∀ (off : Int64), 0 ≤ off.toInt → off.toInt + 8 ≤ 24 →
            (Buffed.RegionMPtr.writeLastBlock
              (Buffed.RegionMPtr.writeFirstBlock
                (Buffed.RegionMPtr.writeParent buf ctx.buf.usize Buffed.OperationOPtr.none (by grind))
                ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def]))
              ctx.buf.usize Buffed.BlockOPtr.none (by grind [Buffed.IRBufContext.size_def])).mem.read64!
              (rg.toM + off)
            = ctx.buf.mem.read64! (rg.toM + off) := by
          intro off hoff hoff2
          apply hread
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
        constructor
        · have := henc.firstBlock
          simp only [Buffed.RegionMPtr.readFirstBlock!, hgetp]
          rw [hrf Buffed.Region.Offsets.firstBlock (by decide) (by decide)] at *
          simpa [Buffed.RegionMPtr.readFirstBlock!] using this
        · have := henc.lastBlock
          simp only [Buffed.RegionMPtr.readLastBlock!, hgetp]
          rw [hrf Buffed.Region.Offsets.lastBlock (by decide) (by decide)] at *
          simpa [Buffed.RegionMPtr.readLastBlock!] using this
        · have := henc.parent
          simp only [Buffed.RegionMPtr.readParent!, hgetp]
          rw [hrf Buffed.Region.Offsets.parent (by decide) (by decide)] at *
          simpa [Buffed.RegionMPtr.readParent!] using this
      · -- New region = ptrSpec: reads at fresh address return the written `none`s.
        simp only [GenericPtr.region.injEq] at hnew
        subst hnew
        have hget : Veir.RegionPtr.get! rg ctxSpec = Region.empty := by grind
        have htoM : rg.toM = ctx.buf.usize := by
          simp only [hptr, RegionPtr.toM, RegionPtr.toFlat]; grind
        -- The three write offsets (firstBlock=0, lastBlock=8, parent=16) are pairwise disjoint,
        -- so each read lands on exactly the slot it wrote, returning `none`.
        -- The three write offsets: firstBlock=0, lastBlock=8, parent=16 (each 8 bytes wide).
        have husz : ctx.buf.usize.toNat < 2 ^ 63 := by grind
        have hmax : (Int64.maxValue.toInt : Int) = 2 ^ 63 - 1 := by decide
        have a0 : (ctx.buf.usize + Buffed.Region.Offsets.firstBlock).toNat = ctx.buf.usize.toNat := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
        have a8 : (ctx.buf.usize + Buffed.Region.Offsets.lastBlock).toNat = ctx.buf.usize.toNat + 8 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
        have a16 : (ctx.buf.usize + Buffed.Region.Offsets.parent).toNat = ctx.buf.usize.toNat + 16 := by
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
        constructor
        · -- firstBlock: read at usize+0 hits writeFirstBlock
          simp only [Sim.OptionBlockPtr.Sim, hget, Region.empty, Buffed.RegionMPtr.readFirstBlock!,
            Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
            Buffed.RegionMPtr.writeParent, htoM]
          rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
            ExArray.read64!_blit64_self]
          rfl
        · -- lastBlock: read at usize+8 hits writeLastBlock (passing writeFirstBlock at +0)
          simp only [Sim.OptionBlockPtr.Sim, hget, Region.empty, Buffed.RegionMPtr.readLastBlock!,
            Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
            Buffed.RegionMPtr.writeParent, htoM]
          rw [ExArray.read64!_blit64_self]
          rfl
        · -- parent: read at usize+16 hits writeParent (passing the two block writes)
          simp only [Sim.OptionOperationPtr.Sim, hget, Region.empty, Buffed.RegionMPtr.readParent!,
            Buffed.RegionMPtr.writeLastBlock, Buffed.RegionMPtr.writeFirstBlock,
            Buffed.RegionMPtr.writeParent, htoM]
          rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
            ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
            ExArray.read64!_blit64_self]
          rfl
    · -- attr_empty
      rw [hattr]
      exact ctx.sim.attr_empty

@[inline]
def Sim.RegionPtr.allocEmpty (ctx : Sim.IRContext OpInfo) : Option (Sim.RegionPtr × Sim.IRContext OpInfo) :=
  match himpl : allocEmptyImpl ctx.buf with
  | none => none
  | some (ctxBuf, ptrImpl) =>
    let specRes := (Veir.RegionPtr.allocEmptyAt ctx.spec ptrImpl.toNat).specGet!
    have hspec : Veir.RegionPtr.allocEmptyAt ctx.spec ptrImpl.toNat = some specRes := by
      have hptr : ptrImpl = ctx.buf.usize := by
        simp only [allocEmptyImpl] at himpl
        split at himpl <;> grind
      have hfree := Sim.RegionPtr.slot_free ctx
      simp only [Veir.RegionPtr.inBounds_def] at hfree
      have husz := ctx.buf.usize_toNat
      have hs := ctx.buf.size_def
      have hsome := Veir.RegionPtr.allocEmptyAt_isSome_of_not_mem
        (ctx := ctx.spec) (addr := ptrImpl.toNat) (by grind)
      simp only [specRes, Option.specGet!]
      exact (Option.some_get! _ hsome).symm
    some ⟨⟨ptrImpl, specRes.2⟩, ⟨ctxBuf, specRes.1, allocEmpty_sim ctx himpl hspec⟩⟩

/-- Strengthening of `allocEmpty_spec`: the spec-level region is allocated exactly at the
address of the returned impl pointer. -/
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
    -- The remaining goal is `allocEmptyAt … = some (specGet!.fst, specGet!.snd)`, i.e. `= some specGet!`.
    have hptr : ptrImpl = ctx.buf.usize := by
      simp only [allocEmptyImpl] at himpl
      split at himpl <;> grind
    have hfree := Sim.RegionPtr.slot_free ctx
    simp only [Veir.RegionPtr.inBounds_def] at hfree
    have husz := ctx.buf.usize_toNat
    have hs := ctx.buf.size_def
    have hsome := Veir.RegionPtr.allocEmptyAt_isSome_of_not_mem
      (ctx := ctx.spec) (addr := ptrImpl.toNat) (by grind)
    simp only [Option.specGet!]
    rw [← Option.some_get! _ hsome]
    simp

@[grind! .]
theorem Sim.RegionPtr.allocEmpty_spec {ctx : Sim.IRContext OpInfo} :
    allocEmpty ctx = some ⟨ptr, ctx'⟩ →
    ∃ addr, Veir.RegionPtr.allocEmptyAt ctx.spec addr = some ⟨ctx'.spec, ptr.spec⟩:=
  fun h => ⟨ptr.impl.toNat, Sim.RegionPtr.allocEmpty_spec' h⟩

set_option maxHeartbeats 10000000 in
@[inline]
def Sim.OperationPtr.allocEmptyImpl (ctx₀ : Buffed.IRBufContext OpInfo)
    (numResults numOperands numBlockOperands numRegions propSize : UInt64)
    (opType : UInt32)
    (hr : numResults.toNat ≤ Buffed.countCard) (ho : numOperands.toNat ≤ Buffed.countCard)
    (hbo : numBlockOperands.toNat ≤ Buffed.countCard) (hreg : numRegions.toNat ≤ Buffed.countCard)
    (hp : propSize.toNat ≤ Buffed.countCard) :
    Option (Buffed.IRBufContext OpInfo × Buffed.OperationMPtr) :=
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

/-- The operation pointer produced by `allocEmptyImpl` lies at or past the end of the buffer:
its address is the old buffer size plus the back-allocated results prefix. -/
theorem Sim.OperationPtr.allocEmptyImpl_ptr_ge {ctx₀ : Buffed.IRBufContext OpInfo}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64}
    {hr ho hbo hreg hp hc} {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize hc
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl)) :
    ctx₀.mem.size ≤ ptrImpl.toNat := by
  simp only [allocEmptyImpl] at h
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

/-- Closed form of the operation pointer returned by `allocEmptyImpl`: the old buffer size
plus the back-allocated results array. -/
theorem Sim.OperationPtr.allocEmptyImpl_ptr_toNat {ctx₀ : Buffed.IRBufContext OpInfo}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl)) :
    ptrImpl.toNat = ctx₀.mem.size + Buffed.OpResult.size.toNat * numResults.toNat := by
  simp only [allocEmptyImpl] at h
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

/-- `allocEmptyImpl` only touches `mem`; the attribute table is unchanged. -/
theorem Sim.OperationPtr.allocEmptyImpl_attributes {ctx₀ : Buffed.IRBufContext OpInfo}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl)) :
    ctxBuf.attributes = ctx₀.attributes := by
  simp only [allocEmptyImpl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i buf halloc
    obtain ⟨rfl, rfl⟩ := Option.some.injEq _ _ ▸ h
    simp only [Buffed.IRBufContext.alloc] at halloc
    split at halloc
    · obtain rfl := Option.some.injEq _ _ ▸ halloc
      rfl
    · exact absurd halloc (by simp)

/-- `allocEmptyImpl` grows the buffer by exactly the computed operation size. -/
theorem Sim.OperationPtr.allocEmptyImpl_size {ctx₀ : Buffed.IRBufContext OpInfo}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl)) :
    ctxBuf.mem.size = ctx₀.mem.size +
      (Buffed.OperationMPtr.computeOperationSize numResults numOperands numBlockOperands
        numRegions propSize).toNat := by
  simp only [allocEmptyImpl] at h
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

/-- 64-bit reads that lie entirely inside the old buffer are unchanged by `allocEmptyImpl`:
the fresh operation is written past the old buffer end. -/
theorem Sim.OperationPtr.allocEmptyImpl_read64_old {ctx₀ : Buffed.IRBufContext OpInfo}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl))
    (n : UInt64) (hn : n.toNat + 8 ≤ ctx₀.mem.size) :
    ctxBuf.mem.read64! n = ctx₀.mem.read64! n := by
  have hptr := Sim.OperationPtr.allocEmptyImpl_ptr_ge h
  have hptn := Sim.OperationPtr.allocEmptyImpl_ptr_toNat h
  have hu := ctx₀.usize_toNat
  have hfits := ctx₀.mem.fits_in_memory
  have hsz := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions propSize hr ho hbo hreg hp
  have hnr := UInt64.toNat_lt numResults
  simp only [allocEmptyImpl] at h
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
      -- The written header fields all lie within 64 bytes past the fresh operation pointer.
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

/-- 32-bit variant of `allocEmptyImpl_read64_old`. -/
theorem Sim.OperationPtr.allocEmptyImpl_read32_old {ctx₀ : Buffed.IRBufContext OpInfo}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
      hr ho hbo hreg hp = some (ctxBuf, ptrImpl))
    (n : UInt64) (hn : n.toNat + 4 ≤ ctx₀.mem.size) :
    ctxBuf.mem.read32! n = ctx₀.mem.read32! n := by
  have hptr := Sim.OperationPtr.allocEmptyImpl_ptr_ge h
  have hptn := Sim.OperationPtr.allocEmptyImpl_ptr_toNat h
  have hu := ctx₀.usize_toNat
  have hfits := ctx₀.mem.fits_in_memory
  have hsz := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions propSize hr ho hbo hreg hp
  have hnr := UInt64.toNat_lt numResults
  simp only [allocEmptyImpl] at h
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
      -- The written header fields all lie within 64 bytes past the fresh operation pointer.
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

/-- The header fields of the freshly allocated operation read back as written: the counts are
the requested capacities, the links are `none`, the opType is the encoded opcode, and the
`attrs` slot is still zero-initialized (pointing at the canonical empty dictionary). -/
theorem Sim.OperationPtr.allocEmptyImpl_new_op_reads {ctx₀ : Buffed.IRBufContext OpInfo}
    {numResults numOperands numBlockOperands numRegions propSize : UInt64} {opType : UInt32}
    {hr ho hbo hreg hp} {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.OperationMPtr}
    (h : allocEmptyImpl ctx₀ numResults numOperands numBlockOperands numRegions propSize opType
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
  have hptr := Sim.OperationPtr.allocEmptyImpl_ptr_ge h
  have hptn := Sim.OperationPtr.allocEmptyImpl_ptr_toNat h
  have hu := ctx₀.usize_toNat
  have hfits := ctx₀.mem.fits_in_memory
  have hsz := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions propSize hr ho hbo hreg hp
  have hnr := UInt64.toNat_lt numResults
  simp only [allocEmptyImpl] at h
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
      -- The written header fields all lie within 64 bytes past the fresh operation pointer.
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

def Sim.OperationPtr.allocEmptySpec (ctx : Veir.IRContext OpInfo) (addr : Nat) (opType : OpInfo)
    (properties : HasOpInfo.propertiesOf opType) (capResults capBlockOperands capRegions capOperands : Nat)
    : Option (Veir.IRContext OpInfo × Veir.OperationPtr) :=
  OperationPtr.allocEmptyAt ctx opType properties capResults capBlockOperands capRegions capOperands addr

/-- `allocEmptyAt` preserves `FieldsInBounds`: existing objects keep their fields (whose
`InBounds` facts transfer since allocation only grows the `InBounds` sets), and the fresh
operation is empty, so its clauses are vacuous or trivial. -/
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

/-- Existing operations keep their byte range across `allocEmptyAt` (their capacities are
unchanged). -/
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

/-- Any address at or beyond the end of the buffer is free in the spec: an operation there
would have its range escape the buffer, contradicting `in_bounds`. -/
theorem Sim.OperationPtr.slot_free (ctx : Sim.IRContext OpInfo) {a : Nat} (ha : ctx.buf.mem.size ≤ a) :
    ¬ (⟨a⟩ : Veir.OperationPtr).InBounds ctx.spec := by
  intro hin
  have hlt := Sim.OperationPtr.after_lt_ctx (ctx := ctx) ⟨a⟩ hin
  -- `afterInt` is the (positive) tail of the operation past its pointer.
  have : (0 : Int) < Buffed.Operation.Offsets.afterInt (⟨a⟩ : Veir.OperationPtr) ctx.spec := by
    simp only [Buffed.Operation.Offsets.afterInt, Buffed.Operation.Offsets.regionsInt,
      Buffed.Operation.Offsets.blockOperandsInt, Buffed.Operation.Offsets.operandsInt]
    grind
  grind

set_option maxHeartbeats 1000000000 in
/-- Freshly allocating an empty operation — buffer side (`allocEmptyImpl`) and spec side
(`allocEmptyAt`, at the same address) — preserves the simulation invariant. -/
theorem Sim.OperationPtr.allocEmpty_sim {ctx : Sim.IRContext OpInfo} {opType : OpInfo}
    {props : HasOpInfo.propertiesOf opType}
    {numResults numOperands numBlockOperands numRegions : UInt64}
    {h₁ : numResults.toNat ≤ countCard} {h₂ : numOperands.toNat ≤ countCard}
    {h₃ : numBlockOperands.toNat ≤ countCard} {h₄ : numRegions.toNat ≤ countCard}
    {hp : (Buffed.Operation.propertySize opType).toNat ≤ countCard}
    {ctxBuf : Buffed.IRBufContext OpInfo} {ptrImpl : Buffed.OperationMPtr}
    {ctxSpec : Veir.IRContext OpInfo} {ptrSpec : Veir.OperationPtr}
    (heqImpl : allocEmptyImpl ctx.buf numResults numOperands numBlockOperands numRegions
      (Buffed.Operation.propertySize opType) (SerializableOpInfo.encode opType)
      h₁ h₂ h₃ h₄ hp = some (ctxBuf, ptrImpl))
    (heqSpec : Veir.OperationPtr.allocEmptyAt ctx.spec opType props numResults.toNat
      numBlockOperands.toNat numRegions.toNat numOperands.toNat ptrImpl.toNat
      = some (ctxSpec, ptrSpec)) :
    Veir.Sim (OpInfo := OpInfo) ⟨ctxBuf, ctxSpec⟩ := by
  have hattrs := Sim.OperationPtr.allocEmptyImpl_attributes heqImpl
  have hsize := Sim.OperationPtr.allocEmptyImpl_size heqImpl
  have hge := Sim.OperationPtr.allocEmptyImpl_ptr_ge heqImpl
  have hptn := Sim.OperationPtr.allocEmptyImpl_ptr_toNat heqImpl
  have hro64 := Sim.OperationPtr.allocEmptyImpl_read64_old heqImpl
  have hro32 := Sim.OperationPtr.allocEmptyImpl_read32_old heqImpl
  obtain ⟨hRnr, hRno, hRnb, hRnrg, hRprev, hRnext, hRpar, hRty, hRattrs⟩ :=
    Sim.OperationPtr.allocEmptyImpl_new_op_reads heqImpl
  have hnew : ptrSpec = ⟨ptrImpl.toNat⟩ := Veir.OperationPtr.allocEmptyAt_ptr_eq heqSpec
  subst hnew
  have hnewIb : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).InBounds ctxSpec :=
    Veir.OperationPtr.allocEmptyAt_new_inBounds heqSpec
  -- The freshly allocated operation reads back as `Operation.empty` with the requested capacities.
  have hget : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec = Veir.Operation.empty opType props
      numResults.toNat numBlockOperands.toNat numRegions.toNat numOperands.toNat := by
    simpa using Veir.OperationPtr.get!_OperationPtr_allocEmptyAt
      (operation := (⟨ptrImpl.toNat⟩ : Veir.OperationPtr)) heqSpec
  have hgetTy : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).getOpType! ctxSpec = opType := by
    simpa using Veir.OperationPtr.getOpType!_OperationPtr_allocEmptyAt
      (operation := (⟨ptrImpl.toNat⟩ : Veir.OperationPtr)) heqSpec
  -- `Operation.empty` is not reducible, so spell the capacities out for `grind`.
  have hcapR : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capResults = numResults.toNat := by
    rw [hget]; rfl
  have hcapO : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capOperands = numOperands.toNat := by
    rw [hget]; rfl
  have hcapB : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capBlockOperands
      = numBlockOperands.toNat := by rw [hget]; rfl
  have hcapRg : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capRegions
      = numRegions.toNat := by rw [hget]; rfl
  -- Allocating a fresh operation leaves every pre-existing object's layout untouched, which
  -- transports `toFlat`/`toM` (hence every read address) from `ctx.spec` to `ctxSpec`.
  have hlp : ctx.spec.LayoutPreserved ctxSpec := by
    have hni := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
    constructor
    · intro op hib
      have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by grind
      constructor <;>
        grind [Veir.OperationPtr.get!_OperationPtr_allocEmptyAt,
          Veir.OperationPtr.getOpType!_OperationPtr_allocEmptyAt]
    · intro blk hib
      grind [Veir.BlockPtr.LayoutPreserved, Veir.BlockPtr.get!_OperationPtr_allocEmptyAt]
  have hfits := ctxBuf.mem.fits_in_memory
  have hfits₀ := ctx.buf.mem.fits_in_memory
  have hszdec := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions (Buffed.Operation.propertySize opType) h₁ h₂ h₃ h₄ hp
  -- omega/cutsat choke on `UInt64.toNat 32`; state every size as a `Nat` literal.
  simp only [show Buffed.OpResult.size.toNat = 40 from rfl,
    show Buffed.ptrSize.toNat = 8 from rfl,
    show Buffed.Operation.sizeBase.toNat = 72 from rfl,
    Int64.maxNatValue] at hszdec hsize hptn hfits hfits₀
  have hfib' := IRContext.fieldsInBounds_OperationPtr_allocEmptyAt heqSpec ctx.sim.fieldsInBounds
  have hrepr' := IRContext.isRepr_OperationPtr_allocEmptyAt heqSpec ctx.sim.repr
    (by simp only [Int64.maxNatValue]; omega) h₁ h₂ h₃ h₄
  constructor
  · exact hfib'
  · exact hrepr'
  · -- `in_bounds`
    intro ptr ib
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
      clear hro64 hro32 hRnr hRno hRnb hRnrg hRprev hRnext hRpar hRty hRattrs
      simp only [TopLevelPtr.range, Veir.OperationPtr.range_ideal hrepr' hnewIb,
        Veir.OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def,
        Veir.OperationPtr.toFlat, IsIncludedIN, ExArray.range_def]
      grind
  · -- `disjoint_allocs`
    clear hro64 hro32 hRnr hRno hRnb hRnrg hRprev hRnext hRpar hRty hRattrs
    have hrgOld : ∀ (q : TopLevelPtr), q.InBounds ctx.spec → q.range ctxSpec = q.range ctx.spec := by
      intro q hq
      have hni := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
      cases q with
      | operation op =>
        have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by grind
        simpa [TopLevelPtr.range] using Veir.OperationPtr.range_OperationPtr_allocEmptyAt heqSpec hne
      | block bl =>
        simpa [TopLevelPtr.range] using
          Veir.BlockPtr.range_OperationPtr_allocEmptyAt (bl := bl) heqSpec
      | region rg => rfl
    -- Every old allocation lives strictly below the old buffer end; the new one starts at or
    -- above it (`hge`/`hptn`), so the two are disjoint.
    have hnewRange : ∀ (q : TopLevelPtr), q.InBounds ctx.spec →
        IsDisjointI (q.range ctxSpec)
          ((TopLevelPtr.operation (⟨ptrImpl.toNat⟩ : Veir.OperationPtr)).range ctxSpec) := by
      intro q hq
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
    rcases (Veir.OperationPtr.allocEmptyAt_operationPtr_iff op heqSpec).mp ib with hold | rfl
    · -- existing operation: every read lies inside the old buffer, and the spec is unchanged
      have hni := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
      have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by grind
      have hafter := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op hold
      have hrepop : op.IsRepr := ctx.sim.repr.operations op hold
      have hindices := ctx.sim.repr.operations_indices op hold
      have hin := ctx.sim.in_bounds (.operation op) (by grind)
      have hfibOld := ctx.sim.fieldsInBounds
      have this := ctx.sim.encoding_op op hold
      constructor
      · constructor
        · have := this.prev
          grind [layout_grind, Buffed.OperationMPtr.readPrev!]
        · have := this.next
          grind [layout_grind, Buffed.OperationMPtr.readNext!]
        · have := this.parent
          grind [layout_grind, Buffed.OperationMPtr.readParent!]
        · have := this.opType
          grind [layout_grind, Buffed.OperationMPtr.readOpType!]
        · have := this.attrs
          grind [layout_grind, Buffed.OperationMPtr.readAttrs!]
      · constructor
        · have := this.numBlockOperands
          grind [layout_grind, Buffed.OperationMPtr.readNumBlockOperands!]
        · intro bo boIb heq
          have hrange := @BlockOperandPtr.range_included_op_range
          have := this.blockOperands bo (by grind [Veir.BlockOperandPtr.inBounds_def]) heq
          constructor
          · have := this.nextUse
            grind [layout_grind, Buffed.BlockOperandMPtr.readNextUse!]
          · have := this.back
            grind [layout_grind, Buffed.BlockOperandMPtr.readBack!]
          · have := this.owner
            grind [layout_grind, Buffed.BlockOperandMPtr.readOwner!]
          · have := this.value
            grind [layout_grind, Buffed.BlockOperandMPtr.readValue!]
      · constructor
        · have := this.numRegions
          grind [layout_grind, Buffed.OperationMPtr.readNumRegions!]
        · intro idx idxIn
          have hcap := hindices.capRegions
          have hsizeLt : ctx.buf.mem.size < Int64.maxValue.toInt := by
            grind [ctx.buf.mem.fits_in_memory]
          have hidxOld : idx < op.getNumRegions! ctx.spec := by
            grind [Veir.OperationPtr.getNumRegions!_OperationPtr_allocEmptyAt]
          have hreg := this.regions idx hidxOld
          -- The offset of the region table is itself computed from buffer reads, all of which sit
          -- below the old buffer end, so it is unchanged by the extension.
          have hoff : Buffed.OperationMPtr.computeRegionsOffset! ctxBuf op.toM
              = Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
            simp only [Buffed.OperationMPtr.computeRegionsOffset!,
              Buffed.OperationMPtr.computeBlockOperandsOffset!,
              Buffed.OperationMPtr.computeOperandsOffset!]
            grind (splits := 20) [Buffed.OperationMPtr.readOpType!,
              Buffed.OperationMPtr.readNumOperands!, Buffed.OperationMPtr.readNumBlockOperands!,
              layout_grind]
          have hnth : Buffed.OperationMPtr.readNthRegion! ctxBuf op.toM (UInt64.ofNat idx)
              = Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM (UInt64.ofNat idx) := by
            simp only [Buffed.OperationMPtr.readNthRegion!,
              Buffed.OperationMPtr.computeRegionOffset!, hoff]
            exact hro64 _ (by grind [layout_grind])
          grind [layout_grind, Nat.toUInt64_eq]
      · constructor
        · have := this.numOperands
          grind [layout_grind, Buffed.OperationMPtr.readNumOperands!]
        · intro oper operIb heq
          have hrange := @OpOperandPtr.range_included_op_range
          have := this.operands oper (by grind [Veir.OpOperandPtr.inBounds_def]) heq
          constructor
          · have := this.nextUse
            grind [layout_grind, Buffed.OpOperandMPtr.readNextUse!]
          · have := this.back
            grind [layout_grind, Buffed.OpOperandMPtr.readBack!]
          · have := this.owner
            grind [layout_grind, Buffed.OpOperandMPtr.readOwner!]
          · have := this.value
            grind [layout_grind, Buffed.OpOperandMPtr.readValue!]
      · constructor
        · have := this.numResults
          grind [layout_grind, Buffed.OperationMPtr.readNumResults!]
        · intro res resIb heq
          have hrange := @OpResultPtr.range_included_op_range
          have := this.results res (by grind [Veir.OpResultPtr.inBounds_def]) heq
          constructor
          · have := this.kind
            grind [layout_grind, Buffed.OpResultMPtr.readKind!]
          · have := this.typee
            grind [layout_grind, Buffed.OpResultMPtr.readType!]
          · have := this.firstUse
            grind [layout_grind, Buffed.OpResultMPtr.readFirstUse!]
          · have := this.index
            grind [layout_grind, Buffed.OpResultMPtr.readIndex!]
          · have := this.owner
            grind [layout_grind, Buffed.OpResultMPtr.readOwner!]
    · -- the freshly allocated operation: every field reads back what `allocEmptyImpl` wrote
      have hnewToM : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).toM = ptrImpl := by
        simp [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
      clear hro64 hro32
      constructor
      · constructor
        · grind [Buffed.OperationMPtr.readPrev!, Sim.OptionOperationPtr.Sim, Veir.Operation.empty,
            Veir.OperationPtr.toO]
        · grind [Buffed.OperationMPtr.readNext!, Sim.OptionOperationPtr.Sim, Veir.Operation.empty,
            Veir.OperationPtr.toO]
        · grind [Buffed.OperationMPtr.readParent!, Sim.OptionBlockPtr.Sim, Veir.Operation.empty,
            Veir.BlockPtr.toO]
        · grind [SerializableOpInfo.decode_encode]
        · -- `attrs`: the zero-initialized index denotes the canonical empty dictionary
          have hae := ctx.sim.attr_empty
          rw [hnewToM, hRattrs, hattrs, hget]
          simpa [Veir.Operation.empty] using hae
      · constructor
        · grind
        · intro bo boIb heq
          exact absurd boIb (Veir.BlockOperandPtr.allocEmptyAt_no_operands heqSpec heq)
      · constructor
        · grind
        · intro idx idxIn
          grind
      · constructor
        · grind
        · intro oper operIb heq
          exact absurd operIb (Veir.OpOperandPtr.allocEmptyAt_no_operands heqSpec heq)
      · constructor
        · grind
        · intro res resIb heq
          exact absurd resIb (Veir.OpResultPtr.allocEmptyAt_no_results heqSpec heq)
  · -- `encoding_block`
    intro blk blkIb
    have hold : blk.InBounds ctx.spec := by
      have := (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff (.block blk) heqSpec).mp (by grind)
      grind
    have hafter := Sim.BlockPtr.after_lt_ctx (ctx := ctx) blk hold
    have hrepbl : blk.IsRepr := ctx.sim.repr.blocks blk hold
    have hindices := ctx.sim.repr.blocks_indices blk hold
    have hin := ctx.sim.in_bounds (.block blk) (by grind)
    have this := ctx.sim.encoding_block blk hold
    constructor
    · constructor
      · have := this.firstUse
        grind [layout_grind, Buffed.BlockMPtr.readFirstUse!]
      · have := this.prev
        grind [layout_grind, Buffed.BlockMPtr.readPrev!]
      · have := this.next
        grind [layout_grind, Buffed.BlockMPtr.readNext!]
      · have := this.parent
        grind [layout_grind, Buffed.BlockMPtr.readParent!]
      · have := this.firstOp
        grind [layout_grind, Buffed.BlockMPtr.readFirstOp!]
      · have := this.lastOp
        grind [layout_grind, Buffed.BlockMPtr.readLastOp!]
    · constructor
      · have := this.numArguments
        grind [layout_grind, Buffed.BlockMPtr.readNumArguments!]
      · intro arg argIn heq
        have hrange := @BlockArgumentPtr.range_included_block_range
        have := this.arguments arg (by grind [Veir.BlockArgumentPtr.inBounds_def]) heq
        constructor
        · have := this.kind
          grind [layout_grind, Buffed.BlockArgumentMPtr.readKind!]
        · have := this.type
          grind [layout_grind, Buffed.BlockArgumentMPtr.readType!]
        · have := this.firstUse
          grind [layout_grind, Buffed.BlockArgumentMPtr.readFirstUse!]
        · have := this.index
          grind [layout_grind, Buffed.BlockArgumentMPtr.readIndex!]
        · have := this.owner
          grind [layout_grind, Buffed.BlockArgumentMPtr.readOwner!]
  · -- `encoding_region`
    intro rg rgIb
    have hold : rg.InBounds ctx.spec := by
      have := (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff (.region rg) heqSpec).mp (by grind)
      grind
    have hin := ctx.sim.in_bounds (.region rg) (by grind)
    have this := ctx.sim.encoding_region rg hold
    constructor
    · have := this.firstBlock
      grind [layout_grind, Buffed.RegionMPtr.readFirstBlock!]
    · have := this.lastBlock
      grind [layout_grind, Buffed.RegionMPtr.readLastBlock!]
    · have := this.parent
      grind [layout_grind, Buffed.RegionMPtr.readParent!]
  · -- `attr_empty`
    rw [hattrs]
    exact ctx.sim.attr_empty

@[inline]
def Sim.OperationPtr.allocEmpty (ctx : Sim.IRContext OpInfo) (opType : OpInfo)
    (properties : HasOpInfo.propertiesOf opType)
    (numResults numOperands numBlockOperands numRegions : UInt64)
    (h₁ : numResults.toNat ≤ countCard) (h₂ : numOperands.toNat ≤ countCard)
    (h₃ : numBlockOperands.toNat ≤ countCard) (h₄ : numRegions.toNat ≤ countCard) :
    Option (Sim.OperationPtr × Sim.IRContext OpInfo) :=
  match heqImpl : allocEmptyImpl ctx.buf numResults numOperands numBlockOperands numRegions
        (Buffed.Operation.propertySize opType) (SerializableOpInfo.encode opType)
        h₁ h₂ h₃ h₄ (Nat.le_of_lt (Operation.propertySize_lt opType)) with
    | none => none
    | some (ctxBuf, ptrImpl) =>
      -- The spec-side allocation succeeds: the new pointer lies at/past the old buffer end,
      -- so its address is free in the spec.
      have hsome : (allocEmptySpec ctx.spec ptrImpl.toNat opType properties
          numResults.toNat numBlockOperands.toNat numRegions.toNat numOperands.toNat).isSome := by
        have hge := Sim.OperationPtr.allocEmptyImpl_ptr_ge heqImpl
        have hfree := Sim.OperationPtr.slot_free ctx hge
        simp only [Veir.OperationPtr.inBounds_def] at hfree
        exact Veir.OperationPtr.allocEmptyAt_isSome_of_not_mem hfree
      match heqSpec : (allocEmptySpec ctx.spec ptrImpl.toNat opType properties
          numResults.toNat numBlockOperands.toNat numRegions.toNat numOperands.toNat).specGet! with
      | (ctxSpec, ptrSpec) =>
        some ⟨⟨ptrImpl, ptrSpec⟩, ⟨ctxBuf, ctxSpec, by
          refine Sim.OperationPtr.allocEmpty_sim (props := properties) (ptrSpec := ptrSpec)
            heqImpl ?_
          -- `allocEmptySpec` is a definitional wrapper around `allocEmptyAt`; `hsome` turns the
          -- `specGet!` equation back into the `= some _` equation the lemma wants.
          show allocEmptySpec ctx.spec ptrImpl.toNat opType properties numResults.toNat
            numBlockOperands.toNat numRegions.toNat numOperands.toNat = some (ctxSpec, ptrSpec)
          grind [Option.specGet!]⟩⟩

/-- Strengthening of `allocEmpty_spec`: the spec-level operation is allocated exactly at the
address of the returned impl pointer. -/
theorem Sim.OperationPtr.allocEmpty_spec' {ctx : Sim.IRContext OpInfo} :
    allocEmpty ctx opType props c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some ⟨ptr, ctx'⟩ →
    Veir.OperationPtr.allocEmptyAt ctx.spec opType props c₁.toNat c₃.toNat c₄.toNat c₂.toNat ptr.impl.toNat = some ⟨ctx'.spec, ptr.spec⟩ := by
  unfold Sim.OperationPtr.allocEmpty allocEmptySpec
  split
  · intro h; exact absurd h (by simp)
  · rename_i ptrImpl heqImpl
    intro h
    -- `ptrImpl` lies at/past the buffer end, so the spec slot is free.
    have hge := Sim.OperationPtr.allocEmptyImpl_ptr_ge heqImpl
    have hfree := Sim.OperationPtr.slot_free ctx hge
    simp only [Veir.OperationPtr.inBounds_def] at hfree
    have hsome := Veir.OperationPtr.allocEmptyAt_isSome_of_not_mem
      (opType := opType) (properties := props) (capResults := c₁.toNat)
      (capBlockOperands := c₃.toNat) (capRegions := c₄.toNat) (capOperands := c₂.toNat) hfree
    simp_all only [Option.some.injEq, Prod.mk.injEq]
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    simp only [Option.specGet!]
    grind

@[grind! .]
theorem Sim.OperationPtr.allocEmpty_spec {ctx : Sim.IRContext OpInfo} :
    allocEmpty ctx opType props c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some ⟨ptr, ctx'⟩ →
    ∃ addr, Veir.OperationPtr.allocEmptyAt ctx.spec opType props c₁.toNat c₃.toNat c₄.toNat c₂.toNat addr = some ⟨ctx'.spec, ptr.spec⟩:=
  fun h => ⟨ptr.impl.toNat, Sim.OperationPtr.allocEmpty_spec' h⟩

-- theorem Veir.Sim.BlockPtr.getParent_impl2 {OpInfo : Type} [inst : HasOpInfo OpInfo] (ctx : Sim.IRContext OpInfo)
--   (ptr : Sim.BlockPtr) (ib : ptr.InBounds ctx) :
--   (Sim.BlockPtr.getParentSim ctx ptr ib).impl = Sim.BlockPtr.getParentImpl ctx.buf ctx.spec ⋯ ptr.impl ptr.spec ib := by
--   unfold Sim.BlockPtr.getParentImpl
--   unfold Sim.BlockPtr.getParentSim
--   grind [Sim.OpOperandPtr, Sim.IRContext, Sim.ValuePtr, Sim.BlockArgumentPtr, Sim.BlockPtr, Sim.OperationPtr, Sim.BlockOperandPtr, Sim.OpResultPtr, Sim.RegionPtr, Sim.OpOperandPtrPtr, Sim.BlockOperandPtrPtr]

-- TODO
