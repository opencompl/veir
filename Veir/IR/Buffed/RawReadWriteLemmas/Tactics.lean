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

/-!
## Tactic macros for the read/write interaction lemmas

Every `<ReadStruct>.readX!_<writeStructLowerCamel>_writeY` lemma in this directory has a proof of
the shape: a fixed stack of `have`s establishing the standard bounds / disjointness / inclusion
facts for the *category* of (reader, writer), followed by a single
`grind (splits := 20) [readX!, writeY, layout_grind, <struct hints>]`.

The macros below capture those shapes, one per (reader-category, writer-category), named
`rw_<reader>_<writer>`.  Reader prefixes: `oo` = OpOperand, `or` = OpResult, `bo` = BlockOperand
(all op sub-object readers, read via `toM ctx.spec`).  Writer categories:

  `opScalar`  — the same/another operation, a scalar field write
  `block` / `region` / `blockArg` — a top-level Block / Region / BlockArgument write
  `<own>` (e.g. `rw_oo_oo`)  — the same sub-object struct, same op, possibly same slot
  the two remaining op-sub structs — another op sub-object write in the same op (hardest case)

Each macro takes the read accessor `$read`, the (qualified) write accessor `$write`, the reader
variable `$r`, the writer variable `$w`, and — where the setup needs `.ib`/`.sim` — the writer's
InBounds hypothesis `$wib`.  `$read`/`$write` are `grindParam`-typed so they splice into the closing
`grind`.  The macros reference the ambient `ctx` and global lemma names, so they use
`set_option hygiene false` (those must resolve at the use site).

These macros are NOT used for the multi-branch `rcases` proofs (ValueImpl / PtrPtr writers).
-/



namespace RwReal

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpOperandPtr reader vs. a scalar operation write. -/
scoped macro "rw_oo_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.OpOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hop2 := ctx.sim.in_bounds (.operation ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec) (by grind) (by grind)
     have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpOperandPtr.range, OpOperandPtr.toFlat, OperationPtr.toM, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpOperandPtr reader vs. a top-level `BlockPtr` write (InBounds hyp `$wib`). -/
scoped macro "rw_oo_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.OpOperandPtr.after_lt_ctx
     have := @Sim.BlockPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ($w).spec ($wib).ib
     have hw := ctx.sim.in_bounds (.block ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.block ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpOperandPtr reader vs. a top-level `RegionPtr` write. -/
scoped macro "rw_oo_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.OpOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hw := ctx.sim.in_bounds (.region ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.region ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, RegionPtr.range, RegionPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpOperandPtr reader vs. a `BlockArgumentPtr` write. -/
scoped macro "rw_oo_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.OpOperandPtr.after_lt_ctx
     have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hw := ctx.sim.in_bounds (.block ($w).spec.block) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.block ($w).spec.block) (by grind) (by grind)
     have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpOperandPtr reader vs. the same-struct `OpOperandPtr` write (same op, possibly same slot). -/
scoped macro "rw_oo_oo_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.OpOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec.op) (by grind) (by grind)
     have hincl₁ := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hincl₂ := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpOperandPtr reader vs. a `OpResultPtr` write (same op — index bounds + `Sim` unfold + ReprIndices; InBounds hyp `$wib`). -/
scoped macro "rw_oo_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.OpOperandPtr.after_lt_ctx
     have := @Sim.OpResultPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpResultPtr.range_included_op_range (ctx := ctx) ($w).spec (by grind)
     have hsim := ($wib).sim
     simp only [Sim.OpResultPtr.Sim] at hsim
     have : ($r).index < (($r).op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
     have hw2idx : ($w).spec.index < (($w).spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
     have hri := ctx.sim.repr.operations_indices ($r).op (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
       OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat, Operation.ReprIndices,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpOperandPtr reader vs. a `BlockOperandPtr` write (same op — index bounds + `Sim` unfold + ReprIndices; InBounds hyp `$wib`). -/
scoped macro "rw_oo_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.OpOperandPtr.after_lt_ctx
     have := @Sim.BlockOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     have hsim := ($wib).sim
     simp only [Sim.BlockOperandPtr.Sim] at hsim
     have : ($r).index < (($r).op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
     have hw2idx : ($w).spec.index < (($w).spec.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
     have hri := ctx.sim.repr.operations_indices ($r).op (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
       OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat, Operation.ReprIndices,
       IsIncludedI, IsDisjointI]))


open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpResultPtr reader vs. a scalar operation write. -/
scoped macro "rw_or_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.OpResultPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hop2 := ctx.sim.in_bounds (.operation ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec) (by grind) (by grind)
     have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) ($r) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpResultPtr.range, OpResultPtr.toFlat, OperationPtr.toM, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpResultPtr reader vs. a top-level `BlockPtr` write (InBounds hyp `$wib`). -/
scoped macro "rw_or_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.OpResultPtr.after_lt_ctx
     have := @Sim.BlockPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) ($r) (by grind)
     have hres := ctx.sim.in_bounds (.operation ($r).op) (by grind)
     have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ($w).spec ($wib).ib
     have hw := ctx.sim.in_bounds (.block ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.block ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpResultPtr reader vs. a top-level `RegionPtr` write. -/
scoped macro "rw_or_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.OpResultPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) ($r) (by grind)
     have hres := ctx.sim.in_bounds (.operation ($r).op) (by grind)
     have hw := ctx.sim.in_bounds (.region ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.region ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, RegionPtr.range, RegionPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpResultPtr reader vs. a `BlockArgumentPtr` write. -/
scoped macro "rw_or_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.OpResultPtr.after_lt_ctx
     have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) ($r) (by grind)
     have hres := ctx.sim.in_bounds (.operation ($r).op) (by grind)
     have hw := ctx.sim.in_bounds (.block ($w).spec.block) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.block ($w).spec.block) (by grind) (by grind)
     have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpResultPtr reader vs. the same-struct `OpResultPtr` write (same op, possibly same slot). -/
scoped macro "rw_or_or_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.OpResultPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec.op) (by grind) (by grind)
     have hincl₁ := OpResultPtr.range_included_op_range (ctx := ctx) ($r) (by grind)
     have hincl₂ := OpResultPtr.range_included_op_range (ctx := ctx) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpResultPtr reader vs. a `OpOperandPtr` write (same op — index bounds + `Sim` unfold + ReprIndices; InBounds hyp `$wib`). -/
scoped macro "rw_or_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.OpResultPtr.after_lt_ctx
     have := @Sim.OpOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) ($r) (by grind)
     have hres := ctx.sim.in_bounds (.operation ($r).op) (by grind)
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     have hsim := ($wib).sim
     simp only [Sim.OpOperandPtr.Sim] at hsim
     have : ($r).index < (($r).op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
     have hw2idx : ($w).spec.index < (($w).spec.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
     have hri := ctx.sim.repr.operations_indices ($r).op (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
       OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- OpResultPtr reader vs. a `BlockOperandPtr` write (same op — index bounds + `Sim` unfold + ReprIndices; InBounds hyp `$wib`). -/
scoped macro "rw_or_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.OpResultPtr.after_lt_ctx
     have := @Sim.BlockOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := OpResultPtr.range_included_op_range (ctx := ctx) ($r) (by grind)
     have hres := ctx.sim.in_bounds (.operation ($r).op) (by grind)
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     have hsim := ($wib).sim
     simp only [Sim.BlockOperandPtr.Sim] at hsim
     have : ($r).index < (($r).op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
     have hw2idx : ($w).spec.index < (($w).spec.op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
     have hri := ctx.sim.repr.operations_indices ($r).op (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat,
       OpResultPtr.rangeInt, OpResultPtr.toFlatNat, Operation.ReprIndices,
       IsIncludedI, IsDisjointI]))


open Lean.Parser.Tactic in
set_option hygiene false in
/-- BlockOperandPtr reader vs. a scalar operation write. -/
scoped macro "rw_bo_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hop2 := ctx.sim.in_bounds (.operation ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec) (by grind) (by grind)
     have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockOperandPtr.range, BlockOperandPtr.toFlat, OperationPtr.toM, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- BlockOperandPtr reader vs. a top-level `BlockPtr` write (InBounds hyp `$wib`). -/
scoped macro "rw_bo_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.BlockOperandPtr.after_lt_ctx
     have := @Sim.BlockPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ($w).spec ($wib).ib
     have hw := ctx.sim.in_bounds (.block ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.block ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockPtr.range, BlockPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- BlockOperandPtr reader vs. a top-level `RegionPtr` write. -/
scoped macro "rw_bo_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hw := ctx.sim.in_bounds (.region ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.region ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, RegionPtr.range, RegionPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- BlockOperandPtr reader vs. a `BlockArgumentPtr` write. -/
scoped macro "rw_bo_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockOperandPtr.after_lt_ctx
     have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hw := ctx.sim.in_bounds (.block ($w).spec.block) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.block ($w).spec.block) (by grind) (by grind)
     have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- BlockOperandPtr reader vs. the same-struct `BlockOperandPtr` write (same op, possibly same slot). -/
scoped macro "rw_bo_bo_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec.op) (by grind) (by grind)
     have hincl₁ := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hincl₂ := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- BlockOperandPtr reader vs. a `OpResultPtr` write (same op — index bounds + `Sim` unfold + ReprIndices; InBounds hyp `$wib`). -/
scoped macro "rw_bo_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.BlockOperandPtr.after_lt_ctx
     have := @Sim.OpResultPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpResultPtr.range_included_op_range (ctx := ctx) ($w).spec (by grind)
     have hsim := ($wib).sim
     simp only [Sim.OpResultPtr.Sim] at hsim
     have : ($r).index < (($r).op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
     have hw2idx : ($w).spec.index < (($w).spec.op.getNumResults! ctx.spec) := by grind [OpResultPtr.inBounds_def]
     have hri := ctx.sim.repr.operations_indices ($r).op (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, OpResultPtr.toM, OpResultPtr.range, OpResultPtr.toFlat, OpResultPtr.rangeInt, OpResultPtr.toFlatNat,
       BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat, Operation.ReprIndices,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
/-- BlockOperandPtr reader vs. a `OpOperandPtr` write (same op — index bounds + `Sim` unfold + ReprIndices; InBounds hyp `$wib`). -/
scoped macro "rw_bo_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.BlockOperandPtr.after_lt_ctx
     have := @Sim.OpOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.operation ($r).op) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     have hsim := ($wib).sim
     simp only [Sim.OpOperandPtr.Sim] at hsim
     have : ($r).index < (($r).op.getNumSuccessors! ctx.spec) := by grind [BlockOperandPtr.inBounds_def]
     have hw2idx : ($w).spec.index < (($w).spec.op.getNumOperands! ctx.spec) := by grind [OpOperandPtr.inBounds_def]
     have hri := ctx.sim.repr.operations_indices ($r).op (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockOperandPtr.toM, BlockOperandPtr.range, BlockOperandPtr.toFlat, OpOperandPtr.toM, OpOperandPtr.range, OpOperandPtr.toFlat, OpOperandPtr.rangeInt, OpOperandPtr.toFlatNat,
       BlockOperandPtr.rangeInt, BlockOperandPtr.toFlatNat, Operation.ReprIndices,
       IsIncludedI, IsDisjointI]))


open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hop2 := ctx.sim.in_bounds (.operation ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r).block) (.operation ($w).spec) (by grind) (by grind)
     have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OperationPtr.toM, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hw := ctx.sim.in_bounds (.region ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r).block) (.region ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, RegionPtr.range, RegionPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have := @Sim.BlockPtr.after_lt_ctx
     have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ($w).spec ($wib).ib
     have hw := ctx.sim.in_bounds (.block ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r).block) (.block ($w).spec) (by grind) (by grind)
     have : ($r).index < (($r).block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
     have hri := ctx.sim.repr.blocks_indices ($r).block (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, BlockPtr.range, BlockPtr.toFlat, Block.ReprIndices,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_ba_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r).block) (.block ($w).spec.block) (by grind) (by grind)
     have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     have : ($r).index < (($r).block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
     have : ($w).spec.index < (($w).spec.block.getNumArguments! ctx.spec) := by grind [BlockArgumentPtr.inBounds_def]
     have hri := ctx.sim.repr.blocks_indices ($r).block (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockArgumentPtr.rangeInt, BlockArgumentPtr.toFlatNat, Block.ReprIndices,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have := @Sim.OpResultPtr.after_lt_ctx
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r).block) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpResultPtr.range_included_op_range (ctx := ctx) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpResultPtr.range, OpResultPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have := @Sim.OpOperandPtr.after_lt_ctx
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r).block) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat,
       IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hinclr := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($r) (by grind)
     have := @Sim.BlockOperandPtr.after_lt_ctx
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r).block) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat,
       IsIncludedI, IsDisjointI]))


open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_rg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " rib:term ", " wib:term : tactic =>
  `(tactic|
    (have b1 := Sim.RegionPtr.after_lt_ctx (ctx := ctx) ($r) ($rib)
     have b2 := Sim.RegionPtr.after_lt_ctx (ctx := ctx) ($w).spec ($wib).ib
     have disj := ctx.sim.disjoint_allocs (.region ($w).spec) (.region ($r))
     have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
     grind (splits := 20) [$read, $write, layout_grind, RegionPtr.range]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.RegionPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hop2 := ctx.sim.in_bounds (.operation ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.region ($r)) (.operation ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       RegionPtr.range, RegionPtr.toFlat, OperationPtr.toM, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic|
    (have := @Sim.RegionPtr.after_lt_ctx
     have := @Sim.BlockPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ($w).spec ($wib).ib
     have hw := ctx.sim.in_bounds (.block ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.region ($r)) (.block ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       RegionPtr.range, RegionPtr.toFlat, BlockPtr.range, BlockPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.RegionPtr.after_lt_ctx
     have := @Sim.BlockArgumentPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hw := ctx.sim.in_bounds (.block ($w).spec.block) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.region ($r)) (.block ($w).spec.block) (by grind) (by grind)
     have hinclw := BlockArgumentPtr.range_included_block_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       RegionPtr.range, RegionPtr.toFlat, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.RegionPtr.after_lt_ctx
     have := @Sim.OpResultPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.region ($r)) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpResultPtr.range_included_op_range (ctx := ctx) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       RegionPtr.range, RegionPtr.toFlat, OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.RegionPtr.after_lt_ctx
     have := @Sim.OpOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.region ($r)) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       RegionPtr.range, RegionPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.RegionPtr.after_lt_ctx
     have := @Sim.BlockOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.region ($r)) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       RegionPtr.range, RegionPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]))


open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_bl_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " proj:ident ", " rib:term ", " wib:term : tactic =>
  `(tactic|
    (have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ($r) ($rib)
     have b2 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ($w).spec ($wib).ib
     have disj := ctx.sim.disjoint_allocs (.block ($w).spec) (.block ($r))
     have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
     have := ctx.sim.encoding_block ($r) (by grind) |>.$proj
     grind (splits := 20) [$read, $write, layout_grind, = Buffed.Block.Offsets.after_ideal, BlockPtr.range]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hop2 := ctx.sim.in_bounds (.operation ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r)) (.operation ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockPtr.range, BlockPtr.toFlat, OperationPtr.toM, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hw := ctx.sim.in_bounds (.region ($w).spec) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r)) (.region ($w).spec) (by grind) (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockPtr.range, BlockPtr.toFlat, RegionPtr.range, RegionPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " proj:ident ", " rib:term ", " wib:term : tactic =>
  `(tactic|
    (have b1 := Sim.BlockPtr.after_lt_ctx (ctx := ctx) ($r) ($rib)
     have disj := ctx.sim.disjoint_allocs (.block ($w).spec.block) (.block ($r))
     have hsize : ctx.buf.mem.size < Int64.maxValue.toInt := by grind [ctx.buf.mem.fits_in_memory]
     have := ctx.sim.encoding_block ($r) (by grind) |>.$proj
     have hincl := BlockArgumentPtr.range_included_block_range (by grind) ($w).spec ($wib).ib
     have hsim := ($wib).sim
     have := ctx.sim.in_bounds (.block ($r)) (by grind)
     simp only [Sim.BlockArgumentPtr.Sim] at hsim
     grind (splits := 20) [$read, $write, layout_grind,
       = Buffed.Block.Offsets.after_ideal, BlockPtr.range,
       BlockArgumentPtr.toM, BlockArgumentPtr.range, BlockArgumentPtr.toFlat, IsIncludedI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockPtr.after_lt_ctx
     have := @Sim.OpResultPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r)) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpResultPtr.range_included_op_range (ctx := ctx) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockPtr.range, BlockPtr.toFlat, OpResultPtr.range, OpResultPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockPtr.after_lt_ctx
     have := @Sim.OpOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r)) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := OpOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockPtr.range, BlockPtr.toFlat, OpOperandPtr.range, OpOperandPtr.toFlat, IsIncludedI, IsDisjointI]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have := @Sim.BlockPtr.after_lt_ctx
     have := @Sim.BlockOperandPtr.after_lt_ctx
     have : ctx.buf.mem.size < 2 ^ 63 - 1 := by grind
     have hw := ctx.sim.in_bounds (.operation ($w).spec.op) (by grind)
     have hdisj := ctx.sim.disjoint_allocs (.block ($r)) (.operation ($w).spec.op) (by grind) (by grind)
     have hinclw := BlockOperandPtr.range_included_op_range (ctx := ctx.spec) (by grind) ($w).spec (by grind)
     grind (splits := 20) [$read, $write, layout_grind,
       BlockPtr.range, BlockPtr.toFlat, BlockOperandPtr.range, BlockOperandPtr.toFlat, IsIncludedI, IsDisjointI]))


end RwReal

/-!
### Stub implementations

Same signatures as the `RwReal.*_impl` macros above, but each expands directly to `sorry`.  These skip
the (very slow) `grind` calls so the files that *use* these tactics compile quickly while iterating.
-/

namespace RwStub

open Lean.Parser.Tactic in
scoped macro "rw_oo_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_oo_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_oo_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_oo_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_oo_oo_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_oo_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_oo_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_or_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_or_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_or_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_or_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_or_or_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_or_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_or_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bo_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bo_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bo_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bo_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bo_bo_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bo_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bo_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_ba_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_ba_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_ba_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_ba_ba_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_ba_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_ba_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_ba_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_rg_rg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " rib:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_rg_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_rg_block_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_rg_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_rg_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_rg_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_rg_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bl_bl_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " proj:ident ", " rib:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bl_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bl_region_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bl_blockArg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " proj:ident ", " rib:term ", " wib:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bl_opResult_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bl_opOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)
open Lean.Parser.Tactic in
scoped macro "rw_bl_blockOperand_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic => `(tactic| sorry)

end RwStub

/-!
### The switch

`open`  **exactly one**  of the two namespaces below.  The `*_impl` macros it brings into scope are the
ones the public `rw_*` forwarders (further down) delegate to.

  * `RwReal` — the real proofs (default).
  * `RwStub` — fast `sorry` stubs; flip to this while iterating on the consumer files, flip back before
    committing.
-/

open scoped RwReal
-- open scoped RwStub

/-!
### Public `rw_*` entry points

Thin forwarders to whichever `*_impl` is currently opened.  Consumers keep using the bare `rw_*` names
(via `open scoped Veir.Buffed`) and never see the split.
-/

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_opScalar" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_oo_opScalar_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_block" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_oo_block_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_region" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_oo_region_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_blockArg" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_oo_blockArg_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_oo" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_oo_oo_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_opResult" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_oo_opResult_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_blockOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_oo_blockOperand_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_opScalar" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_or_opScalar_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_block" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_or_block_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_region" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_or_region_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_blockArg" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_or_blockArg_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_or" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_or_or_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_opOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_or_opOperand_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_blockOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_or_blockOperand_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_opScalar" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bo_opScalar_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_block" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_bo_block_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_region" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bo_region_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_blockArg" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bo_blockArg_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_bo" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bo_bo_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_opResult" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_bo_opResult_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_opOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_bo_opOperand_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_opScalar" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_ba_opScalar_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_region" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_ba_region_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_block" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_ba_block_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_ba" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_ba_ba_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_opResult" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_ba_opResult_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_opOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_ba_opOperand_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_blockOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_ba_blockOperand_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_rg" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " rib:term ", " wib:term : tactic =>
  `(tactic| rw_rg_rg_impl $read, $write, $r, $w, $rib, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_opScalar" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_rg_opScalar_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_block" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " wib:term : tactic =>
  `(tactic| rw_rg_block_impl $read, $write, $r, $w, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_blockArg" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_rg_blockArg_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_opResult" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_rg_opResult_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_opOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_rg_opOperand_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_blockOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_rg_blockOperand_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_bl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " proj:ident ", " rib:term ", " wib:term : tactic =>
  `(tactic| rw_bl_bl_impl $read, $write, $r, $w, $proj, $rib, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_opScalar" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bl_opScalar_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_region" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bl_region_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_blockArg" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " proj:ident ", " rib:term ", " wib:term : tactic =>
  `(tactic| rw_bl_blockArg_impl $read, $write, $r, $w, $proj, $rib, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_opResult" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bl_opResult_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_opOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bl_opOperand_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bl_blockOperand" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bl_blockOperand_impl $read, $write, $r, $w)

end read_write

end Veir.Buffed
