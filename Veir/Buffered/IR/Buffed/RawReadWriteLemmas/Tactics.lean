module

public import Veir.Buffered.IR.Buffed.RawAccessors
public import Veir.Buffered.IR.Buffed.Sim
public import Veir.Buffered.IR.Buffed.SimDefs
public import Veir.Buffered.IR.Buffed.RawAccessorFootprints

public section

set_option linter.unusedVariables false

namespace Veir.Buffered.Buffed

section read_write

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo] {ctx : Sim.IRContext OpInfo}

/-! Tactic macros for the read/write interaction lemmas -/

namespace RwReal

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_rg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " rib:term ", " wib:term : tactic =>
  `(tactic|
    (have himpl : ($w).spec.toM = ($w).impl := ($wib).sim.out
     have haddr_r := _root_.Veir.Buffered.RegionPtr.toM_toNat ctx.sim.repr ($r) ($rib)
     have haddr_w := _root_.Veir.Buffered.RegionPtr.toM_toNat ctx.sim.repr ($w).spec ($wib).ib
     have hrange_r := _root_.Veir.Buffered.Sim.RegionPtr.range_linear ($r) ($rib)
     have hrange_w := _root_.Veir.Buffered.Sim.RegionPtr.range_linear ($w).spec ($wib).ib
     by_cases heq : ($r) = ($w).spec
     · subst heq
       grind (splits := 4) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffered.Buffed.IRBufContext.size_def, add_nat_range_def]
     · have hdisj := _root_.Veir.Buffered.Sim.disjoint_region_region ($r) ($w).spec ($rib) ($wib).ib heq
       grind (splits := 4) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffered.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.Buffered.RegionPtr.rangeInt, _root_.Veir.Buffered.RegionPtr.toFlat]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_oo_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.Buffered.Sim.OpOperandPtr.toM_toNat ($r) hrib
     have hrpib := _root_.Veir.Buffered.Sim.OpOperandPtr.op_inBounds hrib
     have hrincl := _root_.Veir.Buffered.Sim.OpOperandPtr.slot_included ($r) hrib
     have hrprange := _root_.Veir.Buffered.Sim.OperationPtr.range_linear ($r).op hrpib
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM ctx.spec = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.Buffered.Sim.OpOperandPtr.toM_toNat ($w).spec hwib.ib
     have hwpib := _root_.Veir.Buffered.Sim.OpOperandPtr.op_inBounds hwib.ib
     have hwincl := _root_.Veir.Buffered.Sim.OpOperandPtr.slot_included ($w).spec hwib.ib
     have hwprange := _root_.Veir.Buffered.Sim.OperationPtr.range_linear ($w).spec.op hwpib
     have hdisj := fun hpne : ($r).op ≠ ($w).spec.op => _root_.Veir.Buffered.Sim.disjoint_operation_operation ($r).op ($w).spec.op hrpib hwpib hpne
     have hsize := _root_.Veir.Buffered.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffered.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.Buffered.OpOperandPtr.toFlatNat, _root_.Veir.Buffered.OpOperandPtr.rangeInt, _root_.Veir.Buffered.OperationPtr.toFlat, _root_.Veir.Buffered.OpOperandPtr.toFlatNat, _root_.Veir.Buffered.OpOperandPtr.rangeInt, _root_.Veir.Buffered.OperationPtr.toFlat, _root_.Veir.Buffered.OpOperandPtr.ext]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_or_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.Buffered.Sim.OpResultPtr.toM_toNat ($r) hrib
     have hrpib := _root_.Veir.Buffered.Sim.OpResultPtr.op_inBounds hrib
     have hrincl := _root_.Veir.Buffered.Sim.OpResultPtr.slot_included ($r) hrib
     have hrprange := _root_.Veir.Buffered.Sim.OperationPtr.range_linear ($r).op hrpib
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM ctx.spec = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.Buffered.Sim.OpResultPtr.toM_toNat ($w).spec hwib.ib
     have hwpib := _root_.Veir.Buffered.Sim.OpResultPtr.op_inBounds hwib.ib
     have hwincl := _root_.Veir.Buffered.Sim.OpResultPtr.slot_included ($w).spec hwib.ib
     have hwprange := _root_.Veir.Buffered.Sim.OperationPtr.range_linear ($w).spec.op hwpib
     have hdisj := fun hpne : ($r).op ≠ ($w).spec.op => _root_.Veir.Buffered.Sim.disjoint_operation_operation ($r).op ($w).spec.op hrpib hwpib hpne
     have hsize := _root_.Veir.Buffered.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffered.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.Buffered.OpResultPtr.toFlatNat, _root_.Veir.Buffered.OpResultPtr.rangeInt, _root_.Veir.Buffered.OperationPtr.toFlat, _root_.Veir.Buffered.OpResultPtr.toFlatNat, _root_.Veir.Buffered.OpResultPtr.rangeInt, _root_.Veir.Buffered.OperationPtr.toFlat, _root_.Veir.Buffered.OpResultPtr.ext]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_bo_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.Buffered.Sim.BlockOperandPtr.toM_toNat ($r) hrib
     have hrpib := _root_.Veir.Buffered.Sim.BlockOperandPtr.op_inBounds hrib
     have hrincl := _root_.Veir.Buffered.Sim.BlockOperandPtr.slot_included ($r) hrib
     have hrprange := _root_.Veir.Buffered.Sim.OperationPtr.range_linear ($r).op hrpib
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM ctx.spec = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.Buffered.Sim.BlockOperandPtr.toM_toNat ($w).spec hwib.ib
     have hwpib := _root_.Veir.Buffered.Sim.BlockOperandPtr.op_inBounds hwib.ib
     have hwincl := _root_.Veir.Buffered.Sim.BlockOperandPtr.slot_included ($w).spec hwib.ib
     have hwprange := _root_.Veir.Buffered.Sim.OperationPtr.range_linear ($w).spec.op hwpib
     have hdisj := fun hpne : ($r).op ≠ ($w).spec.op => _root_.Veir.Buffered.Sim.disjoint_operation_operation ($r).op ($w).spec.op hrpib hwpib hpne
     have hsize := _root_.Veir.Buffered.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffered.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.Buffered.BlockOperandPtr.toFlatNat, _root_.Veir.Buffered.BlockOperandPtr.rangeInt, _root_.Veir.Buffered.OperationPtr.toFlat, _root_.Veir.Buffered.BlockOperandPtr.toFlatNat, _root_.Veir.Buffered.BlockOperandPtr.rangeInt, _root_.Veir.Buffered.OperationPtr.toFlat, _root_.Veir.Buffered.BlockOperandPtr.ext]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_ba_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.Buffered.Sim.BlockArgumentPtr.toM_toNat ($r) hrib
     have hrpib := _root_.Veir.Buffered.Sim.BlockArgumentPtr.block_inBounds hrib
     have hrincl := _root_.Veir.Buffered.Sim.BlockArgumentPtr.slot_included ($r) hrib
     have hrprange := _root_.Veir.Buffered.Sim.BlockPtr.range_linear ($r).block hrpib
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.Buffered.Sim.BlockArgumentPtr.toM_toNat ($w).spec hwib.ib
     have hwpib := _root_.Veir.Buffered.Sim.BlockArgumentPtr.block_inBounds hwib.ib
     have hwincl := _root_.Veir.Buffered.Sim.BlockArgumentPtr.slot_included ($w).spec hwib.ib
     have hwprange := _root_.Veir.Buffered.Sim.BlockPtr.range_linear ($w).spec.block hwpib
     have hdisj := fun hpne : ($r).block ≠ ($w).spec.block => _root_.Veir.Buffered.Sim.disjoint_block_block ($r).block ($w).spec.block hrpib hwpib hpne
     have hsize := _root_.Veir.Buffered.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffered.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.Buffered.BlockArgumentPtr.toFlatNat, _root_.Veir.Buffered.BlockArgumentPtr.rangeInt, _root_.Veir.Buffered.BlockPtr.rangeInt, _root_.Veir.Buffered.BlockPtr.toFlat, _root_.Veir.Buffered.BlockArgumentPtr.toFlatNat, _root_.Veir.Buffered.BlockArgumentPtr.rangeInt, _root_.Veir.Buffered.BlockPtr.rangeInt, _root_.Veir.Buffered.BlockPtr.toFlat, _root_.Veir.Buffered.BlockArgumentPtr.ext]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_op_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.Buffered.OperationPtr.toM_toNat ctx.sim.repr ($r) hrib
     have hrrange := _root_.Veir.Buffered.Sim.OperationPtr.range_linear ($r) hrib
     try have hincl_n := _root_.Veir.Buffered.OperationPtr.nthRegion_range_included_op_range ctx ($r) idx hidx hrib
     try have hoff_n := _root_.Veir.Buffered.OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt (ctx := ctx) (idx := idx) ($r) hrib (by have := ctx.sim.repr.operations_indices ($r) hrib |>.regions; grind)
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.Buffered.OperationPtr.toM_toNat ctx.sim.repr ($w).spec hwib.ib
     have hwrange := _root_.Veir.Buffered.Sim.OperationPtr.range_linear ($w).spec hwib.ib
     have hdisj := fun hpne : ($r) ≠ ($w).spec => _root_.Veir.Buffered.Sim.disjoint_operation_operation ($r) ($w).spec hrib hwib.ib hpne
     have hsize := _root_.Veir.Buffered.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffered.Buffed.IRBufContext.size_def, add_nat_range_def,
         $read, _root_.Veir.Buffered.Buffed.OperationMPtr.computeResultOffset!, _root_.Veir.Buffered.Buffed.OperationMPtr.computeResultsOffset!,
         _root_.Veir.Buffered.Buffed.OperationMPtr.computeBlockOperandOffset!, _root_.Veir.Buffered.Buffed.OperationMPtr.computeBlockOperandsOffset!,
         _root_.Veir.Buffered.Buffed.OperationMPtr.computeOperandOffset!, _root_.Veir.Buffered.Buffed.OperationMPtr.computeOperandsOffset!,
         _root_.Veir.Buffered.Buffed.OperationMPtr.computeRegionOffset!, _root_.Veir.Buffered.Buffed.OperationMPtr.computeRegionsOffset!,
         ExArray.read64!_eq_read64', _root_.Veir.Buffered.Buffed.uint64_add_int64_toNat, _root_.Veir.Buffered.OperationPtr.toFlat]))

end RwReal
open scoped RwReal

/-! Public `rw_*` entry points -/
open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_oo" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_oo_oo_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_or" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_or_or_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_bo" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_bo_bo_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_ba" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_ba_ba_impl $read, $write, $r, $w)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_rg" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " rib:term ", " wib:term : tactic =>
  `(tactic| rw_rg_rg_impl $read, $write, $r, $w, $rib, $wib)

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_op_opScalar" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic| rw_op_opScalar_impl $read, $write, $r, $w)

end read_write
end Veir.Buffered.Buffed
