module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs
public import Veir.IR.Buffed.RawAccessorFootprints

public section

set_option linter.unusedVariables false

namespace Veir.Buffed

section read_write

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] {ctx : Sim.IRContext OpInfo}

/-! Tactic macros for the read/write interaction lemmas -/

namespace RwReal

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_rg_rg_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term ", " rib:term ", " wib:term : tactic =>
  `(tactic|
    (have himpl : ($w).spec.toM = ($w).impl := ($wib).sim.out
     have haddr_r := _root_.Veir.RegionPtr.toM_toNat ctx.sim.repr ($r) ($rib)
     have haddr_w := _root_.Veir.RegionPtr.toM_toNat ctx.sim.repr ($w).spec ($wib).ib
     have hrange_r := _root_.Veir.Sim.RegionPtr.range_linear ($r) ($rib)
     have hrange_w := _root_.Veir.Sim.RegionPtr.range_linear ($w).spec ($wib).ib
     by_cases heq : ($r) = ($w).spec
     · subst heq
       grind (splits := 4) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def]
     · have hdisj := _root_.Veir.Sim.disjoint_region_region ($r) ($w).spec ($rib) ($wib).ib heq
       grind (splits := 4) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.RegionPtr.rangeInt, _root_.Veir.RegionPtr.toFlat]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_oo_oo_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.Sim.OpOperandPtr.toM_toNat ($r) hrib
     have hrpib := _root_.Veir.Sim.OpOperandPtr.op_inBounds hrib
     have hrincl := _root_.Veir.Sim.OpOperandPtr.slot_included ($r) hrib
     have hrprange := _root_.Veir.Sim.OperationPtr.range_linear ($r).op hrpib
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM ctx.spec = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.Sim.OpOperandPtr.toM_toNat ($w).spec hwib.ib
     have hwpib := _root_.Veir.Sim.OpOperandPtr.op_inBounds hwib.ib
     have hwincl := _root_.Veir.Sim.OpOperandPtr.slot_included ($w).spec hwib.ib
     have hwprange := _root_.Veir.Sim.OperationPtr.range_linear ($w).spec.op hwpib
     have hdisj := fun hpne : ($r).op ≠ ($w).spec.op => _root_.Veir.Sim.disjoint_operation_operation ($r).op ($w).spec.op hrpib hwpib hpne
     have hsize := _root_.Veir.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.OpOperandPtr.toFlatNat, _root_.Veir.OpOperandPtr.rangeInt, _root_.Veir.OperationPtr.toFlat, _root_.Veir.OpOperandPtr.toFlatNat, _root_.Veir.OpOperandPtr.rangeInt, _root_.Veir.OperationPtr.toFlat, _root_.Veir.OpOperandPtr.ext]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_or_or_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.Sim.OpResultPtr.toM_toNat ($r) hrib
     have hrpib := _root_.Veir.Sim.OpResultPtr.op_inBounds hrib
     have hrincl := _root_.Veir.Sim.OpResultPtr.slot_included ($r) hrib
     have hrprange := _root_.Veir.Sim.OperationPtr.range_linear ($r).op hrpib
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM ctx.spec = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.Sim.OpResultPtr.toM_toNat ($w).spec hwib.ib
     have hwpib := _root_.Veir.Sim.OpResultPtr.op_inBounds hwib.ib
     have hwincl := _root_.Veir.Sim.OpResultPtr.slot_included ($w).spec hwib.ib
     have hwprange := _root_.Veir.Sim.OperationPtr.range_linear ($w).spec.op hwpib
     have hdisj := fun hpne : ($r).op ≠ ($w).spec.op => _root_.Veir.Sim.disjoint_operation_operation ($r).op ($w).spec.op hrpib hwpib hpne
     have hsize := _root_.Veir.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.OpResultPtr.toFlatNat, _root_.Veir.OpResultPtr.rangeInt, _root_.Veir.OperationPtr.toFlat, _root_.Veir.OpResultPtr.toFlatNat, _root_.Veir.OpResultPtr.rangeInt, _root_.Veir.OperationPtr.toFlat, _root_.Veir.OpResultPtr.ext]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_bo_bo_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.Sim.BlockOperandPtr.toM_toNat ($r) hrib
     have hrpib := _root_.Veir.Sim.BlockOperandPtr.op_inBounds hrib
     have hrincl := _root_.Veir.Sim.BlockOperandPtr.slot_included ($r) hrib
     have hrprange := _root_.Veir.Sim.OperationPtr.range_linear ($r).op hrpib
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM ctx.spec = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.Sim.BlockOperandPtr.toM_toNat ($w).spec hwib.ib
     have hwpib := _root_.Veir.Sim.BlockOperandPtr.op_inBounds hwib.ib
     have hwincl := _root_.Veir.Sim.BlockOperandPtr.slot_included ($w).spec hwib.ib
     have hwprange := _root_.Veir.Sim.OperationPtr.range_linear ($w).spec.op hwpib
     have hdisj := fun hpne : ($r).op ≠ ($w).spec.op => _root_.Veir.Sim.disjoint_operation_operation ($r).op ($w).spec.op hrpib hwpib hpne
     have hsize := _root_.Veir.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.BlockOperandPtr.toFlatNat, _root_.Veir.BlockOperandPtr.rangeInt, _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockOperandPtr.toFlatNat, _root_.Veir.BlockOperandPtr.rangeInt, _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockOperandPtr.ext]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_ba_ba_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.Sim.BlockArgumentPtr.toM_toNat ($r) hrib
     have hrpib := _root_.Veir.Sim.BlockArgumentPtr.block_inBounds hrib
     have hrincl := _root_.Veir.Sim.BlockArgumentPtr.slot_included ($r) hrib
     have hrprange := _root_.Veir.Sim.BlockPtr.range_linear ($r).block hrpib
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.Sim.BlockArgumentPtr.toM_toNat ($w).spec hwib.ib
     have hwpib := _root_.Veir.Sim.BlockArgumentPtr.block_inBounds hwib.ib
     have hwincl := _root_.Veir.Sim.BlockArgumentPtr.slot_included ($w).spec hwib.ib
     have hwprange := _root_.Veir.Sim.BlockPtr.range_linear ($w).spec.block hwpib
     have hdisj := fun hpne : ($r).block ≠ ($w).spec.block => _root_.Veir.Sim.disjoint_block_block ($r).block ($w).spec.block hrpib hwpib hpne
     have hsize := _root_.Veir.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
         _root_.Veir.BlockArgumentPtr.toFlatNat, _root_.Veir.BlockArgumentPtr.rangeInt, _root_.Veir.BlockPtr.rangeInt, _root_.Veir.BlockPtr.toFlat, _root_.Veir.BlockArgumentPtr.toFlatNat, _root_.Veir.BlockArgumentPtr.rangeInt, _root_.Veir.BlockPtr.rangeInt, _root_.Veir.BlockPtr.toFlat, _root_.Veir.BlockArgumentPtr.ext]))

open Lean.Parser.Tactic in
set_option hygiene false in
scoped macro "rw_op_opScalar_impl" read:grindParam ", " write:grindParam ", " r:term ", " w:term : tactic =>
  `(tactic|
    (have hrib : ($r).InBounds ctx.spec := by assumption
     have haddr_r := _root_.Veir.OperationPtr.toM_toNat ctx.sim.repr ($r) hrib
     have hrrange := _root_.Veir.Sim.OperationPtr.range_linear ($r) hrib
     try have hincl_n := _root_.Veir.OperationPtr.nthRegion_range_included_op_range ctx ($r) idx hidx hrib
     try have hoff_n := _root_.Veir.OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt (ctx := ctx) (idx := idx) ($r) hrib (by have := ctx.sim.repr.operations_indices ($r) hrib |>.regions; grind)
     have hwib : ($w).InBounds ctx := by assumption
     have himpl : ($w).spec.toM = ($w).impl := hwib.sim.out
     have haddr_w := _root_.Veir.OperationPtr.toM_toNat ctx.sim.repr ($w).spec hwib.ib
     have hwrange := _root_.Veir.Sim.OperationPtr.range_linear ($w).spec hwib.ib
     have hdisj := fun hpne : ($r) ≠ ($w).spec => _root_.Veir.Sim.disjoint_operation_operation ($r) ($w).spec hrib hwib.ib hpne
     have hsize := _root_.Veir.Sim.IRContext.mem_size_lt ctx
     grind (splits := 6) only [footprint_grind, isDisjointI_def, IsIncludedI, _root_.Veir.Buffed.IRBufContext.size_def, add_nat_range_def,
         $read, _root_.Veir.Buffed.OperationMPtr.computeResultOffset!, _root_.Veir.Buffed.OperationMPtr.computeResultsOffset!,
         _root_.Veir.Buffed.OperationMPtr.computeBlockOperandOffset!, _root_.Veir.Buffed.OperationMPtr.computeBlockOperandsOffset!,
         _root_.Veir.Buffed.OperationMPtr.computeOperandOffset!, _root_.Veir.Buffed.OperationMPtr.computeOperandsOffset!,
         _root_.Veir.Buffed.OperationMPtr.computeRegionOffset!, _root_.Veir.Buffed.OperationMPtr.computeRegionsOffset!,
         ExArray.read64!_eq_read64', _root_.Veir.Buffed.uint64_add_int64_toNat, _root_.Veir.OperationPtr.toFlat]))

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
end Veir.Buffed
