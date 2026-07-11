module

public import Lean

/-! # The frame-based link-setter `Sim` proof macro

`prove_setLinkSim` lives in its own leaf module (importing only `Lean`): the quotations
resolve every Veir name at expansion site, so no other import is needed, and the module
only recompiles when this file changes.

The macro is split into one top-level builder per proof section: fused into a single
definition, the code generator's base-phase `simp` inlines the whole quotation nest
(~1.9M node visits, ~4 minutes); as separate small definitions it compiles in seconds. -/

public section

namespace Veir
namespace ProveSetLinkSim

open Lean

set_option hygiene false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Everything the section builders need from the macro's arguments. -/
meta structure Cfg where
  ctx : Ident
  w : Ident
  k : String
  wsfxS : String
  ssfxS : String
  isSum : Bool
  wparent : Term
  wparentIb : Term
  wpk : String

meta def prodName (cfg : Cfg) (readerNS field : String) : Term :=
  mkIdent ((((Name.mkSimple "Buffed").str readerNS).str s!"read{field}!_{cfg.wsfxS}"))

meta def congName (cfg : Cfg) (reader : String) : Term :=
  let comps := reader.splitOn "."
  mkIdent (comps.foldl (init := Name.anonymous) (fun n c => n.str c) |>.appendAfter s!"_{cfg.ssfxS}")

meta def simDefName (n : String) : Term :=
  mkIdent ((Name.mkSimple "Sim").str n |>.str "Sim_def")

meta def gp (t : Term) : MacroM (TSyntax ``Parser.Tactic.grindParam) :=
  `(Parser.Tactic.grindParam| $t:term)

meta def gpEq (t : Term) : MacroM (TSyntax ``Parser.Tactic.grindParam) :=
  `(Parser.Tactic.grindParam| = $t:term)

meta def sd (n : String) : MacroM (TSyntax ``Parser.Tactic.grindParam) :=
  gpEq (simDefName n)

meta def wpParam (cfg : Cfg) : MacroM (TSyntax ``Parser.Tactic.grindParam) :=
  gp (⟨cfg.w.raw⟩ : Term)

/-- The shared narrow interval-disjointness discharge. -/
meta def disch : MacroM (TSyntax `tactic) :=
  `(tactic| grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def, Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat, Veir.OperationPtr.toFlat])

/-- `disch` plus the `UInt64.toNat_ofNat'` bridge for the NthRegion array slot. -/
meta def dischU : MacroM (TSyntax `tactic) :=
  `(tactic| grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def, Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat, Veir.OperationPtr.toFlat, UInt64.toNat_ofNat'])

/-- A per-field product-lemma clause for the writer's own section. The sum writers'
product lemmas match on the sum constructor, which needs the default rule set; pass only
non-global params there to stay warning-free. -/
meta def mkClause (cfg : Cfg) (hsrc : Term) (readerNS field : String) (congs : List String)
    (extras : List (TSyntax ``Parser.Tactic.grindParam))
    (pre : List (TSyntax `tactic) := []) : MacroM (TSyntax `tactic) := do
  let p ← gpEq (prodName cfg readerNS field)
  let g ← if cfg.isSum then do
      let wParam ← wpParam cfg
      `(tactic| grind (splits := 6) [$p:grindParam, $wParam:grindParam])
    else do
      let cs ← congs.mapM (fun c => gp (congName cfg c))
      let params := #[p] ++ cs.toArray ++ extras.toArray
      `(tactic| grind (splits := 4) only [$params,*])
  let base ← `(tactic| (have := $hsrc; $g:tactic))
  pre.foldrM (fun t acc => `(tactic| ($t:tactic; $acc:tactic))) base

/-- `get!`-congruence side-goals: narrow list for scalar writers; the sum writers'
congruence lemmas match on the sum constructor, which needs default grind. -/
meta def mkSg (cfg : Cfg) (c : String) : MacroM Term := do
  if cfg.isSum then `(by grind) else `(by grind only [$(← gp (congName cfg c)):grindParam])

/-- Writer-side footprint facts, emitted once. -/
meta def mkWhaves (cfg : Cfg) : MacroM (TSyntax `tactic) :=
  let ctx := cfg.ctx
  match cfg.k with
  | "op" => `(tactic|
      (have himpl := ib.sim.out
       have haddr_w := Veir.OperationPtr.toM_toNat ($ctx).sim.repr ptr.spec ib.ib
       have hwrange := Sim.OperationPtr.range_linear ptr.spec ib.ib
       have hsize := Sim.IRContext.mem_size_lt $ctx))
  | "oo" => `(tactic|
      (have himpl := ib.sim.out
       have haddr_w := Sim.OpOperandPtr.toM_toNat ptr.spec ib.ib
       have hwpib := Sim.OpOperandPtr.op_inBounds ib.ib
       have hwincl := Sim.OpOperandPtr.slot_included ptr.spec ib.ib
       have hwrange := Sim.OperationPtr.range_linear ptr.spec.op hwpib
       have hsize := Sim.IRContext.mem_size_lt $ctx))
  | "bo" => `(tactic|
      (have himpl := ib.sim.out
       have haddr_w := Sim.BlockOperandPtr.toM_toNat ptr.spec ib.ib
       have hwpib := Sim.BlockOperandPtr.op_inBounds ib.ib
       have hwincl := Sim.BlockOperandPtr.slot_included ptr.spec ib.ib
       have hwrange := Sim.OperationPtr.range_linear ptr.spec.op hwpib
       have hsize := Sim.IRContext.mem_size_lt $ctx))
  | "rs" => `(tactic|
      (have himpl := ib.sim.out
       have haddr_w := Sim.OpResultPtr.toM_toNat ptr.spec ib.ib
       have hwpib := Sim.OpResultPtr.op_inBounds ib.ib
       have hwincl := Sim.OpResultPtr.slot_included ptr.spec ib.ib
       have hwrange := Sim.OperationPtr.range_linear ptr.spec.op hwpib
       have hsize := Sim.IRContext.mem_size_lt $ctx))
  | "ba" => `(tactic|
      (have himpl := ib.sim.out
       have haddr_w := Sim.BlockArgumentPtr.toM_toNat ptr.spec ib.ib
       have hwpib := Sim.BlockArgumentPtr.block_inBounds ib.ib
       have hwincl := Sim.BlockArgumentPtr.slot_included ptr.spec ib.ib
       have hwrange := Sim.BlockPtr.range_linear ptr.spec.block hwpib
       have hsize := Sim.IRContext.mem_size_lt $ctx))
  | "bl" => `(tactic|
      (have himpl := ib.sim.out
       have haddr_w := Veir.BlockPtr.toM_toNat ($ctx).sim.repr ptr.spec ib.ib
       have hwrange := Sim.BlockPtr.range_linear ptr.spec ib.ib
       have hsize := Sim.IRContext.mem_size_lt $ctx))
  | "vi" => `(tactic|
      (have haddr_w := Sim.ValuePtr.impl_toNat ptr ib
       have hfoot_w := Sim.ValuePtr.footprint_bound ptr.spec ib.ib
       have hsize := Sim.IRContext.mem_size_lt $ctx))
  | "oopp" => `(tactic|
      (have haddr_w := Sim.OpOperandPtrPtr.impl_toNat ptr ib
       have hfoot_w := Sim.OpOperandPtrPtr.footprint_bound ptr.spec ib.ib
       have hsize := Sim.IRContext.mem_size_lt $ctx))
  | "bopp" => `(tactic|
      (have haddr_w := Sim.BlockOperandPtrPtr.impl_toNat ptr ib
       have hfoot_w := Sim.BlockOperandPtrPtr.footprint_bound ptr.spec ib.ib
       have hsize := Sim.IRContext.mem_size_lt $ctx))
  | _ => `(tactic|
      (have himpl := ib.sim.out
       have haddr_w := Veir.RegionPtr.toM_toNat ($ctx).sim.repr ptr.spec ib.ib
       have hwrange := Sim.RegionPtr.range_linear ptr.spec ib.ib
       have hsize := Sim.IRContext.mem_size_lt $ctx))

/-- Reader-parent-vs-writer-parent disjointness fact. -/
meta def mkHdisjFor (cfg : Cfg) (rk : String) (r rib : Term) : MacroM (TSyntax `tactic) := do
  let wparent := cfg.wparent
  let wparentIb := cfg.wparentIb
  match rk, cfg.wpk with
  | "op", "vi" => `(tactic|
      (have hdisjH := Sim.ValuePtr.disjoint_operation_header ptr.spec ib.ib $r $rib
       have hdisjA := Sim.ValuePtr.disjoint_operation_arrays ptr.spec ib.ib $r $rib))
  | "block", "vi" => `(tactic| have hdisj := Sim.ValuePtr.disjoint_block_header ptr.spec ib.ib $r $rib)
  | _, "vi" => `(tactic| have hdisj := Sim.ValuePtr.disjoint_region_range ptr.spec ib.ib $r $rib)
  | "op", "oopp" => `(tactic|
      (have hdisjH := Sim.OpOperandPtrPtr.disjoint_operation_header ptr.spec ib.ib $r $rib
       have hdisjA := Sim.OpOperandPtrPtr.disjoint_operation_arrays_bo ptr.spec ib.ib $r $rib))
  | "block", "oopp" => `(tactic| have hdisj := Sim.OpOperandPtrPtr.disjoint_block_header ptr.spec ib.ib $r $rib)
  | _, "oopp" => `(tactic| have hdisj := Sim.OpOperandPtrPtr.disjoint_region_range ptr.spec ib.ib $r $rib)
  | "op", "bopp" => `(tactic|
      (have hdisjH := Sim.BlockOperandPtrPtr.disjoint_operation_upTo_bo ptr.spec ib.ib $r $rib
       have hdisjA := Sim.BlockOperandPtrPtr.disjoint_operation_regions ptr.spec ib.ib $r $rib))
  | "block", "bopp" => `(tactic| have hdisj := Sim.BlockOperandPtrPtr.disjoint_block_tail ptr.spec ib.ib $r $rib)
  | _, "bopp" => `(tactic| have hdisj := Sim.BlockOperandPtrPtr.disjoint_region_range ptr.spec ib.ib $r $rib)
  | "op", "op" => `(tactic| have hdisj := fun hne : $r ≠ $wparent => Sim.disjoint_operation_operation $r $wparent $rib $wparentIb hne)
  | "op", "block" => `(tactic| have hdisj := Sim.disjoint_operation_block $r $wparent $rib $wparentIb)
  | "op", _ => `(tactic| have hdisj := Sim.disjoint_operation_region $r $wparent $rib $wparentIb)
  | "block", "op" => `(tactic| have hdisj := Sim.disjoint_block_operation $r $wparent $rib $wparentIb)
  | "block", "block" => `(tactic| have hdisj := fun hne : $r ≠ $wparent => Sim.disjoint_block_block $r $wparent $rib $wparentIb hne)
  | "block", _ => `(tactic| have hdisj := Sim.disjoint_block_region $r $wparent $rib $wparentIb)
  | _, "op" => `(tactic| have hdisj := Sim.disjoint_region_operation $r $wparent $rib $wparentIb)
  | _, "block" => `(tactic| have hdisj := Sim.disjoint_region_block $r $wparent $rib $wparentIb)
  | _, _ => `(tactic| have hdisj := fun hne : $r ≠ $wparent => Sim.disjoint_region_region $r $wparent $rib $wparentIb hne)

/-- Layout-preservation transports for the pushed value's `Sim` fact. -/
meta def mkHsimv (vib : Option Ident) : MacroM (TSyntax `tactic) :=
  match vib with
  | some v => `(tactic|
      (have hsimv := ($v).sim
       try simp only [Veir.Sim.IRContext.inner] at hsimv
       try have hsimO := OpOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp ($v).ib)
       try have hsimO := BlockOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp ($v).ib)
       try have hsimM := OpOperandPtrPtr.layoutPreserved_same_toM hlay ($v).ib
       try have hsimM := BlockOperandPtrPtr.layoutPreserved_same_toM hlay ($v).ib
       try have hsimM := ValuePtr.layoutPreserved_same_toM hlay ($v).ib))
  | none => `(tactic| skip)

/-- A single count-field frame refine: `frame ctx subj subjIb hencField ?_ sg` + discharge. -/
meta def mkNumFrame (cfg : Cfg) (frame hencField subj subjIb sg : Term) : MacroM (TSyntax `tactic) := do
  let d ← disch
  `(tactic|
    (refine $frame $(cfg.ctx) $subj $subjIb $hencField ?_ $sg
     apply Buffed.agreesOn_blit64
     $d:tactic))

/-- The op-header section: per-field products for op writers, one frame otherwise. -/
meta def mkOpBase (cfg : Cfg) : MacroM (TSyntax `tactic) := do
  if cfg.k == "op" then
    let cPrev ← mkClause cfg (← `(henc.prev)) "OperationMPtr" "Prev" ["OperationPtr.get!"] [← sd "OptionOperationPtr"]
    let cNext ← mkClause cfg (← `(henc.next)) "OperationMPtr" "Next" ["OperationPtr.get!"] [← sd "OptionOperationPtr"]
    let cParent ← mkClause cfg (← `(henc.parent)) "OperationMPtr" "Parent" ["OperationPtr.get!"] [← sd "OptionBlockPtr"]
    let cOpType ← mkClause cfg (← `(henc.opType)) "OperationMPtr" "OpType" ["OperationPtr.getOpType!"] []
    let cAttrs ← mkClause cfg (← `(henc.attrs)) "OperationMPtr" "Attrs" ["OperationPtr.get!"] [← wpParam cfg]
    `(tactic|
      (constructor
       · $cPrev:tactic
       · $cNext:tactic
       · $cParent:tactic
       · $cOpType:tactic
       · $cAttrs:tactic))
  else
    let sgOpGet ← mkSg cfg "OperationPtr.get!"
    let sgOpTy ← mkSg cfg "OperationPtr.getOpType!"
    let d ← disch
    `(tactic|
      (refine OperationPtr.matchesBase_frame $(cfg.ctx) op hopin henc.toMatchesBase ?_ hlay $sgOpGet $sgOpGet $sgOpGet $sgOpGet $sgOpTy opIb
       apply Buffed.agreesOn_blit64
       $d:tactic))

/-- The NthRegion section: always framed (header words + the array slot). -/
meta def mkNthRegion (cfg : Cfg) : MacroM (TSyntax `tactic) := do
  let sgOpRegion ← mkSg cfg "OperationPtr.getRegion!"
  let d ← disch
  let dU ← dischU
  `(tactic|
    (intros idx idxIn
     have hnr : idx < op.getNumRegions! ctx.spec := by grind
     have hcap := ctx.sim.repr.operations_indices op (by grind) |>.capRegions
     have hcnt := ctx.sim.repr.operations_indices op (by grind) |>.regions
     refine OperationPtr.nthRegion_frame $(cfg.ctx) op hopin idx hnr (henc.regions idx hnr) ?_ ?_ $sgOpRegion
     · apply Buffed.agreesOn_blit64
       $d:tactic
     · have hidxc : idx < (op.get! ctx.spec).capRegions := by grind
       have haddrR : (op.toM.toNat : Int) = op.id := by grind [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
       have hincl := OperationPtr.nthRegion_range_included_op_range $(cfg.ctx) op idx.toUInt64 (by grind) hopin
       apply Buffed.agreesOn_blit64
       $dU:tactic))

/-- The blockOperand slots: per-field products for bo-footprint writers, framed otherwise. -/
meta def mkBOslots (cfg : Cfg) : MacroM (TSyntax `tactic) := do
  if cfg.k == "bo" || cfg.k == "bopp" then
    let cBOnu ← mkClause cfg (← `(hmatch.nextUse)) "BlockOperandMPtr" "NextUse" ["BlockOperandPtr.get!"] [← sd "OptionBlockOperandPtr"]
      [← `(tactic| have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds))]
    let cBOback ← mkClause cfg (← `(hmatch.back)) "BlockOperandMPtr" "Back" ["BlockOperandPtr.get!"] [← sd "BlockOperandPtrPtr"]
      [← `(tactic| have htoM_b := BlockOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds)]
    let cBOowner ← mkClause cfg (← `(hmatch.owner)) "BlockOperandMPtr" "Owner" ["BlockOperandPtr.get!"] [← sd "OperationPtr"]
    let cBOvalue ← mkClause cfg (← `(hmatch.value)) "BlockOperandMPtr" "Value" ["BlockOperandPtr.get!"] [← sd "BlockPtr"]
    `(tactic|
      (intros bo boIb heq
       have hboIb : bo.InBounds ctx.spec := by grind
       have hmatch := ctx.sim.encoding_op op (by grind) |>.blockOperands bo hboIb heq
       have htoM := BlockOperandPtr.layoutPreserved_same_toM hlay hboIb
       have hfib := BlockOperandPtr.get_fieldsInBounds ctx.spec bo hFIB hboIb
       constructor
       · $cBOnu:tactic
       · $cBOback:tactic
       · $cBOowner:tactic
       · $cBOvalue:tactic))
  else
    let hd ← mkHdisjFor cfg "op" (← `(bo.op)) (← `(hpib))
    let sgBO ← mkSg cfg "BlockOperandPtr.get!"
    let d ← disch
    `(tactic|
      (intros bo boIb heq
       have hboIb : bo.InBounds ctx.spec := by grind
       have hincl := Sim.BlockOperandPtr.slot_included bo hboIb
       have hpib := Sim.BlockOperandPtr.op_inBounds hboIb
       have hprangeS := Sim.OperationPtr.range_linear bo.op hpib
       $hd:tactic
       refine BlockOperandPtr.matches_frame $(cfg.ctx) bo hboIb (henc.blockOperands bo hboIb heq) ?_ hlay $sgBO boIb
       apply Buffed.agreesOn_blit64
       $d:tactic))

/-- The operand slots: per-field products for oo-footprint writers, framed otherwise. -/
meta def mkOOslots (cfg : Cfg) : MacroM (TSyntax `tactic) := do
  if cfg.k == "oo" || cfg.k == "oopp" then
    let cOOnu ← mkClause cfg (← `(hmatch.nextUse)) "OpOperandMPtr" "NextUse" ["OpOperandPtr.get!"] [← sd "OptionOpOperandPtr"]
      [← `(tactic| have htoO := OpOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds))]
    let cOOback ← mkClause cfg (← `(hmatch.back)) "OpOperandMPtr" "Back" ["OpOperandPtr.get!"] [← sd "OpOperandPtrPtr"]
      [← `(tactic| have htoM_b := OpOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds)]
    let cOOowner ← mkClause cfg (← `(hmatch.owner)) "OpOperandMPtr" "Owner" ["OpOperandPtr.get!"] [← sd "OperationPtr"]
    let cOOvalue ← mkClause cfg (← `(hmatch.value)) "OpOperandMPtr" "Value" ["OpOperandPtr.get!"] [← sd "ValuePtr"]
      [← `(tactic| have htoM_v := ValuePtr.layoutPreserved_same_toM hlay hfib.value_inBounds)]
    `(tactic|
      (intros oper operIb heq
       have hooIb : oper.InBounds ctx.spec := by grind
       have hmatch := ctx.sim.encoding_op op (by grind) |>.operands oper hooIb heq
       have htoM := OpOperandPtr.layoutPreserved_same_toM hlay hooIb
       have hfib := OpOperandPtr.get_fieldsInBounds ctx.spec oper hFIB hooIb
       constructor
       · $cOOnu:tactic
       · $cOOback:tactic
       · $cOOowner:tactic
       · $cOOvalue:tactic))
  else
    let hd ← mkHdisjFor cfg "op" (← `(oper.op)) (← `(hpib))
    let sgOO ← mkSg cfg "OpOperandPtr.get!"
    let d ← disch
    `(tactic|
      (intros oper operIb heq
       have hooIb : oper.InBounds ctx.spec := by grind
       have hincl := Sim.OpOperandPtr.slot_included oper hooIb
       have hpib := Sim.OpOperandPtr.op_inBounds hooIb
       have hprangeS := Sim.OperationPtr.range_linear oper.op hpib
       $hd:tactic
       refine OpOperandPtr.matches_frame $(cfg.ctx) oper hooIb (henc.operands oper hooIb heq) ?_ hlay $sgOO operIb
       apply Buffed.agreesOn_blit64
       $d:tactic))

/-- The result slots: per-field products for rs-footprint writers, framed otherwise. -/
meta def mkRSslots (cfg : Cfg) : MacroM (TSyntax `tactic) := do
  if cfg.k == "rs" || cfg.k == "vi" || cfg.k == "oopp" then
    let cRSkind ← mkClause cfg (← `(hmatch.kind)) "OpResultMPtr" "Kind" ["OpResultPtr.get!"] []
    let cRStype ← mkClause cfg (← `(hmatch.typee)) "OpResultMPtr" "Type" ["OpResultPtr.get!"] [← wpParam cfg]
    let cRSfu ← mkClause cfg (← `(hmatch.firstUse)) "OpResultMPtr" "FirstUse" ["OpResultPtr.get!"] [← sd "OptionOpOperandPtr"]
      [← `(tactic| have htoO := OpOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds))]
    let cRSidx ← mkClause cfg (← `(hmatch.index)) "OpResultMPtr" "Index" ["OpResultPtr.get!"] []
    let cRSowner ← mkClause cfg (← `(hmatch.owner)) "OpResultMPtr" "Owner" ["OpResultPtr.get!"] [← sd "OperationPtr"]
    `(tactic|
      (intros res resIb heq
       have hresIb : res.InBounds ctx.spec := by grind
       have hmatch := ctx.sim.encoding_op op (by grind) |>.results res hresIb heq
       have htoM := OpResultPtr.layoutPreserved_same_toM hlay hresIb
       have hfib := OpResultPtr.get_fieldsInBounds ctx.spec res hFIB hresIb
       constructor
       · $cRSkind:tactic
       · $cRStype:tactic
       · $cRSfu:tactic
       · $cRSidx:tactic
       · $cRSowner:tactic))
  else
    let hd ← mkHdisjFor cfg "op" (← `(res.op)) (← `(hpib))
    let sgRS ← mkSg cfg "OpResultPtr.get!"
    let d ← disch
    `(tactic|
      (intros res resIb heq
       have hresIb : res.InBounds ctx.spec := by grind
       have hincl := Sim.OpResultPtr.slot_included res hresIb
       have hpib := Sim.OpResultPtr.op_inBounds hresIb
       have hprangeS := Sim.OperationPtr.range_linear res.op hpib
       $hd:tactic
       refine OpResultPtr.matches_frame $(cfg.ctx) res hresIb (henc.results res hresIb heq) ?_ hlay $sgRS resIb
       apply Buffed.agreesOn_blit64
       $d:tactic))

/-- The block-argument slots: per-field products for ba-footprint writers, framed otherwise. -/
meta def mkBAslots (cfg : Cfg) : MacroM (TSyntax `tactic) := do
  if cfg.k == "ba" || cfg.k == "vi" || cfg.k == "oopp" then
    let cBAkind ← mkClause cfg (← `(hmatch.kind)) "BlockArgumentMPtr" "Kind" ["BlockArgumentPtr.get!"] []
    let cBAtype ← mkClause cfg (← `(hmatch.type)) "BlockArgumentMPtr" "Type" ["BlockArgumentPtr.get!"] [← wpParam cfg]
    let cBAfu ← mkClause cfg (← `(hmatch.firstUse)) "BlockArgumentMPtr" "FirstUse" ["BlockArgumentPtr.get!"] [← sd "OptionOpOperandPtr"]
      [← `(tactic| have htoO := OpOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds))]
    let cBAidx ← mkClause cfg (← `(hmatch.index)) "BlockArgumentMPtr" "Index" ["BlockArgumentPtr.get!"] []
    let cBAowner ← mkClause cfg (← `(hmatch.owner)) "BlockArgumentMPtr" "Owner" ["BlockArgumentPtr.get!"] [← sd "BlockPtr"]
    `(tactic|
      (intros arg argIn heq
       have hargIb : arg.InBounds ctx.spec := by grind
       have hmatch := henc.arguments arg hargIb heq
       have hfib := BlockArgumentPtr.get_fieldsInBounds ctx.spec arg hFIB hargIb
       constructor
       · $cBAkind:tactic
       · $cBAtype:tactic
       · $cBAfu:tactic
       · $cBAidx:tactic
       · $cBAowner:tactic))
  else
    let hd ← mkHdisjFor cfg "block" (← `(arg.block)) (← `(hpib))
    let sgBA ← mkSg cfg "BlockArgumentPtr.get!"
    let d ← disch
    `(tactic|
      (intros arg argIn heq
       have hargIb : arg.InBounds ctx.spec := by grind
       have hincl := Sim.BlockArgumentPtr.slot_included arg hargIb
       have hpib := Sim.BlockArgumentPtr.block_inBounds hargIb
       have hprangeS := Sim.BlockPtr.range_linear arg.block hpib
       $hd:tactic
       refine BlockArgumentPtr.matches_frame $(cfg.ctx) arg hargIb (henc.arguments arg hargIb heq) ?_ hlay $sgBA argIn
       apply Buffed.agreesOn_blit64
       $d:tactic))

/-- The block-header section: per-field products for block writers, one frame otherwise. -/
meta def mkBlBase (cfg : Cfg) : MacroM (TSyntax `tactic) := do
  if cfg.k == "bl" || cfg.k == "bopp" then
    let cBLfu ← mkClause cfg (← `(henc.firstUse)) "BlockMPtr" "FirstUse" ["BlockPtr.get!"] [← sd "OptionBlockOperandPtr"]
      [← `(tactic| have hfibB := BlockPtr.get_fieldsInBounds ctx.spec blk hFIB hblin),
       ← `(tactic| have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfibB.firstUse_inBounds))]
    let cBLprev ← mkClause cfg (← `(henc.prev)) "BlockMPtr" "Prev" ["BlockPtr.get!"] [← sd "OptionBlockPtr"]
    let cBLnext ← mkClause cfg (← `(henc.next)) "BlockMPtr" "Next" ["BlockPtr.get!"] [← sd "OptionBlockPtr"]
    let cBLparent ← mkClause cfg (← `(henc.parent)) "BlockMPtr" "Parent" ["BlockPtr.get!"] [← sd "OptionRegionPtr"]
    let cBLfop ← mkClause cfg (← `(henc.firstOp)) "BlockMPtr" "FirstOp" ["BlockPtr.get!"] [← sd "OptionOperationPtr"]
    let cBLlop ← mkClause cfg (← `(henc.lastOp)) "BlockMPtr" "LastOp" ["BlockPtr.get!"] [← sd "OptionOperationPtr"]
    `(tactic|
      (constructor
       · $cBLfu:tactic
       · $cBLprev:tactic
       · $cBLnext:tactic
       · $cBLparent:tactic
       · $cBLfop:tactic
       · $cBLlop:tactic))
  else
    let sgBL ← mkSg cfg "BlockPtr.get!"
    let d ← disch
    `(tactic|
      (refine BlockPtr.matchesBase_frame $(cfg.ctx) blk hblin henc.toMatchesBase ?_ hlay $sgBL $sgBL $sgBL $sgBL $sgBL $sgBL blkIb
       apply Buffed.agreesOn_blit64
       $d:tactic))

/-- The region section: per-field products for region writers, one frame otherwise. -/
meta def mkRegionSec (cfg : Cfg) : MacroM (TSyntax `tactic) := do
  if cfg.k == "rg" then
    let cRGfb ← mkClause cfg (← `(henc.firstBlock)) "RegionMPtr" "FirstBlock" ["RegionPtr.get!"] [← sd "OptionBlockPtr"]
    let cRGlb ← mkClause cfg (← `(henc.lastBlock)) "RegionMPtr" "LastBlock" ["RegionPtr.get!"] [← sd "OptionBlockPtr"]
    let cRGparent ← mkClause cfg (← `(henc.parent)) "RegionMPtr" "Parent" ["RegionPtr.get!"] [← sd "OptionOperationPtr"]
    `(tactic|
      (constructor
       · $cRGfb:tactic
       · $cRGlb:tactic
       · $cRGparent:tactic))
  else
    let hd ← mkHdisjFor cfg "region" (← `(rg)) (← `(hrgin))
    let sgRG ← mkSg cfg "RegionPtr.get!"
    let d ← disch
    `(tactic|
      ($hd:tactic
       refine RegionPtr.matches_frame $(cfg.ctx) rg hrgin henc ?_ hlay $sgRG rgIb
       apply Buffed.agreesOn_blit64
       $d:tactic))

/-- The full `Sim` constructor skeleton, with the per-section tactics spliced in. -/
meta def mkMain (cfg : Cfg) (spec : Term) (wAttr : TSyntax ``Parser.Tactic.grindParam)
    (hsimv whaves hdisjOp hdisjBl tOpBase tNumBO tBOslots tNumRG tNthRegion tNumOO tOOslots
     tNumRS tRSslots tBlBase tNumArgs tBAslots tRegion : TSyntax `tactic) :
    MacroM (TSyntax `tactic) := do
  let ctx := cfg.ctx
  `(tactic|
    (have hFIB : ($ctx).spec.FieldsInBounds := Veir.Sim.IRContext.fieldsInBounds $ctx
     have hlay : ($ctx).spec.LayoutPreserved $spec :=
       IRContext.LayoutPreserved.of_layoutUnchanged_ltr (by grind)
     $hsimv:tactic
     $whaves:tactic
     constructor
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
       have hopin : op.InBounds ($ctx).spec := by grind
       have henc := ($ctx).sim.encoding_op op hopin
       have hprange := Sim.OperationPtr.range_linear op hopin
       $hdisjOp:tactic
       constructor
       · $tOpBase:tactic
       · constructor
         · $tNumBO:tactic
         · $tBOslots:tactic
       · constructor
         · $tNumRG:tactic
         · $tNthRegion:tactic
       · constructor
         · $tNumOO:tactic
         · $tOOslots:tactic
       · constructor
         · $tNumRS:tactic
         · $tRSslots:tactic
     · simp only
       intros blk blkIb
       have hblin : blk.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_block blk hblin
       have hbrange := Sim.BlockPtr.range_linear blk hblin
       $hdisjBl:tactic
       constructor
       · $tBlBase:tactic
       · constructor
         · $tNumArgs:tactic
         · $tBAslots:tactic
     · simp only
       intros rg rgIb
       have hrgin : rg.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_region rg hrgin
       have hrrange := Sim.RegionPtr.range_linear rg hrgin
       $tRegion:tactic
     · have := ($ctx).sim.attr_empty
       grind only [$wAttr:grindParam]))

end ProveSetLinkSim

open Lean ProveSetLinkSim in
set_option hygiene false in
/-- Shared `Sim` proof for the single-word link setters: the sections matching the writer's
own structure kind(s) keep per-field product-lemma clauses (the write lands inside their
footprint), and every other `Matches` section is transported by one `Frames.lean` lemma plus
a single interval-disjointness `grind`. `wkind` names the writer's structure kind: `op`,
`oo`, `bo`, `rs`, `ba`, `bl`, `rg`, or the sum-typed `vi` (`ValuePtr`), `oopp`
(`OpOperandPtrPtr`) and `bopp` (`BlockOperandPtrPtr`), whose case analysis is packaged in
the `Frames.lean` disjointness lemmas. -/
macro "prove_setLinkSim" ctx:ident wkind:ident w:ident wsfx:ident ssfx:ident spec:term:max vib:(ident)? : tactic => do
  let k := wkind.getId.toString
  -- writer parent pointer, its `InBounds` proof, and the parent's kind (op/block/region)
  let (wparent, wparentIb, wpk) ← match k with
    | "op" => do pure ((← `(ptr.spec)), (← `(ib.ib)), "op")
    | "oo" | "bo" | "rs" => do pure ((← `(ptr.spec.op)), (← `(hwpib)), "op")
    | "ba" => do pure ((← `(ptr.spec.block)), (← `(hwpib)), "block")
    | "bl" => do pure ((← `(ptr.spec)), (← `(ib.ib)), "block")
    | "rg" => do pure ((← `(ptr.spec)), (← `(ib.ib)), "region")
    | "vi" | "oopp" | "bopp" => do pure ((← `(ptr.spec)), (← `(ib.ib)), k)
    | _ => Macro.throwError s!"prove_setLinkSim: unknown writer kind '{k}'"
  let cfg : Cfg := {
    ctx, w, k
    wsfxS := wsfx.getId.toString
    ssfxS := ssfx.getId.toString
    isSum := k == "vi" || k == "oopp" || k == "bopp"
    wparent, wparentIb, wpk
  }
  let whaves ← mkWhaves cfg
  let hsimv ← mkHsimv vib
  let tOpBase ← mkOpBase cfg
  let tNumBO ← mkNumFrame cfg (← `(OperationPtr.numBlockOperands_frame)) (← `(henc.numBlockOperands))
    (← `(op)) (← `(hopin)) (← mkSg cfg "OperationPtr.get!")
  let tNumRG ← mkNumFrame cfg (← `(OperationPtr.numRegions_frame)) (← `(henc.numRegions))
    (← `(op)) (← `(hopin)) (← mkSg cfg "OperationPtr.get!")
  let tNumOO ← mkNumFrame cfg (← `(OperationPtr.numOperands_frame)) (← `(henc.numOperands))
    (← `(op)) (← `(hopin)) (← mkSg cfg "OperationPtr.get!")
  let tNumRS ← mkNumFrame cfg (← `(OperationPtr.numResults_frame)) (← `(henc.numResults))
    (← `(op)) (← `(hopin)) (← mkSg cfg "OperationPtr.get!")
  let tNumArgs ← mkNumFrame cfg (← `(BlockPtr.numArguments_frame)) (← `(henc.numArguments))
    (← `(blk)) (← `(hblin)) (← mkSg cfg "BlockPtr.get!")
  let tNthRegion ← mkNthRegion cfg
  let tBOslots ← mkBOslots cfg
  let tOOslots ← mkOOslots cfg
  let tRSslots ← mkRSslots cfg
  let tBAslots ← mkBAslots cfg
  let tBlBase ← mkBlBase cfg
  let tRegion ← mkRegionSec cfg
  let hdisjOp ← mkHdisjFor cfg "op" (← `(op)) (← `(hopin))
  let hdisjBl ← mkHdisjFor cfg "block" (← `(blk)) (← `(hblin))
  let wAttr ← gp (⟨w.raw⟩ : Term)
  mkMain cfg spec wAttr hsimv whaves hdisjOp hdisjBl tOpBase tNumBO tBOslots tNumRG tNthRegion
    tNumOO tOOslots tNumRS tRSslots tBlBase tNumArgs tBAslots tRegion

end Veir
