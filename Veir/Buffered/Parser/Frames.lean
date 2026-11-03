module

public import Veir.Buffered.Parser.AllocationFrames
public import Veir.Buffered.Rewriter.WellFormed.BlockUse
public import Veir.Buffered.Rewriter.WellFormed.CreateOp
public import Veir.Buffered.Rewriter.WellFormed.CreateBlock
import all Veir.Buffered.Rewriter.Basic
import all Veir.Buffered.IR.Buffed.Basic
import all Veir.Buffered.IR.Buffed.ContainerDealloc

/-!
Static liveness frames for parser transactions. These propositions transport existing
handles; they do not search an allocation table or inspect addresses at runtime.
-/
public section
namespace Veir.Buffered

set_option maxHeartbeats 1000000

/-- Allocation preserves *simulated* references, including context-dependent SSA addresses,
not just the bounds of their specification pointers. -/
theorem Rewriter.createOp_sim_inBounds_mono {ctx next : Parser.IR.RawContext}
    {opType types operands successors regions props ip h₁ h₂ h₃ h₄ h₅ h₆ p}
    (hc : createOp ctx opType types operands successors regions props ip h₁ h₂ h₃ h₄ h₅ h₆ = some (next, p))
    (q : Sim.GenericPtr) (hq : q.InBounds ctx) : q.InBounds next := by
  simp only [createOp.unfold] at hc
  split at hc
  · contradiction
  · split at hc
    · grind
    · rename_i op allocated halloc
      split at hc
      · grind
      · have ha := Sim.OperationPtr.allocRecycled_genericPtr_mono q halloc hq
        split at hc
        · contradiction
        · rename_i withRegions hregions
          have hr := Rewriter.initOpRegions_inBounds_mono q
            (Rewriter.initOpResults_inBounds_mono q rfl ha) hregions
          split at hc
          · simp only [Option.bind_eq_bind, Option.bind] at hc
            split at hc
            · contradiction
            · rename_i final hinsert
              obtain ⟨rfl, rfl⟩ := Option.some.inj hc
              apply (Rewriter.insertOp?_inBounds_mono q hinsert).mpr
              exact Rewriter.initBlockOperands_inBounds_mono' q
                (Rewriter.initOpOperands_inBounds_mono' q hr)
          · obtain ⟨rfl, rfl⟩ := Option.some.inj hc
            exact Rewriter.initBlockOperands_inBounds_mono' q
              (Rewriter.initOpOperands_inBounds_mono' q hr)

/-- A local value survives deletion of a different operation, regardless of where the
local is stored (an SSA table, an operand array, or a caller's stack frame). -/
private theorem dealloc_value {ctx : Parser.IR.RawContext} {op : Sim.OperationPtr} {v : Sim.ValuePtr}
    {hi hd} (hv : v.InBounds ctx)
    (hne : ∀ res, v.spec = .opResult res → res.op ≠ op.spec) :
    v.InBounds (op.dealloc ctx hi hd) := by
  have hib : v.spec.InBounds (op.spec.dealloc ctx.spec hi.ib) := by
    cases hs : v.spec with
    | opResult res =>
      have hn := hne res hs
      grind [ValuePtr.InBounds]
    | blockArgument arg => grind [ValuePtr.InBounds]
  have hlay := IRContext.layoutPreserved_OperationPtr_dealloc op.spec hi.ib
  have heq := ValuePtr.layoutPreserved_same_toM hlay hib
  constructor
  · simp only [Sim.OperationPtr.dealloc.unfold, Sim.OperationPtr.forget.unfold, Sim.IRContext.releaseRange.unfold,
      Sim.ValuePtr.Sim_def, Sim.IRContext.inner, Sim.RawIRContext.spec, Erased.out_mk]
    change v.spec.toM (op.spec.dealloc ctx.spec hi.ib) = v.impl
    rw [← heq]
    exact hv.sim.out
  · simpa only [Sim.OperationPtr.dealloc.unfold, Sim.OperationPtr.forget.unfold, Sim.IRContext.releaseRange.unfold,
      Sim.IRContext.spec, Erased.out_mk] using hib

theorem Rewriter.eraseOp_value_inBounds {ctx : Parser.IR.RawContext} {op : Sim.OperationPtr} {v : Sim.ValuePtr}
    {hc hi ho hs hd} (hv : v.InBounds ctx)
    (hne : ∀ res, v.spec = .opResult res → res.op ≠ op.spec) :
    v.InBounds (eraseOp ctx op hc hi ho hs hd) := by
  simp only [eraseOp.unfold]
  apply dealloc_value (hne := hne)
  grind [generic_ptr_grind]

theorem Rewriter.createOp_numResults {ctx next : Parser.IR.RawContext}
    {opType types operands successors regions props ip h₁ h₂ h₃ h₄ h₅ h₆ p}
    (wf : ctx.spec.WellFormed)
    (hc : createOp ctx opType types operands successors regions props ip h₁ h₂ h₃ h₄ h₅ h₆ = some (next, p)) :
    p.spec.getNumResults! next.spec = types.size := by
  have hib := Rewriter.createOp_new_inBounds p hc
  have hcap := (Rewriter.createOp_preserves_wellFormed wf hc).operations p.spec hib.ib
    |>.capResults_eq_numResults
  simp only [createOp.unfold] at hc
  split at hc
  · contradiction
  · split at hc
    · contradiction
    · rename_i allocated allocatedCtx halloc
      split at hc
      · contradiction
      · split at hc
        · contradiction
        · rename_i regionsCtx hregions
          have hr : (allocated.spec.get! regionsCtx.spec).capResults = types.size := by
            rw [Rewriter.initOpRegions_preserves_capResults _ hregions,
              Rewriter.initOpResults_preserves_capResults _ (heq := rfl)]
            have hs := Sim.OperationPtr.allocRecycled_spec' halloc
            clear hc hcap hib wf hregions
            grind [Operation.empty, Array.sizeU64_toNat]
          split at hc
          · simp only [Option.bind_eq_bind, Option.bind] at hc
            split at hc
            · contradiction
            · rename_i inserted hinsert
              obtain ⟨rfl, rfl⟩ := Option.some.inj hc
              rw [← hcap, (Rewriter.insertOp?_layoutUnchanged hinsert).preserves.ops _ hib.ib |>.numResults,
                Rewriter.initBlockOperands_preserves_capResults,
                Rewriter.initOpOperands_preserves_capResults _ (heq := rfl)]
              exact hr
          · obtain ⟨rfl, rfl⟩ := Option.some.inj hc
            rw [← hcap, Rewriter.initBlockOperands_preserves_capResults,
              Rewriter.initOpOperands_preserves_capResults _ (heq := rfl)]
            exact hr

theorem Rewriter.createBlock_new_not_inBounds {ctx next : Parser.IR.RawContext} {types ip hip hrep p}
    (hc : createBlock ctx types ip hip hrep = some (next, p)) : ¬ p.spec.InBounds ctx.spec := by
  simp only [createBlock.unfold] at hc
  split at hc
  · split at hc
    · grind
    · simp at hc
      split at hc
      · grind
      · split at hc
        · simp [Option.bind] at hc
          split at hc <;> grind
        · grind
  · grind

theorem Rewriter.createBlock_numArguments {ctx next : Parser.IR.RawContext} {types ip hip hrep p}
    (_wf : ctx.spec.WellFormed)
    (hc : createBlock ctx types ip hip hrep = some (next, p)) :
    p.spec.getNumArguments! next.spec = types.size := by
  simp only [createBlock.unfold] at hc
  split at hc
  · split at hc
    · contradiction
    · simp only [Option.bind_eq_bind, Option.bind] at hc
      split at hc
      · contradiction
      · rename_i initialized hargs
        have hn := Rewriter.initBlockArguments_numArguments hargs (by simp)
        split at hc
        · split at hc
          · contradiction
          · rename_i inserted hinsert
            obtain ⟨rfl, rfl⟩ := Option.some.inj hc
            simp only [insertBlock?.unfold] at hinsert
            grind
        · obtain ⟨rfl, rfl⟩ := Option.some.inj hc
          exact hn
  · contradiction

/-- Deleting an argument-free placeholder block cannot invalidate any SSA value. -/
theorem Rewriter.eraseBlock_value_inBounds {ctx : Parser.IR.RawContext} {block : Sim.BlockPtr}
    {v : Sim.ValuePtr} {hi hp hd} (hv : v.InBounds ctx)
    (empty : block.spec.getNumArguments! ctx.spec = 0) :
    v.InBounds (eraseBlock ctx block hi hp hd) := by
  have hib : v.spec.InBounds (block.spec.dealloc ctx.spec) := by
    have hvib := hv.ib
    cases hs : v.spec with
    | opResult res => grind [ValuePtr.InBounds]
    | blockArgument arg =>
      have harg : arg.InBounds ctx.spec := by simpa only [hs, ValuePtr.inBounds_blockArg] using hvib
      have hn : arg.block ≠ block.spec := by grind [BlockArgumentPtr.inBounds_def]
      grind [ValuePtr.InBounds]
  have hl := IRContext.layoutPreserved_BlockPtr_dealloc block.spec hi.ib
  have heq := ValuePtr.layoutPreserved_same_toM hl hib
  constructor
  · simp only [eraseBlock.unfold, Sim.BlockPtr.dealloc.unfold, Sim.BlockPtr.forget.unfold, Sim.IRContext.releaseRange.unfold,
      Sim.ValuePtr.Sim_def, Sim.IRContext.inner, Sim.RawIRContext.spec, Erased.map_out, Erased.out_mk]
    change v.spec.toM (block.spec.dealloc ctx.spec) = v.impl
    rw [← heq]
    exact hv.sim.out
  · rwa [eraseBlock_spec]

end Veir.Buffered
