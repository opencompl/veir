module

public import Veir.Passes.Legalization.Validity.PhiWidening
public import Veir.Passes.KeptValuesSimulation
public import Veir.Verifier
import all Veir.IR.Basic
import all Veir.Passes.Legalization.Validity.PhiWidening
import all Veir.Passes.Legalization.Validity.PhiFrame
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interfaces.FunctionInterfaces
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Func.OpInfo
import all Veir.GlobalOpInfo

public section
namespace Veir.Legalization.CTreeProofs

/-- Entry blocks have no incoming branch operands. -/
def PhiEntries (ctx : WfIRContext OpCode) : Prop :=
  ∀ {region : RegionPtr} {b : BlockPtr}, region.InBounds ctx.raw →
    region.getFirstBlock! ctx.raw = some b → b.hasPredecessor! ctx.raw = false

theorem PhiEntries.of_verified {ctx : WfIRContext OpCode} {moduleOp : OperationPtr}
    (verified : ctx.Verified moduleOp) : PhiEntries ctx := by
  intro r b rIn first
  exact verified.entryBlock_hasNoPredecessor (by grind)
    (RegionPtr.parent_of_firstBlock rIn first) first

namespace PhiWidening
open _root_.CTree Veir.CTree
variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
    (W : PhiWidening src dst block args)

/-- Block execution either returns refined results or reaches another related block call. -/
def BlockStepsSim : Prop :=
  ∀ b (bIn : b.InBounds src.raw) vs s b' (bIn' : b'.InBounds dst.raw) vs' s',
    W.CallRel b vs s b' vs' s' →
    Sim (Sum.LiftRel (EntryRel W.CallRel) (fun t s => KeptValues.ResultRel s t))
      (blockStep (CFGState.entry bIn' vs' s')) (blockStep (CFGState.entry bIn vs s))

/-- The entry to a function uses ordinary argument refinement since it has no predecessors. -/
private theorem entryCall (entries : PhiEntries src)
    (phi : block.hasPredecessor! src.raw = true) {region : RegionPtr}
    (regionIn : region.InBounds src.raw) {b : BlockPtr} (first : region.getFirstBlock! src.raw = some b)
    {vs vs' : Array RuntimeValue} (refines : vs ⊒ vs') (mem : MemoryState) :
    W.CallRel b vs ⟨VariableState.empty src, mem⟩ b vs' ⟨VariableState.empty dst, mem⟩ := by
  have noPred := entries regionIn first
  have different : b ≠ block := by rintro rfl; simp [phi] at noPred
  refine ⟨rfl, ⟨MemoryState.isRefinedBy_refl _, ?_⟩, refines.1, ?_⟩
  · intro v h v' hv
    simp [VariableState.empty, VariableState.getVar?] at hv
  · intro i hi
    have absent : b.getArgument i ∉ selectedArgs block args.reverse := by
      simp [selectedArgs, BlockPtr.getArgument_def, Ne.symm different]
    simpa [ArgumentRel, absent] using refines.2 i hi

private theorem func_refines (steps : W.BlockStepsSim) (entries : PhiEntries src) (phi : block.hasPredecessor! src.raw = true)
    {func : OperationPtr} (hin : func.InBounds src.raw) (hFunc : func.getOpType! src.raw = .func .func) :
    func.isRefinedByAsFunctionCTree src func dst hin (W.opHeader hin).inBounds := by
  have hSame := W.opHeader hin
  have hFunc' : func.getOpType! dst.raw = .func .func := hSame.code.trans hFunc
  have f : FunctionOp src.raw func := .of func src.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc]; rfl)
  have f' : FunctionOp dst.raw func := .of func dst.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc']; rfl)
  rw [OperationPtr.isRefinedByAsFunctionCTree, FunctionOp.of?_eq_some f, FunctionOp.of?_eq_some f']
  intro vs vs' mem hValues
  have num := hSame.numRegions
  rw [OperationPtr.getNumRegions!_eq_getNumRegions hin,
      OperationPtr.getNumRegions!_eq_getNumRegions hSame.inBounds] at num
  simp only [CTree.interpretFunction, FunctionOp.of?_eq_some f, FunctionOp.of?_eq_some f', num]
  split
  · exact sim_fail _ _
  next hRegions =>
    have nonempty : 0 < func.getNumRegions src.raw hin := by omega
    have regionIn : (f.getFunctionBody hin nonempty).InBounds src.raw := by
      have := src.wellFormed.inBounds
      simp only [FunctionOp.getFunctionBody]
      grind
    have body : f'.getFunctionBody hSame.inBounds (by omega) = f.getFunctionBody hin nonempty := by
      have := hSame.region 0
      simp only [FunctionOp.getFunctionBody]
      grind
    rw [tree_bind_eq, tree_bind_eq]
    refine Sim.bind (RR := fun t s => KeptValues.ResultRel s t) _ _ _ _ ?_
      (fun _ _ h => (Sim.pure _ _ _).mpr h.2)
    rw [interpretRegion_eq_inflateCFGTree, interpretRegion_eq_inflateCFGTree]
    apply sim_inflate
    simp only [interpretCFGTree]
    have first := W.ctxSame.firstBlock regionIn
    split
    · next b' hb' =>
      split
      · next b hb =>
        obtain rfl : b' = b := by grind
        exact iter_cfgStep_sim (Rel := W.CallRel) steps _ _
          (W.entryCall entries phi regionIn (by grind) hValues mem)
      · exact sim_fail _ _
    · split
      · exfalso; grind
      · exact sim_fail _ _

/-- Simulation of each block step lifts to CTree refinement of every named top-level function. -/
theorem isModuleRefinedByCTree_of_entries (steps : W.BlockStepsSim) {moduleOp : OperationPtr}
    (entries : PhiEntries src) (phi : block.hasPredecessor! src.raw = true) :
    moduleOp.isModuleRefinedByCTree src moduleOp dst := by
  intro func hin name hTop
  have hdr := W.opHeader hin
  refine ⟨func, hdr.inBounds, ⟨hdr.code.trans hTop.isFunc, ?_, ?_⟩,
    W.func_refines steps entries phi hin hTop.isFunc⟩
  · rw [hdr.properties]; exact hTop.hasName
  · have hFields := src.wellFormed.inBounds
    have parent : func.getParentOp! dst.raw = func.getParentOp! src.raw := by
      simp only [OperationPtr.getParentOp!, OperationPtr.getParentRegion!, hdr.parent, Bind.bind, Option.bind]
      cases hp : func.getParent! src.raw with
      | none => rfl
      | some b =>
        dsimp only
        rw [W.ctxSame.blockParent (show b.InBounds src.raw by grind)]
        cases hr : b.getParent! src.raw with
        | none => rfl
        | some r => exact W.ctxSame.regionParent (by grind)
    exact parent.trans hTop.isTopLevel

end PhiWidening
end Veir.Legalization.CTreeProofs
