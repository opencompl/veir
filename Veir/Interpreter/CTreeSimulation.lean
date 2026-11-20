module

public import Veir.Interpreter.CTreeInterpreter
public import CTree.IterSim
public import Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.CTreeInterpreter
import all CTree.Interp
import all CTree.Defs

public section

namespace Veir.CTree

/-- Lift a simulation of reachable CFG steps to a simulation of the complete loop.
The two sets of locations and states may differ. The event family must be shared;
region callbacks must therefore already have a common representation. -/
theorem sim_cfgLoop
    {I J X Y : Type} (reachable : I → J → Prop) (results : X → Y → Prop)
    (target : I → Tree (I ⊕ X)) (source : J → Tree (J ⊕ Y))
    {i : I} {j : J} (initial : reachable i j)
    (step : ∀ i j, reachable i j →
      _root_.CTree.Sim (Sum.LiftRel reachable results) (target i) (source j)) :
    _root_.CTree.Sim results (_root_.CTree.iter target i) (_root_.CTree.iter source j) :=
  _root_.CTree.Sim.iter target source i j initial step

/-- Common-effect specialization of the generic finite iteration helper. -/
abbrev cfgSteps {I X : Type} (step : I → Tree (I ⊕ X)) :=
  _root_.CTree.iterSteps step

@[simp]
theorem cfgSteps_one {I X : Type} (step : I → Tree (I ⊕ X)) (i : I) :
    cfgSteps step 1 i = step i :=
  _root_.CTree.iterSteps_one step i

/-- Synchronized local simulations compose over any finite batch of CFG steps. -/
theorem sim_cfgSteps {I J X Y : Type}
    (reachable : I → J → Prop) (results : X → Y → Prop)
    (target : I → Tree (I ⊕ X)) (source : J → Tree (J ⊕ Y))
    (step : ∀ i j, reachable i j →
      _root_.CTree.Sim (Sum.LiftRel reachable results) (target i) (source j))
    (n : Nat) {i : I} {j : J} (initial : reachable i j) :
    _root_.CTree.Sim (Sum.LiftRel reachable results)
      (cfgSteps target n i) (cfgSteps source n j) :=
  _root_.CTree.Sim.iterSteps reachable results target source step n initial

/-- Common-effect specialization of the generic finite-batch invariant. -/
abbrev BatchedCFGSimulation {I J X Y : Type}
    (target : I → Tree (I ⊕ X)) (source : J → Tree (J ⊕ Y))
    (reachable : I → J → Prop) (results : X → Y → Prop) :=
  _root_.CTree.IterBatchedSimulation target source reachable results

/-- Unit batches recover the synchronized reachable-step invariant. -/
def BatchedCFGSimulation.of_step {I J X Y : Type}
    {target : I → Tree (I ⊕ X)} {source : J → Tree (J ⊕ Y)}
    {reachable : I → J → Prop} {results : X → Y → Prop}
    (step : ∀ i j, reachable i j →
      _root_.CTree.Sim (Sum.LiftRel reachable results) (target i) (source j)) :
    BatchedCFGSimulation target source reachable results :=
  _root_.CTree.IterBatchedSimulation.of_step step

/-- Local CFG-step simulations lift while retaining unresolved region callbacks.
The relation need only hold at reachable pairs of locations and states. -/
theorem sim_interpretCFG_loop {ctx : WfIRContext OpCode}
    (reachable : (interpretCFG.StateLocation ctx × InterpreterState ctx) →
      (interpretCFG.StateLocation ctx × InterpreterState ctx) → Prop)
    (results : (InterpreterState ctx × Array RuntimeValue) →
      (InterpreterState ctx × Array RuntimeValue) → Prop)
    {i j : interpretCFG.StateLocation ctx × InterpreterState ctx}
    (initial : reachable i j)
    (step : ∀ i j, reachable i j → _root_.CTree.Sim
      (Sum.LiftRel reachable results)
      (interpretCFG.iter i.1 i.2) (interpretCFG.iter j.1 j.2)) :
    _root_.CTree.Sim results
      (_root_.CTree.iter (fun p => interpretCFG.iter p.1 p.2) i)
      (_root_.CTree.iter (fun p => interpretCFG.iter p.1 p.2) j) :=
  _root_.CTree.Sim.iter _ _ i j initial step

/-- Start the reachable-step argument at a region's entry block. -/
theorem sim_interpretCFG {ctx : WfIRContext OpCode}
    (region : RegionPtr) (regionIn : region.InBounds ctx.raw)
    (targetValues sourceValues : Array RuntimeValue)
    (targetState sourceState : InterpreterState ctx)
    (reachable : (interpretCFG.StateLocation ctx × InterpreterState ctx) →
      (interpretCFG.StateLocation ctx × InterpreterState ctx) → Prop)
    (results : (InterpreterState ctx × Array RuntimeValue) →
      (InterpreterState ctx × Array RuntimeValue) → Prop)
    (initial : ∀ (bb : BlockPtr) (bbIn : bb.InBounds ctx.raw),
      region.getFirstBlock ctx.raw = some bb →
      reachable (.inl (⟨bb, bbIn⟩, targetValues), targetState)
        (.inl (⟨bb, bbIn⟩, sourceValues), sourceState))
    (step : ∀ i j, reachable i j → _root_.CTree.Sim
      (Sum.LiftRel reachable results)
      (interpretCFG.iter i.1 i.2) (interpretCFG.iter j.1 j.2)) :
    _root_.CTree.Sim results
      (interpretCFG region targetValues targetState regionIn)
      (interpretCFG region sourceValues sourceState regionIn) := by
  unfold interpretCFG
  split
  next bb entry =>
    apply sim_interpretCFG_loop reachable results
    · exact initial bb (by grind) entry
    · exact step
  next missing => exact sim_fail _ _

/-- A single unfolding of recursive region handling. Its output effects are shared
across contexts even though the unresolved region-effect families differ. -/
def regionRecStep {ctx : WfIRContext OpCode} {X : Type}
    (t : RegionTree ctx (InterpreterState ctx) X) :
    Tree (RegionTree ctx (InterpreterState ctx) X ⊕ X) :=
  match t.unfold with
  | .ret r => return .inr r
  | .tau i k => _root_.CTree.CTree.tauG i (fun x => return .inl (k x))
  | .vis (.inl i) k => pure (.inl
      ((fun ⟨region, values, state, inBounds⟩ =>
        interpretCFG region values state inBounds) i >>= k))
  | .vis (.inr i) k => _root_.CTree.CTree.vis i (fun x => return .inl (k x))

/-- Cross-context recursive interpretation follows from a relation closed under
one unfolding of region handling. This supports different callback event types;
no equality or cast between contexts is required. -/
theorem sim_interpretRegion
    {targetCtx sourceCtx : WfIRContext OpCode}
    (targetRegion sourceRegion : RegionPtr)
    (targetIn : targetRegion.InBounds targetCtx.raw)
    (sourceIn : sourceRegion.InBounds sourceCtx.raw)
    (targetValues sourceValues : Array RuntimeValue)
    (targetState : InterpreterState targetCtx) (sourceState : InterpreterState sourceCtx)
    (results : (InterpreterState targetCtx × Array RuntimeValue) →
      (InterpreterState sourceCtx × Array RuntimeValue) → Prop)
    (reachable :
      RegionTree targetCtx (InterpreterState targetCtx)
        (InterpreterState targetCtx × Array RuntimeValue) →
      RegionTree sourceCtx (InterpreterState sourceCtx)
        (InterpreterState sourceCtx × Array RuntimeValue) → Prop)
    (initial : reachable
      (interpretCFG targetRegion targetValues targetState targetIn)
      (interpretCFG sourceRegion sourceValues sourceState sourceIn))
    (step : ∀ t s, reachable t s → _root_.CTree.Sim
      (Sum.LiftRel reachable results) (regionRecStep t) (regionRecStep s)) :
    _root_.CTree.Sim results
      (interpretRegion targetRegion targetValues targetState targetIn)
      (interpretRegion sourceRegion sourceValues sourceState sourceIn) := by
  unfold interpretRegion _root_.CTree.mrec _root_.CTree.interp_mrec
  apply _root_.CTree.Sim.iter _ _ _ _ initial
  intro t s h
  have hs := step t s h
  unfold regionRecStep at hs
  grind

/-- Lift region refinement across contexts through the function wrapper.
Only a well-formed source function imposes obligations: its target must still be a
function with one region, and the bodies must simulate from empty variables and the given memory. -/
theorem sim_interpretFunction
    {targetCtx sourceCtx : WfIRContext OpCode} {target source : OperationPtr}
    (targetIn : target.InBounds targetCtx.raw) (sourceIn : source.InBounds sourceCtx.raw)
    (targetValues sourceValues : Array RuntimeValue) (mem : MemoryState)
    (results : Array RuntimeValue → Array RuntimeValue → Prop)
    (bodies : ∀ (sourceFn : FunctionOp sourceCtx.raw source),
      FunctionOp.of? source sourceCtx.raw = some sourceFn →
      ∀ (sourceOne : source.getNumRegions sourceCtx.raw = 1),
      ∃ (targetFn : FunctionOp targetCtx.raw target),
        FunctionOp.of? target targetCtx.raw = some targetFn ∧
        ∃ (targetOne : target.getNumRegions targetCtx.raw = 1),
          _root_.CTree.Sim (fun t s => results t.2 s.2)
            (interpretRegion (targetFn.getFunctionBody targetIn (by omega)) targetValues
              ⟨.empty targetCtx, mem⟩)
            (interpretRegion (sourceFn.getFunctionBody sourceIn (by omega)) sourceValues
              ⟨.empty sourceCtx, mem⟩)) :
    _root_.CTree.Sim results
      (interpretFunction target targetValues mem targetIn) (interpretFunction source sourceValues mem sourceIn) := by
  cases sourceEq : FunctionOp.of? source sourceCtx.raw with
  | none =>
    simp only [interpretFunction, sourceEq]
    exact sim_fail _ _
  | some sourceFn =>
    by_cases sourceOne : source.getNumRegions sourceCtx.raw = 1
    · obtain ⟨targetFn, targetEq, targetOne, bodySim⟩ := bodies sourceFn sourceEq sourceOne
      simp only [interpretFunction, sourceEq, targetEq, sourceOne, targetOne,
        ne_eq, not_true_eq_false, ↓reduceDIte]
      exact _root_.CTree.Sim.bind _ _ _ _ bodySim (fun t s h => by simpa using h)
    · simp only [interpretFunction, sourceEq, ne_eq, sourceOne]
      exact sim_fail _ _

end Veir.CTree

namespace Veir

/-- A cross-context body simulation gives the public function-refinement relation.
The body premise is required only for a source function with one region. -/
theorem OperationPtr.isRefinedByAsFunctionCTree_of_bodies
    {sourceCtx targetCtx : WfIRContext OpCode} {source target : OperationPtr}
    (sourceIn : source.InBounds sourceCtx.raw) (targetIn : target.InBounds targetCtx.raw)
    (sourceFn : FunctionOp sourceCtx.raw source) (targetFn : FunctionOp targetCtx.raw target)
    (sourceHeader : FunctionOp.of? source sourceCtx.raw = some sourceFn)
    (targetHeader : FunctionOp.of? target targetCtx.raw = some targetFn)
    (headers : source.getNumRegions sourceCtx.raw = 1 → target.getNumRegions targetCtx.raw = 1)
    (bodies : ∀ (sourceValues targetValues : Array RuntimeValue) (mem : MemoryState),
      sourceValues ⊒ targetValues →
      ∀ (sourceOne : source.getNumRegions sourceCtx.raw = 1),
      _root_.CTree.Sim (fun t s => RuntimeValue.arrayIsRefinedBy s.2 t.2)
        (CTree.interpretRegion (targetFn.getFunctionBody targetIn (by have := headers sourceOne; omega))
          targetValues ⟨.empty targetCtx, mem⟩)
        (CTree.interpretRegion (sourceFn.getFunctionBody sourceIn (by omega))
          sourceValues ⟨.empty sourceCtx, mem⟩)) :
    source.isRefinedByAsFunctionCTree sourceCtx target targetCtx sourceIn targetIn := by
  simp only [isRefinedByAsFunctionCTree, sourceHeader, targetHeader]
  intro sourceValues targetValues mem refined
  apply CTree.sim_interpretFunction targetIn sourceIn targetValues sourceValues mem
  intro sf sfEq sourceOne
  have : sf = sourceFn := by grind
  subst sf
  exact ⟨targetFn, targetHeader, headers sourceOne, bodies sourceValues targetValues mem refined sourceOne⟩

end Veir
