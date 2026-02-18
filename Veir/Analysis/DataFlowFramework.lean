module

public import Std.Data.HashMap
public import Veir.Analysis.Lattice
public import Veir.IR.Basic

public section

namespace Veir
namespace Analysis

open Std (HashMap)

/-
In classical data-flow analysis, lattice anchor represent positions in a
program to which lattice elements are attached. In sparse data-flow analysis,
these can be SSA values, and in dense data-flow analysis, these are the
program points before and after every operation.
-/
inductive ProgramPoint where
  | blockEntry (ptr : BlockPtr)
  | beforeOp (ptr : OperationPtr)
  | afterOp (ptr : OperationPtr)
deriving Inhabited, Repr, DecidableEq, Hashable

/-
In classical data-flow analysis, lattice anchor represent positions in a
program to which lattice elements are attached. In sparse data-flow
analysis, these can be SSA values, and in dense data-flow analysis, these
are the program points before and after every operation.
-/
inductive LatticeAnchor where
  | value (ptr : ValuePtr)
  | point (p : ProgramPoint)
  | block (ptr : BlockPtr)
deriving Inhabited, Repr, DecidableEq, Hashable

abbrev DataFlowAnalysisPtr := Nat
abbrev WorkItem := ProgramPoint × DataFlowAnalysisPtr

/-
Analysis states contain data-flow information that are attached to lattice anchors and which evolve as the analysis iterates. 
-/
structure AnalysisState where
  anchor : LatticeAnchor
  dependents : Array WorkItem 
deriving Inhabited

def AnalysisState.addDependency (state : AnalysisState) (p: ProgramPoint) (analysis : DataFlowAnalysisPtr) : AnalysisState :=
  { state with dependents := state.dependents.push ⟨ p, analysis ⟩ }

def AnalysisState.getAnchor (state : AnalysisState) : LatticeAnchor :=
  state.anchor

/-
FIFO queue for `WorkItem`s.

TODO: Figure out of this is an efficient internal implementation for the worklist
-/
structure WorkListNodePtr where
  id : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

structure WorkListNode where
  item : WorkItem
  next : Option WorkListNodePtr

structure WorkList where
  nodes : HashMap WorkListNodePtr WorkListNode := {}
  first : Option WorkListNodePtr := none
  last : Option WorkListNodePtr := none
  nextID : Nat := 0
deriving Inhabited

def WorkList.empty : WorkList :=
  { nodes := {}, first := none, last := none, nextID := 0 }

def WorkList.isEmpty (w : WorkList) : Bool :=
  w.first.isNone

def WorkList.getNode (w : WorkList) (ptr : WorkListNodePtr) : Option WorkListNode :=
  w.nodes[ptr]?

def WorkList.getItem (w : WorkList) (ptr : WorkListNodePtr) : Option WorkItem :=
  (w.getNode ptr).map (·.item)

def WorkList.peek? (w : WorkList) : Option WorkItem :=
  match w.first with
  | none => none
  | some ptr => w.getItem ptr

def WorkList.enqueue (w : WorkList) (item : WorkItem) : WorkList :=
  let newPtr : WorkListNodePtr := { id := w.nextID }
  let newNode : WorkListNode :=
    { item := item, next := none }
  let nodes := w.nodes.insert newPtr newNode
  match w.last with
  | none =>
      { nodes := nodes, first := some newPtr, last := some newPtr,
        nextID := w.nextID + 1 }
  | some lastPtr =>
      match nodes[lastPtr]? with
      | none => panic! "WorkList invariant violated: missing last node"
      | some lastNode =>
          let nodes := nodes.insert lastPtr { lastNode with next := some newPtr }
          { nodes := nodes, first := w.first, last := some newPtr,
            nextID := w.nextID + 1 }

def WorkList.dequeue? (w : WorkList) : (Option WorkItem) × WorkList :=
  match w.first with
  | none => (none, w)
  | some firstPtr =>
      match w.getNode firstPtr with
      | none => panic! "WorkList invariant violated: missing first node"
      | some firstNode =>
          let nodes := w.nodes.erase firstPtr
          match firstNode.next with
          | none =>
              (some firstNode.item,
               { nodes := nodes, first := none, last := none,
                 nextID := w.nextID })
          | some nextPtr =>
              (some firstNode.item,
               { nodes := nodes, first := some nextPtr, last := w.last,
                 nextID := w.nextID })

/-
Mutable-style context for dataflow execution

TODO: Maybe WorkList and DataFlowContext should be merged into one type?
-/
structure DataFlowContext where
  /-
  The solver's work queue. Work items can be inserted to the front of the
  queue to be processed greedily, speeding up computations that otherwise
  quickly degenerate to quadratic due to propagation of state updates.
  -/
  worklist : WorkList := WorkList.empty
  analysisStates : HashMap LatticeAnchor AnalysisState
deriving Inhabited

/-
Create a dependency between the given AnalysisState and lattice anchor on the given DataFlowAnalysis.
-/
def DataFlowContext.addDependency
    (ctx : DataFlowContext) (state : AnalysisState)
    (p : ProgramPoint) (analysis : DataFlowAnalysisPtr) : DataFlowContext :=
  match ctx.analysisStates[state.anchor]? with
  | none =>
      { ctx with analysisStates :=
          ctx.analysisStates.insert state.anchor (state.addDependency p analysis) }
  | some curState =>
      { ctx with analysisStates :=
          ctx.analysisStates.insert state.anchor (curState.addDependency p analysis) }

/-
Enqueue WorkItem to WorkList
-/
def DataFlowContext.enqueue (ctx : DataFlowContext) (item : WorkItem) : DataFlowContext :=
  { ctx with worklist := ctx.worklist.enqueue item }

/-
Dequeue WorkItem from WorkList
-/
def DataFlowContext.dequeue? (ctx : DataFlowContext) : (Option WorkItem) × DataFlowContext :=
  let (item, worklist) := ctx.worklist.dequeue?
  (item, { ctx with worklist := worklist })

/-
Base class for all data-flow analyses. A child analysis is expected to build
an initial dependency graph (and optionally provide an initial state) when
initialized and define transfer functions when visiting program points.
-/
structure DataFlowAnalysis where
  /-
  Initialize the analysis from the provided top-level operation by building
  an initial dependency graph between all lattice anchors of interest. This
  can be implemented by calling `visit` on all program points of interest
  below the top-level operation.
  An analysis can optionally provide initial values to certain analysis
  states to influence the evolution of the analysis.
  -/
  init : DataFlowAnalysisPtr -> DataFlowContext -> OperationPtr -> IRContext -> DataFlowContext

  /-
  Visit the given program point. This function is invoked by the solver on
  this analysis with a given program point when a dependent analysis state
  is updated. The function is similar to a transfer function; it queries
  certain analysis states and sets other states.
 
  The function is expected to create dependencies on queried states and
  propagate updates on changed states. A dependency can be created by
  calling `addDependency` between the input state and a program point,
  indicating that, if the state is updated, the solver should invoke `solve`
  on the program point. The dependent point does not have to be the same as
  the provided point. An update to a state is propagated by calling
  `propagateIfChange` on the state. If the state has changed, then all its
  dependents are placed on the worklist.
 
  The dependency graph does not need to be static. Each invocation of
  `visit` can add new dependencies, but these dependencies will not be
  dynamically added to the worklist because the solver doesn't know what
  will provide a value for then.
  -/
  visit : DataFlowAnalysisPtr -> DataFlowContext -> ProgramPoint -> IRContext -> DataFlowContext

deriving Inhabited

/-
The general data-flow analysis solver. This class is responsible for
orchestrating child data-flow analyses, running the fixed-point iteration
algorithm, managing analysis state and lattice anchor memory, and tracking
dependencies between analyses, lattice anchor, and analysis states.
-/
structure DataFlowSolver where
  ctx : DataFlowContext
  analyses : Array DataFlowAnalysis := #[]
deriving Inhabited

def DataFlowSolver.enqueue (solver : DataFlowSolver) (item : WorkItem) : DataFlowSolver :=
  { solver with ctx := solver.ctx.enqueue item }

def DataFlowSolver.dequeue? (solver : DataFlowSolver) : (Option WorkItem) × DataFlowSolver :=
  let (item, ctx) := solver.ctx.dequeue?
  (item, { solver with ctx := ctx })

def DataFlowSolver.load (solver : DataFlowSolver)
    (analysis : DataFlowAnalysis) : DataFlowSolver × DataFlowAnalysisPtr :=
  let ptr := solver.analyses.size
  ({ solver with analyses := solver.analyses.push analysis }, ptr)

def DataFlowSolver.getAnalysis! (solver : DataFlowSolver) (ptr : DataFlowAnalysisPtr) : DataFlowAnalysis :=
  solver.analyses[ptr]!

def DataFlowSolver.visitWorkItem
    (solver : DataFlowSolver) (item : WorkItem) (irCtx : IRContext) : DataFlowSolver :=
  let (point, analysisPtr) := item
  let analysis := solver.getAnalysis! analysisPtr
  { solver with ctx := analysis.visit analysisPtr solver.ctx point irCtx }

/-
This function is called by the solver when the analysis state is updated
to enqueue more work items. For example, if a state tracks dependents
through the IR (e.g. use-def chains), this function can be implemented to
push those dependents on the worklist.
-/
def DataFlowSolver.onUpdate (solver : DataFlowSolver) (state : AnalysisState) : DataFlowSolver := Id.run do
  let mut solver := solver 
  for item in state.dependents do
    solver := solver.enqueue item
  solver

/-
Propagate an update to an analysis state if it changed by pushing
dependent work items to the back of the worklist queue.
-/
def DataFlowSolver.propagateIfChanged (solver : DataFlowSolver) (state : AnalysisState) (changed : ChangeResult) : DataFlowSolver :=
  if changed == .change then 
    solver.onUpdate state 
  else
    solver

/-
Create a dependency between the given AnalysisState and lattice anchor on the given DataFlowAnalysis.
-/
def DataFlowSolver.addDependency
    (solver : DataFlowSolver) (state : AnalysisState)
    (p : ProgramPoint) (analysis : DataFlowAnalysisPtr) : DataFlowSolver :=
  { solver with ctx := solver.ctx.addDependency state p analysis }
  
end Analysis
end Veir
