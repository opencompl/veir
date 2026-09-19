module

public import Std.Data.HashSet
public import Veir.Analysis.DataFlow.Facts
public import Veir.IR.WellFormed

open Std (DHashMap HashMap HashSet)

public section

namespace Veir

/-!
# Dataflow framework 
-/

/--
The solver state containing all dataflow facts and the worklist of program points 
to call transfer functions on.
-/
structure DataFlowContext where
  lattice : DHashMap FactKey (Fact ·.kind)
  dependencyGraph : DependencyGraph FactKey WorkItem
  registeredAnalyses : HashSet AnalysisKind
  workList : WorkList

def DataFlowContext.empty : DataFlowContext :=
  { lattice := ∅
    dependencyGraph := .empty
    registeredAnalyses := ∅
    workList := .empty }

/--
Implement this class to register a custom type to be recognized as
a fact type by the dataflow framework.
-/
class FactSpec (kind : FactKind) where
  /--
  Default state a fact starts in. Typically either bottom or top. 
  -/
  mkDefault : Fact kind
  /--
  Hook called after the framework enqueues a changed fact's dependents.
  Override it for fact kind specific propagation behavior.
  -/
  propagate : Fact kind → LatticeAnchor → DataFlowContext → WfIRContext OpCode → DataFlowContext :=
    fun _ _ dfCtx _ => dfCtx

namespace Fact

/--
Construct the default fact for a given lattice anchor. 
-/
def mkDefault (kind : FactKind) [FactSpec kind] : Fact kind :=
  FactSpec.mkDefault (kind := kind)

/--
Run the fact kind's propagation hook.
-/
def propagate [FactSpec kind]
    (fact : Fact kind)
    (anchor : LatticeAnchor)
    (ctx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext :=
  FactSpec.propagate (kind := kind) fact anchor ctx irCtx

end Fact

/--
A single transfer problem scheduled by the fixpoint solver.
-/
structure DataFlowAnalysis where
  /--
  Tag to identify the implemented analysis.
  -/
  kind : AnalysisKind
  /--
  Given the top level operation pointer, initializes the analysis to a valid state.
  This often involves enqueueing some number of work items into the work list, such
  as every SSA value reachable from the top level operation pointer.
  -/
  init : OperationPtr → DataFlowContext → WfIRContext OpCode → DataFlowContext
  /--
  The transfer function, visiting the given `InsertPoint`.
  -/
  visit : InsertPoint → DataFlowContext → WfIRContext OpCode → DataFlowContext

namespace DataFlowContext

/--
Enqueue one transfer problem onto the worklist.
-/
def enqueue (ctx : DataFlowContext) (workItem : WorkItem) : DataFlowContext :=
  { ctx with workList := ctx.workList.enqueue workItem }

/-- Return whether the given analysis is registered in the current fixpoint loop. -/
def hasAnalysis (ctx : DataFlowContext) (analysisKind : AnalysisKind) : Bool :=
  ctx.registeredAnalyses.contains analysisKind

/-- Return the facts read by `dependent`. -/
def getDependencies (ctx : DataFlowContext) (dependent : WorkItem) : HashSet FactKey :=
  ctx.dependencyGraph.getDependencies dependent

/-- Return the work items that read `dependency`. -/
def getDependents (ctx : DataFlowContext) (dependency : FactKey) : HashSet WorkItem :=
  ctx.dependencyGraph.getDependents dependency

/-- Replace the facts read by `dependent`. Updates both graph directions. -/
def setDependencies
    (ctx : DataFlowContext)
    (dependent : WorkItem)
    (dependencies : HashSet FactKey) : DataFlowContext :=
  { ctx with dependencyGraph := ctx.dependencyGraph.setDependencies dependent dependencies }

/-- Add one fact read by `dependent`. Updates both graph directions. -/
def addDependency
    (ctx : DataFlowContext)
    (dependent : WorkItem)
    (dependency : FactKey) : DataFlowContext :=
  { ctx with dependencyGraph := ctx.dependencyGraph.addDependency dependent dependency }

/-- Remove every fact read by `dependent`, updating both graph directions. -/
def clearDependencies (ctx : DataFlowContext) (dependent : WorkItem) : DataFlowContext :=
  { ctx with dependencyGraph := ctx.dependencyGraph.clearDependencies dependent }

/--
Read the fact of kind `kind` stored at `anchor`, if any.
-/
def getFact? (kind : FactKind) [FactSpec kind]
    (ctx : DataFlowContext) (anchor : LatticeAnchor) : Option (Fact kind) :=
  ctx.lattice.get? { anchor, kind }

/--
Read the fact of kind `kind` at `anchor`, creating the default fact if it is absent.
Note that this doesn't modify the context.
-/
def getOrMkFact (kind : FactKind) [spec : FactSpec kind]
    (ctx : DataFlowContext) (anchor : LatticeAnchor) : Fact kind :=
  match ctx.getFact? kind anchor with
  | some fact => fact
  | none => Fact.mkDefault kind

/--
Overwrite the stored fact of kind `kind` for `anchor`. 
-/
private def setFact (kind : FactKind) [FactSpec kind]
    (ctx : DataFlowContext) (anchor : LatticeAnchor) (fact : Fact kind) : DataFlowContext :=
  { ctx with lattice := ctx.lattice.insert { anchor, kind } fact }

/--
Apply an update with `f` to the fact of kind `kind` stored at `anchor`. 
-/
def modifyFact (kind : FactKind) [FactSpec kind]
    (ctx : DataFlowContext) (anchor : LatticeAnchor) (f : Fact kind → Fact kind) : DataFlowContext :=
  let current := ctx.getOrMkFact kind anchor
  ctx.setFact kind anchor (f current)

/--
Apply an update with `f` to the fact of kind `kind` stored at `anchor` and 
`propagate` if it changed.
-/
def modifyFactAndPropagate (kind : FactKind) [spec : FactSpec kind]
    (ctx : DataFlowContext)
    (anchor : LatticeAnchor)
    (f : Fact kind → Fact kind × Bool)
    (irCtx : WfIRContext OpCode) : DataFlowContext :=
  let current := ctx.getOrMkFact kind anchor
  let (fact, changed) := f current
  let ctx := ctx.setFact kind anchor fact
  if changed then
    Id.run do
      let mut ctx := ctx
      for dependent in ctx.getDependents { anchor, kind } do
        ctx := ctx.enqueue dependent
      fact.propagate anchor ctx irCtx
  else
    ctx

end DataFlowContext

/--
Map for analyses involved in the fixpoint loop. When the fixpoint
loop pops a workitem off the worklist, it receives an `AnalysisKind`.
This object serves to map that kind back to the `DataFlowAnalysis` it
belongs to.
-/
abbrev AnalysesMap := HashMap AnalysisKind DataFlowAnalysis

/--
Run the worklist solver to completion.

Returns `Option` since `run` may run forever.
TODO: Eventually prove via monotonicity that this is in fact impossible.
-/
partial def run (analysesMap : AnalysesMap) (ctx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Option DataFlowContext :=
  match ctx.workList.dequeue? with
  | none => some ctx
  | some ((point, analysisKind), workList) =>
    let ctx := { ctx with workList := workList }
    match analysesMap.get? analysisKind with
    | some analysis =>
      let ctx := analysis.visit point ctx irCtx
      run analysesMap ctx irCtx
    | none =>
      panic! s!"analysis {reprStr analysisKind} is not registered"

/--
Initialize the registered analyses and run the worklist solver to a fixpoint.

Returns `some` whenever it terminates.
-/
def fixpointSolve (top : OperationPtr) (analyses : Array DataFlowAnalysis)
    (irCtx : WfIRContext OpCode) : Option DataFlowContext := Id.run do
  let mut ctx := DataFlowContext.empty
  let mut registeredAnalysesMap : AnalysesMap := ∅
  for analysis in analyses do
    registeredAnalysesMap := registeredAnalysesMap.insert analysis.kind analysis
    ctx := { ctx with registeredAnalyses := ctx.registeredAnalyses.insert analysis.kind }
  for analysis in analyses do
    ctx := analysis.init top ctx irCtx
  run registeredAnalysesMap ctx irCtx

end Veir
