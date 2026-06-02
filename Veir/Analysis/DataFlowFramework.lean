module

public import Std.Data.DHashMap
public import Std.Data.HashMap
public import Veir.Analysis.DataFlow.Facts

open Std (DHashMap HashMap)

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
  lattice : HashMap LatticeAnchor (DHashMap FactKind Fact)
  workList : WorkList

def DataFlowContext.empty : DataFlowContext :=
  { lattice := ∅
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
  Hook that's called when the fact changes state. Typically used to
  enqueue a fact's dependents because it changed.
  -/
  propagate : Fact kind → DataFlowContext → IRContext OpCode → DataFlowContext

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
    (ctx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  FactSpec.propagate (kind := kind) fact ctx irCtx

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
  init : OperationPtr → DataFlowContext → IRContext OpCode → DataFlowContext
  /--
  The transfer function, visiting the given `InsertPoint`.
  -/
  visit : InsertPoint → DataFlowContext → IRContext OpCode → DataFlowContext

namespace DataFlowContext

/--
Enqueue one transfer problem onto the worklist.
-/
def enqueue (ctx : DataFlowContext) (workItem : WorkItem) : DataFlowContext :=
  { ctx with workList := ctx.workList.enqueue workItem }

/--
Read the fact of kind `kind` stored at `anchor`, if any.
-/
def getFact? (kind : FactKind) [FactSpec kind]
    (ctx : DataFlowContext) (anchor : LatticeAnchor) : Option (Fact kind) := do
  let facts ← ctx.lattice.get? anchor
  DHashMap.get? facts kind

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
  let facts := (ctx.lattice.getD anchor ∅).insert kind fact
  { ctx with lattice := ctx.lattice.insert anchor facts }

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
    (irCtx : IRContext OpCode) : DataFlowContext :=
  let current := ctx.getOrMkFact kind anchor
  let (fact, changed) := f current
  let ctx := ctx.setFact kind anchor fact
  if changed then
    fact.propagate ctx irCtx
  else
    ctx

end DataFlowContext

/--
Analyses involved in the fixpoint loop.
-/
abbrev RegisteredAnalyses := HashMap AnalysisKind DataFlowAnalysis

/--
Run the worklist solver to completion.

Returns `Option` since `run` may run forever.
TODO: Eventually prove via monotonicity that this is in fact impossible.
-/
partial def run (analyses : RegisteredAnalyses) (ctx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option DataFlowContext :=
  match ctx.workList.dequeue? with
  | none => some ctx
  | some ((point, analysisKind), workList) =>
    let ctx := { ctx with workList := workList }
    match analyses.get? analysisKind with
    | some analysis =>
      let ctx := analysis.visit point ctx irCtx
      run analyses ctx irCtx
    | none =>
      panic! s!"analysis {reprStr analysisKind} is not registered"

/--
Initialize the registered analyses and run the worklist solver to a fixpoint.

Returns `some` whenever it terminates.
-/
def fixpointSolve (top : OperationPtr) (analyses : Array DataFlowAnalysis)
    (irCtx : IRContext OpCode) : Option DataFlowContext := Id.run do
  let mut ctx := DataFlowContext.empty
  let mut registeredAnalyses : RegisteredAnalyses := ∅
  for analysis in analyses do
    registeredAnalyses := registeredAnalyses.insert analysis.kind analysis
  for analysis in analyses do
    ctx := analysis.init top ctx irCtx
  run registeredAnalyses ctx irCtx

end Veir
