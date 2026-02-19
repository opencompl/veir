module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Init.Data.Queue
public import Veir.IR.Basic

open Std(HashSet)
open Std(HashMap)
open Std(Queue)

namespace Veir

inductive ProgramPoint where
  | OperationPtr

inductive LatticeAnchor
  | ProgramPoint
  | ValuePtr 
deriving BEq, Hashable

-- record-of-functions style
structure DataFlowAnalysis where
  ctx : Type -- Used only for LatticeContext
  init : OperationPtr -> ctx -> ctx
  visit : ProgramPoint -> ctx -> ctx

-- ================================== WorkList =================================== -- 
def WorkItem := ProgramPoint × DataFlowAnalysis
def WorkList := Queue WorkItem
-- =============================================================================== -- 

-- ================================ AnalysisState ================================ -- 
-- Lattice Elements are stored in structures that implement the `Update` typeclass.
-- These structures contain a `BaseAnalysisState` along with anything else it needs.
-- `AnalysisState` is used to allow for dynamic dispatch (runtime polymorphism).
class Update (State : Type u) (Ctx : Type v) where
  onUpdate : State -> WorkList -> Ctx -> (WorkList × Ctx)

structure BaseAnalysisState where
  anchor : LatticeAnchor
  dependents : Array WorkItem 

instance : Update BaseAnalysisState Unit where
  onUpdate (state : BaseAnalysisState) (workList : WorkList) (_: Unit) : (WorkList × Unit) := Id.run do
    let mut workList := workList 
    for workItem in state.dependents do
      workList := workList.enqueue workItem
    ⟨ workList, () ⟩  

structure AnalysisState where
  impl : Type u -- struct that contains a BaseAnalysisState and some lattice element
  ctx : Type v -- Used only for LatticeContext
  inst : Update impl ctx

-- =============================================================================== -- 

def LatticeContext := HashMap LatticeAnchor AnalysisState

structure AbstractSparseLatticeStateImpl extends BaseAnalysisState where
  useDefSubscribers : Array DataFlowAnalysis 

instance : Update AbstractSparseLatticeStateImpl LatticeContext where
  onUpdate (state: AbstractSparseLatticeStateImpl) (workList : WorkList) (ctx : LatticeContext) : WorkList := Id.run do 
    let mut workList := state.toBaseAnalysisState.onUpdate state workList Unit
    workList

def AbstractSparseLatticeState : AnalysisState :=
  { impl := AbstractSparseLatticeStateImpl
    ctx := LatticeContext 
    inst := inferInstance }

/- void AbstractSparseLattice::onUpdate(DataFlowSolver *solver) const { -/
/-   AnalysisState::onUpdate(solver); -/
/- -/
/-   // Push all users of the value to the queue. -/
/-   for (Operation *user : cast<Value>(anchor).getUsers()) -/
/-     for (DataFlowAnalysis *analysis : useDefSubscribers) -/
/-       solver->enqueue({solver->getProgramPointAfter(user), analysis}); -/
/- } -/


def fixpointSolve (top: OperationPtr) (analyses : Array DataFlowAnalysis) : LatticeContext :=
  let latticeCtx : LatticeContext := sorry
  sorry

end Veir
