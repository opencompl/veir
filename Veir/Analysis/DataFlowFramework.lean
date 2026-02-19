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

-- =============================== DataFlowAnalysis ============================== -- 
structure DataFlowAnalysis where -- record-of-functions style
  ctx : Type -- Used only for LatticeContext
  init : OperationPtr -> ctx -> ctx
  visit : ProgramPoint -> ctx -> ctx
-- =============================================================================== -- 

-- ================================== WorkList =================================== -- 
def WorkItem := ProgramPoint × DataFlowAnalysis
def WorkList := Queue WorkItem
-- =============================================================================== -- 

-- ================================ AnalysisState ================================ -- 
-- Lattice Elements are stored in structures that implement the `Update` typeclass.
-- These structures contain a `BaseAnalysisState` along with anything else it needs.
-- `AnalysisState` is used to allow for dynamic dispatch (runtime polymorphism).
class Update (State : Type u) (Ctx : Type v) where
  onUpdate : State -> Ctx -> Ctx

structure BaseAnalysisState where
  anchor : LatticeAnchor
  dependents : Array WorkItem 

def BaseAnalysisState.onUpdate (state : BaseAnalysisState) (workList : WorkList) : WorkList := Id.run do
  let mut workList := workList 
  for workItem in state.dependents do
    workList := workList.enqueue workItem
  workList  

structure AnalysisState where -- record-of-functions style
  impl : Type u -- struct that contains a BaseAnalysisState and some lattice element
  ctx : Type v
  value : impl
  onUpdate : Update impl ctx

-- =============================================================================== -- 

-- =============================== DataFlowContext =============================== -- 
structure DataFlowContext where 
  lattice : HashMap LatticeAnchor AnalysisState
  workList : WorkList

instance : Coe DataFlowContext WorkList where
  coe ctx := ctx.workList

-- =============================================================================== -- 

structure AbstractSparseLatticeState extends BaseAnalysisState where
  useDefSubscribers : Array DataFlowAnalysis 

instance : Update AbstractSparseLatticeState DataFlowContext where
  onUpdate (state: AbstractSparseLatticeState) (ctx : DataFlowContext) : DataFlowContext := Id.run do 
    let mut ctx := {ctx with workList := state.onUpdate ctx}
    -- Do some other stuff...
    ctx
     
def mkAbstractSparseLatticeState (value : AbstractSparseLatticeState) : AnalysisState :=
  { impl := AbstractSparseLatticeState 
    ctx := DataFlowContext
    value := value 
    onUpdate := inferInstance 
  }

structure ConstantLatticeState extends AbstractSparseLatticeState where
  value : ValuePtr

instance : Update ConstantLatticeState DataFlowContext where
  onUpdate state ctx :=
    Update.onUpdate
      state.toAbstractSparseLatticeState
      ctx

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
