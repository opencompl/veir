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
  ctx : Type u -- Always `DataFlowContext`
  init : OperationPtr -> ctx -> ctx
  visit : ProgramPoint -> ctx -> ctx
-- =============================================================================== -- 

-- ================================== WorkList =================================== -- 
def WorkItem := ProgramPoint × DataFlowAnalysis
def WorkList := Queue WorkItem
-- =============================================================================== -- 

-- ================================ AnalysisState ================================ -- 
-- Lattice Elements are stored in structures that implement the `Update` typeclass.
-- These structures extend `BaseAnalysisState` along storing with anything else it needs.
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
  impl : Type u -- struct that extends `BaseAnalysisState` and contains some extra data
  ctx : Type v -- Always `DataFlowContext`
  value : impl
  onUpdate : Update impl ctx

-- =============================================================================== -- 

-- =============================== DataFlowContext =============================== -- 
structure DataFlowContext where 
  lattice : HashMap LatticeAnchor AnalysisState
  workList : WorkList

def DataFlowContext.empty : DataFlowContext :=
  { lattice := ∅
    workList := .empty
  }

instance : Coe DataFlowContext WorkList where
  coe ctx := ctx.workList

def DataFlowAnalysis.new
    (init : OperationPtr -> DataFlowContext -> DataFlowContext)
    (visit : ProgramPoint -> DataFlowContext -> DataFlowContext) : DataFlowAnalysis :=
  { ctx := DataFlowContext
    init := init
    visit := visit
  }

def AnalysisState.new (value : Impl) [Update Impl DataFlowContext] : AnalysisState :=
  { impl := Impl 
    ctx := DataFlowContext 
    value := value
    onUpdate := inferInstance
  }

-- =============================================================================== -- 

-- ====================== Example `AnalysisState` Children ======================= -- 
structure AbstractSparseLatticeState extends BaseAnalysisState where
  useDefSubscribers : Array DataFlowAnalysis 

instance : Update AbstractSparseLatticeState DataFlowContext where
  onUpdate (state: AbstractSparseLatticeState) (ctx : DataFlowContext) : DataFlowContext := Id.run do 
    let mut ctx := {ctx with workList := state.onUpdate ctx}
    -- Do some other stuff...
    ctx
     
structure ConstantLatticeState extends AbstractSparseLatticeState where
  value : ValuePtr

instance : Update ConstantLatticeState DataFlowContext where
  onUpdate state ctx :=
    Update.onUpdate
      state.toAbstractSparseLatticeState
      ctx
-- =============================================================================== -- 

-- ===================== Example `DataFlowAnalysis` Children ===================== -- 
def ConstantAnalysis.init (top : OperationPtr) (ctx : DataFlowContext) : DataFlowContext :=
  sorry
def ConstantAnalysis.visit (point : ProgramPoint) (ctx : DataFlowContext) : DataFlowContext := 
  sorry
def ConstantAnalysis := DataFlowAnalysis.new ConstantAnalysis.init ConstantAnalysis.visit 
-- =============================================================================== -- 

-- =============================== Fixpoint Solver =============================== -- 
def fixpointSolve (top: OperationPtr) (analyses : Array DataFlowAnalysis) : DataFlowContext :=
  let ctx := DataFlowContext.empty
  for analysis in analyses do
    panic! "Not Done" 
  ctx

-- =============================================================================== -- 

end Veir
