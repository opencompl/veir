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
-- NEVER use this type directly, use `DataFlowAnalysis` which provides a proof that
-- `ctx` is always of type `DataFlowContext`
structure RawDataFlowAnalysis where 
  ctx : Type u -- Always `DataFlowContext`
  init : OperationPtr -> ctx -> ctx
  visit : ProgramPoint -> ctx -> ctx

structure DataFlowAnalysisPtr where
  id: Nat

instance : Coe DataFlowAnalysisPtr Nat where
  coe ptr := ptr.id
-- =============================================================================== -- 

-- ================================== WorkList =================================== -- 
-- A queued item stores a program point and the index of the analysis to run.
def WorkItem := ProgramPoint × DataFlowAnalysisPtr 
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

-- NEVER use this type directly, use `AnalysisState` which provides a proof that
-- `ctx` is always of type `DataFlowContext`
structure RawAnalysisState where -- record-of-functions style
  impl : Type u -- struct that extends `BaseAnalysisState` and contains some extra data
  ctx : Type v -- Always `DataFlowContext`
  value : impl
  onUpdate : Update impl ctx

-- =============================================================================== -- 

-- =============================== DataFlowContext =============================== -- 
structure DataFlowContext where 
  lattice : HashMap LatticeAnchor RawAnalysisState
  workList : WorkList

def DataFlowContext.empty : DataFlowContext :=
  { lattice := ∅
    workList := .empty
  }

instance : Coe DataFlowContext WorkList where
  coe ctx := ctx.workList

-- =============================================================================== -- 

-- ========================== DataFlowContext Wrappers =========================== -- 
-- Wrapper proving that a `RawDataFlowAnalysis` is specialized to `DataFlowContext`.
structure DataFlowAnalysis where
  val : RawDataFlowAnalysis
  hctx : val.ctx = DataFlowContext

namespace DataFlowAnalysis

def init (analysis : DataFlowAnalysis) (top : OperationPtr) (ctx : DataFlowContext) : DataFlowContext := by
  cases analysis with
  | mk val hctx =>
    cases val with
    | mk _ init _ =>
      cases hctx
      exact init top ctx

def visit (analysis : DataFlowAnalysis) (point : ProgramPoint) (ctx : DataFlowContext) : DataFlowContext := by
  cases analysis with
  | mk val hctx =>
    cases val with
    | mk _ _ visit =>
      cases hctx
      exact visit point ctx

def toRaw (analysis : DataFlowAnalysis) : RawDataFlowAnalysis :=
  analysis.val

def new
    (init : OperationPtr -> DataFlowContext -> DataFlowContext)
    (visit : ProgramPoint -> DataFlowContext -> DataFlowContext) : DataFlowAnalysis :=
  { val := { ctx := DataFlowContext 
             init := init
             visit := visit }
    hctx := rfl
  }

end DataFlowAnalysis

-- Wrapper proving that a `RawAnalysisState` is specialized to `DataFlowContext`.
structure AnalysisState where
  val : RawAnalysisState
  hctx : val.ctx = DataFlowContext

namespace AnalysisState

def onUpdate (state : AnalysisState) (ctx : DataFlowContext) : DataFlowContext := by
  cases state with
  | mk val hctx =>
    cases val with
    | mk Impl _ value onUpdate =>
      cases hctx
      letI : Update Impl DataFlowContext := onUpdate
      exact Update.onUpdate value ctx

def toRaw (state : AnalysisState) : RawAnalysisState :=
  state.val

def new (value : Impl) [Update Impl DataFlowContext] : AnalysisState :=
  { val := { impl := Impl
             ctx := DataFlowContext
             value := value
             onUpdate := inferInstance }
    hctx := rfl
  }

end AnalysisState
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
partial def run (analyses : Array DataFlowAnalysis) (ctx : DataFlowContext) : DataFlowContext :=
  match ctx.workList.dequeue? with
  | none =>
    ctx
  | some ((point, dataFlowAnalysisPtr), rest) =>
    let ctx := { ctx with workList := rest }
    let ctx :=
      if h : dataFlowAnalysisPtr < analyses.size then
        let analysis := analyses[dataFlowAnalysisPtr.id]'h
        analysis.visit point ctx
      else
        dbg_trace "Invalid DataFlowAnalysisPtr!"
        ctx
    run analyses ctx

def fixpointSolve (top: OperationPtr) (analyses : Array DataFlowAnalysis) : DataFlowContext := Id.run do
  -- init
  let mut ctx := DataFlowContext.empty
  for analysis in analyses do
    ctx := analysis.init top ctx

  -- run
  run analyses ctx

-- =============================================================================== -- 

end Veir
