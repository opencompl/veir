module

public import Std.Data.HashMap
public import Init.Data.Queue
public import Veir.IR.Basic
public import Veir.Properties

open Std(HashMap)
open Std(Queue)

public section

namespace Veir

inductive ProgramPoint where
  | OperationPtr (op : OperationPtr)
deriving BEq, Hashable

inductive LatticeAnchor
  | ProgramPoint (point : ProgramPoint)
  | ValuePtr (value : ValuePtr)
deriving BEq, Hashable

-- =============================== DataFlowAnalysis ============================== --
-- `Dynamic` is ALWAYS `DataFlowContext`; panic if this invariant is broken.
structure DataFlowAnalysis where
  private mk ::
  initDyn : OperationPtr -> Dynamic -> IRContext OpCode -> Dynamic
  visitDyn : ProgramPoint -> Dynamic -> IRContext OpCode -> Dynamic
-- =============================================================================== --

-- ================================== WorkList =================================== --
-- A queued item stores a program point and the analysis to run.
@[expose] def WorkItem := ProgramPoint × DataFlowAnalysis
@[expose] def WorkList := Queue WorkItem
-- =============================================================================== --

-- ================================ AnalysisState ================================ --
-- Lattice elements are stored in structures that implement the `Update` typeclass.
class Update (State : Type u) (Ctx : Type v) where
  onUpdate : State -> Ctx -> IRContext OpCode -> Ctx

structure BaseAnalysisState where
  anchor : LatticeAnchor
  dependents : Array WorkItem

def BaseAnalysisState.onUpdate (state : BaseAnalysisState) (workList : WorkList) : WorkList := Id.run do
  let mut workList := workList
  for workItem in state.dependents do
    workList := workList.enqueue workItem
  workList

-- `valueDyn` stores the concrete state object. `onUpdateDyn` expects `(valueDyn, dfCtxDyn)`.
structure AnalysisState where
  private mk ::
  valueDyn : Dynamic
  -- State -> DataFlowContext -> IRContext -> DataFlowContext
  onUpdateDyn : Dynamic -> Dynamic -> IRContext OpCode -> Dynamic
-- =============================================================================== --

-- =============================== DataFlowContext =============================== --
structure DataFlowContext where
  /-- 
  Maps a program location to a set of states for that location, 
  each belonging to a different analysis.
  -/
  lattice : HashMap LatticeAnchor (HashMap Lean.Name AnalysisState)

  -- queue for the fixpoint solver
  workList : WorkList
deriving TypeName

def DataFlowContext.empty : DataFlowContext :=
  { lattice := ∅
    workList := .empty
  }

instance : Inhabited DataFlowContext where
  default := DataFlowContext.empty

private unsafe def asDataFlowContextImpl (ctxDyn : Dynamic) : DataFlowContext :=
  unsafeCast ctxDyn

private unsafe def asDynamicImpl (ctx : DataFlowContext) : Dynamic :=
  unsafeCast ctx

@[implemented_by asDataFlowContextImpl]
private opaque asDataFlowContext (ctxDyn : Dynamic) : DataFlowContext :=
  match ctxDyn.get? DataFlowContext with
  | some dfCtx =>
    dfCtx
  | none =>
    panic! s!"expected DataFlowContext, got {ctxDyn.typeName}"

@[implemented_by asDynamicImpl]
private def asDynamic (ctx : DataFlowContext) : Dynamic :=
  Dynamic.mk ctx

instance : Coe DataFlowContext WorkList where
  coe dfCtx := dfCtx.workList

-- ================== Safe API (DataFlowAnalysis/AnalysisState) ================== --
namespace DataFlowAnalysis

def init (analysis : DataFlowAnalysis) (top : OperationPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  asDataFlowContext (analysis.initDyn top (asDynamic dfCtx) irCtx)

def visit (analysis : DataFlowAnalysis) (point : ProgramPoint) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  asDataFlowContext (analysis.visitDyn point (asDynamic dfCtx) irCtx)

def new
    (init : OperationPtr -> DataFlowContext -> IRContext OpCode -> DataFlowContext)
    (visit : ProgramPoint -> DataFlowContext -> IRContext OpCode -> DataFlowContext) : DataFlowAnalysis :=
  { initDyn := fun top dfCtxDyn irCtx =>
      asDynamic (init top (asDataFlowContext dfCtxDyn) irCtx)
    visitDyn := fun point dfCtxDyn irCtx =>
      asDynamic (visit point (asDataFlowContext dfCtxDyn) irCtx)
  }

end DataFlowAnalysis

namespace AnalysisState

def onUpdate (state : AnalysisState) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  asDataFlowContext (state.onUpdateDyn state.valueDyn (asDynamic dfCtx) irCtx)

def new (value : Impl) [TypeName Impl] [Update Impl DataFlowContext] : AnalysisState :=
  { valueDyn := Dynamic.mk value
    onUpdateDyn := fun valueDyn dfCtxDyn irCtx =>
      match valueDyn.get? Impl with
      | some value =>
        let dfCtx := asDataFlowContext dfCtxDyn
        asDynamic (Update.onUpdate value dfCtx irCtx)
      | none =>
        asDynamic (panic! s!"expected value of type {TypeName.typeName Impl}, got {valueDyn.typeName}" : DataFlowContext)
  }

def getValue? (state : AnalysisState) (Impl : Type u) [TypeName Impl] : Option Impl :=
  state.valueDyn.get? Impl

end AnalysisState
-- =============================================================================== --

-- =============================== DataFlowContext =============================== --
namespace DataFlowContext

def getState? (dfCtx : DataFlowContext) (anchor : LatticeAnchor)
    (State : Type) [TypeName State] : Option State := do
  let states ← dfCtx.lattice.get? anchor
  let state ← states.get? (TypeName.typeName State)  
  AnalysisState.getValue? state State

def insertState
    (dfCtx : DataFlowContext)
    (anchor : LatticeAnchor)
    (state : AnalysisState) : DataFlowContext :=
  let states := (dfCtx.lattice.getD anchor ∅).insert state.valueDyn.typeName state
  { dfCtx with lattice := dfCtx.lattice.insert anchor states }

end DataFlowContext
-- =============================================================================== --

-- =============================== Fixpoint Solver =============================== --
partial def run (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext :=
  match dfCtx.workList.dequeue? with
  | none =>
    dfCtx
  | some ((point, analysis), workList) =>
    let dfCtx := { dfCtx with workList := workList }
    let dfCtx := analysis.visit point dfCtx irCtx
    run dfCtx irCtx

def fixpointSolve (top : OperationPtr) (analyses : Array DataFlowAnalysis)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- init
  let mut dfCtx := DataFlowContext.empty
  for analysis in analyses do
    dfCtx := analysis.init top dfCtx irCtx

  -- run
  run dfCtx irCtx

-- =============================================================================== --

end Veir
