module

public import Std.Data.HashMap
public import Init.Data.Queue
public import Veir.IR.Basic
public import Veir.GlobalOpInfo

open Std(HashMap Queue)

public section

namespace Veir

inductive ProgramPoint where
  | inBlock (block : BlockPtr) (nextOp : Option OperationPtr)
  | standaloneOp (op : OperationPtr)
deriving BEq, Hashable

namespace ProgramPoint

/-- Create the program point at the beginning of a block. -/
def beforeBlock (block : BlockPtr) (irCtx : IRContext OpCode) : ProgramPoint :=
  .inBlock block (block.get! irCtx).firstOp

/-- Create the program point at the end of a block. -/
def afterBlock (block : BlockPtr) : ProgramPoint :=
  .inBlock block none

/-- Create the program point immediately before an operation. -/
def beforeOp (op : OperationPtr) (irCtx : IRContext OpCode) : ProgramPoint :=
  match (op.get! irCtx).parent with
  | some block =>
    .inBlock block (some op)
  | none =>
    .standaloneOp op

/-- Create the program point immediately after an operation. -/
def afterOp (op : OperationPtr) (irCtx : IRContext OpCode) : ProgramPoint :=
  match (op.get! irCtx).parent with
  | some block =>
    .inBlock block (op.get! irCtx).next
  | none =>
    .standaloneOp op

/-- Return the containing block, if this point is inside a block. -/
def getBlock? : ProgramPoint -> Option BlockPtr
  | .inBlock block _ =>
    some block
  | .standaloneOp _ =>
    none

/-- Return whether the program point is at the beginning of a block. -/
def isBlockStart (point : ProgramPoint) (irCtx : IRContext OpCode) : Bool :=
  match point with
  | .inBlock block nextOp =>
    nextOp == (block.get! irCtx).firstOp
  | .standaloneOp _ =>
    false

/-- Return the operation immediately preceding a non-block-start point. -/
def getPrevOp! (point : ProgramPoint) (irCtx : IRContext OpCode) : OperationPtr :=
  match point with
  | .inBlock block (some nextOp) =>
    match (nextOp.get! irCtx).prev with
    | some prev =>
      prev
    | none =>
      panic! s!"ProgramPoint.getPrevOp!: block-start point in block {block.id}"
  | .inBlock block none =>
    match (block.get! irCtx).lastOp with
    | some lastOp =>
      lastOp
    | none =>
      panic! s!"ProgramPoint.getPrevOp!: empty block {block.id} has no previous operation"
  | .standaloneOp op =>
    op

end ProgramPoint

@[expose] def CFGEdge := BlockPtr × BlockPtr

instance : BEq CFGEdge :=
  inferInstanceAs (BEq (BlockPtr × BlockPtr))

instance : Hashable CFGEdge :=
  inferInstanceAs (Hashable (BlockPtr × BlockPtr))

namespace CFGEdge

def getFrom (edge : CFGEdge) : BlockPtr :=
  edge.1

def getTo (edge : CFGEdge) : BlockPtr :=
  edge.2

end CFGEdge

inductive LatticeAnchor
  | ProgramPoint (point : ProgramPoint)
  | ValuePtr (value : ValuePtr)
  | CFGEdge (edge : CFGEdge)
deriving BEq, Hashable

class LatticeElement (Domain : Type) extends BEq Domain where
  typeNameInst : TypeName Domain
  bottom : Domain
  top : Domain
  join : Domain -> Domain -> Domain
  meet : Domain -> Domain -> Domain

attribute [instance] Veir.LatticeElement.toBEq

@[reducible] instance [LatticeElement Value] : TypeName Value :=
  LatticeElement.typeNameInst

-- =============================== DataFlowAnalysis ============================== --
-- `Dynamic` is ALWAYS `DataFlowContext`; panic if this invariant is broken.
structure DataFlowAnalysis where
  private mk ::
  id : Lean.Name
  initDyn : OperationPtr -> Dynamic -> IRContext OpCode -> Dynamic
  visitDyn : ProgramPoint -> Dynamic -> IRContext OpCode -> Dynamic
-- =============================================================================== --

-- ================================== WorkList =================================== --
-- A queued item stores a program point and the analysis to run.
@[expose] def WorkItem := ProgramPoint × Lean.Name
@[expose] def WorkList := Queue WorkItem
-- =============================================================================== --

-- ============================= ErasedAnalysisState ============================= --
-- `valueDyn` stores the concrete state object. `onUpdateDyn` expects `(valueDyn, dfCtxDyn)`.
structure ErasedAnalysisState where
  private mk ::
  valueDyn : Dynamic
  -- State -> DataFlowContext -> IRContext -> DataFlowContext
  onUpdateDyn : Dynamic -> Dynamic -> IRContext OpCode -> Dynamic
-- =============================================================================== --

-- =============================== DataFlowContext =============================== --
structure DataFlowContext where
  /-- Registered analyses for the current solver run, keyed by analysis id. -/
  analyses : HashMap Lean.Name DataFlowAnalysis

  /-- 
  Maps a program location to a set of states for that location, 
  each belonging to a different analysis.
  -/
  lattice : HashMap LatticeAnchor (HashMap Lean.Name ErasedAnalysisState)

  -- queue for the fixpoint solver
  workList : WorkList
deriving TypeName

def DataFlowContext.empty : DataFlowContext :=
  { analyses := ∅
    lattice := ∅
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
-- =============================================================================== --

-- ================== Safe API (DataFlowAnalysis/AnalysisState) ================== --
namespace DataFlowAnalysis

def init (analysis : DataFlowAnalysis) (top : OperationPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  asDataFlowContext (analysis.initDyn top (asDynamic dfCtx) irCtx)

def visit (analysis : DataFlowAnalysis) (point : ProgramPoint) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  asDataFlowContext (analysis.visitDyn point (asDynamic dfCtx) irCtx)

def new
    (id : Lean.Name)
    (init : OperationPtr -> DataFlowContext -> IRContext OpCode -> DataFlowContext)
    (visit : ProgramPoint -> DataFlowContext -> IRContext OpCode -> DataFlowContext) : DataFlowAnalysis :=
  { id := id
    initDyn := fun top dfCtxDyn irCtx =>
      asDynamic (init top (asDataFlowContext dfCtxDyn) irCtx)
    visitDyn := fun point dfCtxDyn irCtx =>
      asDynamic (visit point (asDataFlowContext dfCtxDyn) irCtx)
  }

end DataFlowAnalysis

structure AnalysisStateHeader where
  anchor : LatticeAnchor
  dependents : Array WorkItem

def AnalysisStateHeader.enqueueDependents (state : AnalysisStateHeader) (workList : WorkList) : WorkList := Id.run do
  let mut workList := workList
  for workItem in state.dependents do
    workList := workList.enqueue workItem
  workList

class AnalysisState (State : Type u) where
  typeNameInst : TypeName State
  mkState : LatticeAnchor -> State
  onUpdate : State -> DataFlowContext -> IRContext OpCode -> DataFlowContext
  toHeader : State -> AnalysisStateHeader

@[reducible] instance [AnalysisState State] : TypeName State :=
  AnalysisState.typeNameInst

instance [AnalysisState State] : CoeOut State AnalysisStateHeader where
  coe := AnalysisState.toHeader

namespace AnalysisState

def anchor (state : State) [AnalysisState State] : LatticeAnchor :=
  (AnalysisState.toHeader state).anchor

def dependents (state : State) [AnalysisState State] : Array WorkItem :=
  (AnalysisState.toHeader state).dependents

end AnalysisState

namespace ErasedAnalysisState

def onUpdate (state : ErasedAnalysisState) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  asDataFlowContext (state.onUpdateDyn state.valueDyn (asDynamic dfCtx) irCtx)

def new (state : Impl) [AnalysisState Impl] : ErasedAnalysisState :=
  { valueDyn := Dynamic.mk state
    onUpdateDyn := fun valueDyn dfCtxDyn irCtx =>
      match valueDyn.get? Impl with
      | some state =>
        let dfCtx := asDataFlowContext dfCtxDyn
        asDynamic (AnalysisState.onUpdate state dfCtx irCtx)
      | none =>
        asDynamic (panic! s!"expected value of type {TypeName.typeName Impl}, got {valueDyn.typeName}" : DataFlowContext)
  }

def getValue? (state : ErasedAnalysisState) (Impl : Type u) [AnalysisState Impl] : Option Impl :=
  state.valueDyn.get? Impl

end ErasedAnalysisState
-- =============================================================================== --

-- =============================== DataFlowContext =============================== --
namespace DataFlowContext

def getAnalysis? (dfCtx : DataFlowContext) (id : Lean.Name) : Option DataFlowAnalysis :=
  dfCtx.analyses.get? id

def insertAnalysis (dfCtx : DataFlowContext) (analysis : DataFlowAnalysis) : DataFlowContext :=
  { dfCtx with analyses := dfCtx.analyses.insert analysis.id analysis }

def getState? {State : Type} [AnalysisState State]
  (dfCtx : DataFlowContext) (anchor : LatticeAnchor) : Option State := do
  let states ← dfCtx.lattice.get? anchor
  let state ← states.get? (TypeName.typeName State)  
  ErasedAnalysisState.getValue? state State

def getOrMkState {State : Type} [AnalysisState State]
  (dfCtx : DataFlowContext) (anchor : LatticeAnchor) : State :=
  match dfCtx.getState? (State := State) anchor with
  | some state => state
  | none => AnalysisState.mkState anchor

private def writeState
    (dfCtx : DataFlowContext)
    (anchor : LatticeAnchor)
    (state : State)
    [AnalysisState State] : DataFlowContext :=
  let erasedState := ErasedAnalysisState.new state
  let states := (dfCtx.lattice.getD anchor ∅).insert erasedState.valueDyn.typeName erasedState
  { dfCtx with lattice := dfCtx.lattice.insert anchor states }

def setState
    (dfCtx : DataFlowContext)
    (anchor : LatticeAnchor)
    (f : State -> State)
    [AnalysisState State] : DataFlowContext :=
  let current := dfCtx.getOrMkState (State := State) anchor
  dfCtx.writeState anchor (f current)

def setStateAndUpdate
    (dfCtx : DataFlowContext)
    (anchor : LatticeAnchor)
    (f : State -> State × Bool)
    (irCtx : IRContext OpCode)
    [AnalysisState State] : DataFlowContext :=
  let current := dfCtx.getOrMkState (State := State) anchor
  let (state, changed) := f current
  let dfCtx := dfCtx.writeState anchor state
  if changed then
    AnalysisState.onUpdate state dfCtx irCtx
  else
    dfCtx

end DataFlowContext
-- =============================================================================== --

-- =============================== Fixpoint Solver =============================== --
partial def run (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext :=
  match dfCtx.workList.dequeue? with
  | none =>
    dfCtx
  | some ((point, analysisId), workList) =>
    let dfCtx := { dfCtx with workList := workList }
    match dfCtx.getAnalysis? analysisId with
    | some analysis =>
      let dfCtx := analysis.visit point dfCtx irCtx
      run dfCtx irCtx
    | none =>
      panic! s!"analysis {analysisId} is not registered in DataFlowContext"

def fixpointSolve (top : OperationPtr) (analyses : Array DataFlowAnalysis)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- init
  let mut dfCtx := DataFlowContext.empty
  
  -- Register analysis
  for analysis in analyses do
    dfCtx := dfCtx.insertAnalysis analysis
  
  -- Initialize analysis
  for analysis in analyses do
    dfCtx := analysis.init top dfCtx irCtx

  -- run
  run dfCtx irCtx
-- =============================================================================== --

end Veir
