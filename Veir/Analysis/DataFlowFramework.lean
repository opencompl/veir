module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Init.Data.Queue
public import Veir.IR.Basic

open Std(HashSet)
open Std(HashMap)
open Std(Queue)

namespace Veir

inductive ChangeResult where
  | noChange
  | change
deriving BEq

abbrev ProgramPoint := OperationPtr

structure WorkItem where 
  α : Type
  value : α 
  point : ProgramPoint

inductive LatticeAnchor where
  | point (point : ProgramPoint)
  | value (value : ValuePtr)
  deriving BEq, Hashable, Inhabited

structure AnalysisState where
  anchor: LatticeAnchor
  dependents: Array WorkItem
deriving Inhabited

structure DataFlowCtx where
  analysisStates : HashMap LatticeAnchor AnalysisState
  workList : Queue WorkItem

class DataFlowAnalysis (α : Type) where
  init : α -> OperationPtr -> DataFlowCtx -> DataFlowCtx 
  visit : α -> ProgramPoint -> DataFlowCtx -> DataFlowCtx 

structure AnyAnalysis where
  α : Type
  value : α
  impl : DataFlowAnalysis α

def DataFlowCtx.addDependency (ctx: DataFlowCtx) (state : AnalysisState) (dependent : ProgramPoint) (analysis : α) : DataFlowCtx := 
  let state := {state with dependents := state.dependents.push ⟨ α, analysis, dependent ⟩ }  
  let analysisStates := ctx.analysisStates.insert state.anchor state
  {ctx with analysisStates := analysisStates}

def DataFlowCtx.propagateIfChanged (ctx : DataFlowCtx) (state : AnalysisState) (changed : ChangeResult) : DataFlowCtx := Id.run do  
  match changed with 
    | .change =>
      let mut ctx := ctx
      for item in state.dependents do
        ctx := { ctx with workList := ctx.workList.enqueue item }
      ctx
    | .noChange => ctx 

def DataFlowCtx.getOrCreate (ctx : DataFlowCtx) (anchor : LatticeAnchor) : AnalysisState × DataFlowCtx := 
  if ctx.analysisStates.contains anchor then
    ⟨ ctx.analysisStates.get! anchor, ctx ⟩
  else
    let ctx := { ctx with analysisStates := ctx.analysisStates.insert anchor ⟨ anchor, #[] ⟩ } 
    ⟨ ctx.analysisStates.get! anchor, ctx ⟩

def DataFlowCtx.initializeAndRun (ctx : DataFlowCtx) (top : OperationPtr) (analyses: Array AnyAnalysis) : DataFlowCtx := Id.run do
  let mut ctx := ctx
  for (analysis : AnyAnalysis) in analyses do
    ctx := analysis.impl.init analysis.value top ctx
  while !ctx.workList.isEmpty do
    match ctx.workList.dequeue? with
    | none => break
    | some res => 
      ctx := {ctx with workList := res.2 }
      let workItem := res.1
      let analysis := DataFlowAnalysis workItem.α 
      ctx := DataFlowAnalysis.visit workItem.value top ctx 
    panic! "not done" 
  ctx

end Veir
