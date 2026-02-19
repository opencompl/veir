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

structure DataFlowAnalysis where
  ctx : Type
  init : OperationPtr -> ctx -> ctx

-- ================================== WorkList =================================== -- 
def WorkItem := ProgramPoint × DataFlowAnalysis
def WorkList := Queue WorkItem
-- =============================================================================== -- 

structure DependentPtr where
  id: Nat
  deriving BEq, Hashable

structure DataFlowContext where
  workList : Queue (ProgramPoint × DataFlowAnalysis) 
  dependents : HashMap DependentPtr WorkItem

-- ================================ AnalysisState ================================ -- 
-- Lattice Elements are stored in structures that implement the `Update` typeclass.
-- These structures contain a `BaseAnalysisState` along with anything else it needs.
-- `AnalysisState` is used to allow for dynamic dispatch (runtime polymorphism).
class Update (α : Type) where
  onUpdate : α -> DataFlowContext -> DataFlowContext 

structure BaseAnalysisState where
  anchor : LatticeAnchor
  dependents : Array DependentPtr 

instance : Update BaseAnalysisState where
  onUpdate (state : BaseAnalysisState) (ctx : DataFlowContext) : DataFlowContext := Id.run do
    let mut ctx := ctx 
    for ptr in state.dependents do
      let workItem := sorry --(ctx.dependents.get! ptr) 
      ctx := {ctx with workList := ctx.workList.enqueue workItem}
    ctx 

structure AnalysisState where
  impl : Type
  inst : Update impl
-- =============================================================================== -- 

def Lattice := HashMap LatticeAnchor AnalysisState 

def fixpointSolve (top: OperationPtr) (analyses : Array DataFlowAnalysis) : LatticeContext :=
  let latticeCtx : LatticeContext := sorry
  sorry

end Veir
