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

class DataFlowAnalysis (ctx : Type) where
  impl : Type
  init : impl -> OperationPtr -> ctx -> ctx

-- ================================== WorkList =================================== -- 
def WorkItem := ProgramPoint × DataFlowAnalysis
def WorkList := Queue WorkItem
-- =============================================================================== -- 

-- ================================ AnalysisState ================================ -- 
-- Lattice Elements are stored in structures that implement the `Update` typeclass.
-- These structures contain a `BaseAnalysisState` along with anything else it needs.
-- `AnalysisState` is used to allow for dynamic dispatch (runtime polymorphism).
class Update (α : Type) where
  onUpdate : α -> WorkList -> WorkList 

structure BaseAnalysisState where
  anchor : LatticeAnchor
  dependents : Array WorkItem

instance : Update BaseAnalysisState where
  onUpdate (state : BaseAnalysisState) (workList : WorkList) : WorkList := Id.run do
    let mut workList := workList
    for workItem in state.dependents do
      workList := workList.enqueue workItem
    workList 

structure AnalysisState where
  impl : Type
  inst : Update impl
-- =============================================================================== -- 

def LatticeContext := HashMap LatticeAnchor AnalysisState 

def fixpointSolve (top: OperationPtr) (analyses : Array DataFlowAnalysis) : LatticeContext :=
  let latticeCtx : LatticeContext := sorry
  sorry

end Veir
