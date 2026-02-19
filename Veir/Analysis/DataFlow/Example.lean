module

public import Veir.Analysis.DataFlowFramework

public section

namespace Veir

inductive ChangeResult where
  | change
  | noChange

class Join (α : Type) where
  join : α -> α -> α  

class Meet (α : Type) where
  meet : α -> α -> α  

structure ConstantValue where
  constant: Option Nat 

instance : Join ConstantValue where
  join (lhs rhs : ConstantValue) : ConstantValue :=
    if lhs.constant.isNone then
      rhs
    else if rhs.constant.isNone then
      lhs
    else if lhs.constant == rhs.constant then
      lhs
    else
      ⟨ none ⟩ 

-- ====================== Example `AnalysisState` Children ======================= -- 
structure AbstractSparseLatticeState extends BaseAnalysisState where
  useDefSubscribers : Array DataFlowAnalysis

instance : Update AbstractSparseLatticeState DataFlowContext where
  onUpdate (state: AbstractSparseLatticeState) (ctx : DataFlowContext) : DataFlowContext := Id.run do
    let mut ctx := {ctx with workList := state.onUpdate ctx}
    -- Do some other stuff...
    ctx

structure LatticeState extends AbstractSparseLatticeState where
  ValueT : Type
  value : ValueT
  join : Join ValueT 

instance : Update LatticeState DataFlowContext where
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

end Veir
