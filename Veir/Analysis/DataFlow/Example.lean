module

public import Veir.Analysis.DataFlowFramework

public section

namespace Veir

inductive ChangeResult where
  | change
  | noChange

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

instance : Update LatticeState DataFlowContext where
  onUpdate state ctx :=
    Update.onUpdate
      state.toAbstractSparseLatticeState
      ctx

namespace LatticeState

def join (lhs : LatticeState) (rhs : AbstractSparseLatticeState) : ChangeResult :=
  sorry

end LatticeState
-- =============================================================================== -- 

-- ===================== Example `DataFlowAnalysis` Children ===================== -- 
def ConstantAnalysis.init (top : OperationPtr) (ctx : DataFlowContext) : DataFlowContext :=
  sorry

def ConstantAnalysis.visit (point : ProgramPoint) (ctx : DataFlowContext) : DataFlowContext :=
  sorry

def ConstantAnalysis := DataFlowAnalysis.new ConstantAnalysis.init ConstantAnalysis.visit
-- =============================================================================== -- 

end Veir
