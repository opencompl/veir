module

public import Veir.Verifier
public import Veir.Interpreter.CTreeInterpreter

public section

/-!
# Interpreted verified operation results conform to their types
-/

open CTree

namespace Veir

/--
Assert for a given opcode that a verified operation matching this opcode only yields results that
conform to the types its verifier permits.
-/
def OpCode.ResultsConform (opType : OpCode) : Prop :=
  ∀ (ctx : WfIRContext OpCode) (op : OperationPtr) (opIn : op.InBounds ctx.raw),
    op.getOpType ctx.raw opIn = opType →
    op.Verified ctx opIn →
    ∀ (operands : Array RuntimeValue) (mem : MemoryState),
      RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw) →
      ∀ (results : Array RuntimeValue) (mem' : MemoryState) (act : Option ControlFlowAction),
        CTree.MayReturn (op.interpretCTree opIn operands mem) (results, mem', act) →
        RuntimeValue.ArrayConforms results (op.getResultTypes! ctx.raw)

/-- Unfold `OpCode.resultsConform`. -/
theorem OpCode.resultsConform_def {opType : OpCode} :
    opType.ResultsConform ↔
      ∀ (ctx : WfIRContext OpCode) (op : OperationPtr) (opIn : op.InBounds ctx.raw),
        op.getOpType ctx.raw opIn = opType →
        op.Verified ctx opIn →
        ∀ (operands : Array RuntimeValue) (mem : MemoryState),
          RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw) →
          ∀ (results : Array RuntimeValue) (mem' : MemoryState) (act : Option ControlFlowAction),
            CTree.MayReturn (op.interpretCTree opIn operands mem) (results, mem', act) →
            RuntimeValue.ArrayConforms results (op.getResultTypes! ctx.raw) :=
  Iff.rfl

/--
`ResultsConform opType` holds when every verified operation of opcode `opType` only yields results
that conform to its declared result types, as `OpCode.ResultsConform` states it.
-/
class ResultsConform (opType : OpCode) : Prop where
  conform : opType.ResultsConform

/--
Every result a verified operation's CTree can produce conforms to the operation's declared
`resultTypes`.
-/
theorem interpretCTree_results_conform {op : OperationPtr} {ctx : WfIRContext OpCode}
    {opIn : op.InBounds ctx.raw}
    (conform : (op.getOpType ctx.raw opIn).ResultsConform)
    (opVerif : op.Verified ctx opIn)
    (conforms : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : CTree.MayReturn (op.interpretCTree opIn operands mem) (results, mem', act)) :
    RuntimeValue.ArrayConforms results (op.getResultTypes! ctx.raw) :=
  OpCode.resultsConform_def.mp conform
    ctx op opIn rfl opVerif operands mem conforms results mem' act h

end Veir

end
