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
Unfold `OpCode.ResultsConform` onto the `CTree.interpretOp'` of the opcode and the `!`-accessors of
the operation, which is the form a dialect proves.
-/
theorem OpCode.resultsConform_def! {opType : OpCode} :
    opType.ResultsConform ↔
      ∀ (ctx : WfIRContext OpCode) (op : OperationPtr) (opIn : op.InBounds ctx.raw),
        op.getOpType! ctx.raw = opType →
        op.Verified ctx opIn →
        ∀ (operands : Array RuntimeValue) (mem : MemoryState),
          RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw) →
          ∀ (results : Array RuntimeValue) (mem' : MemoryState) (act : Option ControlFlowAction),
            CTree.MayReturn (CTree.interpretOp' opType (op.getProperties! ctx.raw opType)
              (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) mem
              (op.getRegions! ctx.raw)) (results, mem', act) →
            RuntimeValue.ArrayConforms results (op.getResultTypes! ctx.raw) := by
  refine resultsConform_def.trans ⟨fun h ctx op opIn hType => ?_, fun h ctx op opIn hType => ?_⟩
  · subst hType
    simpa only [OperationPtr.interpretCTree_def!] using
      h ctx op opIn (OperationPtr.getOpType!_eq_getOpType opIn).symm
  · have hType! := (OperationPtr.getOpType!_eq_getOpType opIn).trans hType
    subst hType!
    simpa only [OperationPtr.interpretCTree_def!] using h ctx op opIn rfl

/--
Values, as many as the operation has results, conform to the result types of the operation when
each conforms to the type of its result.
-/
theorem RuntimeValue.ArrayConforms.of_getResult {OpInfo : Type} [HasOpInfo OpInfo]
    {ctx : WfIRContext OpInfo} {op : OperationPtr} {vals : Array RuntimeValue}
    (hs : vals.size = op.getNumResults! ctx.raw)
    (h : ∀ i (hi : i < vals.size), vals[i].Conforms ((op.getResult i).getType! ctx.raw)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  refine ⟨by rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hs], fun i hi => ?_⟩
  rw [getElem!_pos vals i hi, OperationPtr.getResultTypes!.getElem!_eq (hs ▸ hi)]
  exact h i hi

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
