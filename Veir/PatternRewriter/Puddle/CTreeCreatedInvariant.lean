module

public import Veir.PatternRewriter.Puddle.CTreeModuleSoundness
public import Veir.Interpreter.CTreeEntryInvariant
import all Veir.PatternRewriter.Puddle.CreationCheckedSemantics
import all Veir.Interpreter.CTree

public section
namespace Veir.Puddle.CTree

/-- Executing the actual linked creation batch keeps all dominating target values available
at its successor, using the checked result installations performed by the interpreter. -/
theorem interpretCreatedOpsChecked_definesDominatingIn
    {ctx : WfIRContext OpCode} (ops : List OperationPtr) (first next : OperationPtr)
    {block : BlockPtr} {region : RegionPtr} {state final : InterpreterState ctx}
    (starts : ops.head? = some first)
    (bounds : ∀ op ∈ ops, op.InBounds ctx.raw)
    (parents : ∀ op ∈ ops, op.getParent! ctx.raw = some block)
    (blockParent : block.getParent! ctx.raw = some region)
    (chain : ForwardChain ctx.raw ops (some next))
    (defined : state.DefinesDominatingIn region (.before first))
    (outcome : PureOrErr.CanInterpretTo (interpretCreatedOpsChecked ctx ops state) (.ok final)) :
    final.DefinesDominatingIn region (.before next) := by
  induction ops generalizing first state with
  | nil => simp at starts
  | cons op ops ih =>
    have equal : op = first := by simpa using starts
    subst first
    have opIn := bounds op (by simp)
    have opParent := parents op (by simp)
    simp only [interpretCreatedOpsChecked, opIn, dite_true] at outcome
    obtain ⟨⟨middle, action⟩, head, tail⟩ :=
      (PureOrErr.CanInterpretTo.bind_iff _ _ _).mp outcome |>.resolve_right (by simp)
    obtain ⟨operands, raw, _, _, installed, _, _⟩ :=
      interpretOpCore_outcome op opIn state (middle, action) head
    have after : middle.DefinesDominatingIn region (InsertPoint.after op ctx.raw block) :=
      InterpreterState.DefinesDominatingIn.setResultValues defined opParent blockParent installed
    cases ops with
    | nil =>
      have nextEq : op.getNextOp! ctx.raw = some next := chain
      have equal := PureOrErr.CanInterpretTo.pure_iff _ _ |>.mp tail
      cases equal
      simpa only [InsertPoint.after_eq_of_some_next nextEq] using after
    | cons second rest =>
      have nextEq : op.getNextOp! ctx.raw = some second := chain.1
      apply ih second rfl
        (fun current member => bounds current (by simp [member]))
        (fun current member => parents current (by simp [member])) chain.2 ?_ tail
      simpa only [InsertPoint.after_eq_of_some_next nextEq] using after

end Veir.Puddle.CTree
