module

public import Veir.Interpreter.CTree.Basic

public section

open CTree

namespace Veir.CTreeInterpreter

/-- Consume a finite approximation while owning the SSA store outside all tree
continuations. A read borrows the store; a write consumes it. Only explicit
scope entry saves an older store, so flat execution permits in-place updates.
Fuel counts observed nodes, including SSA events and freeze choices. -/
private def runApprox {ctx : WfIRContext OpCode} (fuel : Nat)
    (tree : CTreeN (SSAE ctx ⊕ₑ ErrorE ⊕ₑ UBE) FreezeC α fuel)
    (variables : VariableState ctx) (scopes : List (VariableState ctx))
    : Except String (Interp α) :=
  match fuel with
  | 0 => .error "CTree interpreter exhausted its fuel"
  | n + 1 => match tree with
    | .ret value =>
      if scopes.isEmpty then .ok (.ok value) else .ok .fail
    | .tau (.inl .c1) k => runApprox n (k ⟨⟩) variables scopes
    | .tau (.inr ⟨bw⟩) k => runApprox n (k (0 : BitVec bw)) variables scopes
    | .vis (.inr (.inl _)) _ => .ok .fail
    | .vis (.inr (.inr _)) _ => .ok .ub
    | .vis (.inl event) k => match event with
      | .readOperands op =>
        if _h : op.InBounds ctx.raw then
          match variables.getOperandValues op with
          | none => .ok .fail
          | some values => runApprox n (k values) variables scopes
        else .ok .fail
      | .writeResults op values =>
        if h : op.InBounds ctx.raw then
          match variables.setResultValues? op values h with
          | none => .ok .fail
          | some variables => runApprox n (k ()) variables scopes
        else .ok .fail
      | .writeArguments block values =>
        if h : block.InBounds ctx.raw then
          if values.size != block.getNumArguments! ctx.raw then .ok .fail
          else match variables.setArgumentValues? block values h with
          | none => .ok .fail
          | some variables => runApprox n (k ()) variables scopes
        else .ok .fail
      | .enterScope inherit =>
        let next := if inherit then variables else .empty ctx
        runApprox n (k ()) next (variables :: scopes)
      | .leaveScope => match scopes with
        | [] => .ok .fail
        | saved :: scopes => runApprox n (k ()) saved scopes

/-- Execute against a fresh, exclusively owned SSA store. Choose zero for LLVM
freeze, as the normal interpreter does. Return failure/UB distinctly from fuel
exhaustion. The tree is reusable: each invocation gets independent state. -/
def run {ctx : WfIRContext OpCode} (fuel : Nat) (tree : Tree ctx α)
    : Except String (Interp α) :=
  runApprox fuel (tree.approx fuel) (.empty ctx) []

end Veir.CTreeInterpreter
