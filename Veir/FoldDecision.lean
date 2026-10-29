module

public import Veir.Interpreter.RuntimeValue.Basic

/-!
  # Fold decisions

  The result of deciding that an operation folds. This lives in its own file so
  that `HasOpInfo`, and therefore every dialect's fold table, can refer to it
  without depending on the folding machinery built on top of it.
-/

namespace Veir

public section

/-- What an operation folds to, when it folds at all. -/
inductive FoldDecision where
  /-- Use operand `j` in place of the result. -/
  | useOperand (j : Nat)
  /-- Use the runtime constant `rv` in place of the result. -/
  | useConstant (rv : RuntimeValue)

/-- A single-result fold to operand `j`, when `condition` holds. -/
@[expose] def FoldDecision.useOperandIf (condition : Bool) (j : Nat) : Option (Array FoldDecision) :=
  if condition then some #[.useOperand j] else none

/-- A single-result fold to the constant `rv`, when `condition` holds. -/
@[expose] def FoldDecision.useConstantIf (condition : Bool) (rv : RuntimeValue) :
    Option (Array FoldDecision) :=
  if condition then some #[.useConstant rv] else none

end

end Veir
