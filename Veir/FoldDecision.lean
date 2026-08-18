module

public import Veir.RuntimeValue

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

/--
Return a poison constant when at least one known operand is wholly poison and
the single result type has a poison representation.
-/
def FoldDecision.propagatePoison (resultTypes : Array TypeAttr)
    (constantOperands : Array (Option RuntimeValue)) : Option FoldDecision := do
  guard (constantOperands.any fun
    | some value => value.isPoison
    | none => false)
  let #[resultType] := resultTypes | none
  return .useConstant (← RuntimeValue.getPoisonForType resultType)

end

end Veir
