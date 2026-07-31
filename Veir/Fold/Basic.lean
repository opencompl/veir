module

public import Veir.Interpreter.RuntimeValue

public section

namespace Veir

/--
  The decision of whether and how an operation folds. Folding is currently
  restricted to operations with exactly one result.
-/
inductive FoldDecision where
  /-- Use operand `j` in place of the result. -/
  | useOperand (j : Nat)
  /-- Use the runtime constant `rv` in place of the result. -/
  | useConstant (rv : RuntimeValue)
  /-- The operation does not fold with the supplied operand information. -/
  | noFold

namespace Fold

/-- Construct a poison decision for a supported result type. -/
def poisonDecision (resultTypes : Array TypeAttr) : FoldDecision :=
  match resultTypes[0]? with
  | some resultType =>
    match resultType.val with
    | .integerType intTy => .useConstant (.int intTy.bitwidth .poison)
    | _ => .noFold
  | none => .noFold

/--
  Partial folds shared by `arith.select` and `llvm.select`.

  Besides a known condition, this handles poison arms, the boolean
  `select %c, true, false`, and equal known integer arms. Each case depends
  only on the select itself and its supplied constant operands.
-/
def selectFoldsTo (resultTypes : Array TypeAttr)
    (constOperands : Array (Option RuntimeValue)) : FoldDecision :=
  match constOperands.toList with
  | [some (.int 1 (.val c)), _, _] =>
    if c = 1 then .useOperand 1 else .useOperand 2
  | [some (.int 1 .poison), _, _] => poisonDecision resultTypes
  | [_, some (.int _ .poison), _] => .useOperand 2
  | [_, _, some (.int _ .poison)] => .useOperand 1
  | [_, some (.int 1 (.val t)), some (.int 1 (.val f))] =>
    if t = 1 ∧ f = 0 then .useOperand 0
    else if t = f then .useConstant (.int 1 (.val t))
    else .noFold
  | [_, some (.int bw lhs), some (.int bw' rhs)] =>
    if h : bw' ≠ bw then .noFold else
    let rhs := rhs.cast (by simp at h; exact h)
    if lhs = rhs then .useConstant (.int bw lhs) else .noFold
  | [_, some (.byte bw lhs), some (.byte bw' rhs)] =>
    if h : bw' ≠ bw then .noFold else
    let rhs := rhs.cast (by simp at h; exact h)
    if lhs = rhs then .useConstant (.byte bw lhs) else .noFold
  | [_, some (.float bw lhs), some (.float bw' rhs)] =>
    if bw = bw' ∧ lhs.toBits = rhs.toBits then
      .useConstant (.float bw lhs)
    else .noFold
  | [_, some (.addr lhs), some (.addr rhs)] =>
    if lhs = rhs then .useConstant (.addr lhs) else .noFold
  | [_, some (.reg lhs), some (.reg rhs)] =>
    if lhs = rhs then .useConstant (.reg lhs) else .noFold
  | _ => .noFold

end Fold

end Veir
