import Veir.Rewriter
import Veir.WellFormedness.WellFormed
import Veir.WellFormedness.Rewriter

abbrev OpCode.module := 0
abbrev OpCode.constant := 1
abbrev OpCode.addi := 2
abbrev OpCode.muli := 4
abbrev OpCode.test := 99

open Veir

structure addIZeroFolding_matchingCondition (ctx: IRContext) (op: OperationPtr) (lhsValue: ValuePtr) (rhsPtr: OperationPtr) : Prop where
  opIsAdd : op.getOpType ctx sorry = OpCode.addi
  rhsOpIsCst : rhsPtr.getOpType ctx sorry = OpCode.constant
  rhsOpIsZero : (rhsPtr.get ctx (by sorry)).properties = 0
  rhsIsRhs : op.getOperand ctx (by sorry) 1 (by sorry) = ValuePtr.opResult (OpResultPtr.mk rhsPtr 0)
  lhsIsLhs : op.getOperand ctx (by sorry) 0 (by sorry) = lhsValue


def addIZeroFolding (ctx: IRContext) (op: OperationPtr) : Option IRContext := do
  if op.getOpType ctx sorry ≠ OpCode.addi then
    return ctx

  -- Get the rhs and check that it is the constant 0
  let rhsValuePtr := op.getOperand ctx (by sorry) 1 (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  if rhsOp.getOpType ctx (by sorry) ≠ OpCode.constant then
    return ctx
  let rhsOpStruct := rhsOp.get ctx (by sorry)
  if rhsOpStruct.properties ≠ 0 then
    return ctx

  -- Get the lhs value
  let lhsValuePtr := op.getOperand ctx (by sorry) 0 (by sorry)

  let oldVal := op.getResult ctx (by sorry) 0 (by sorry)
  let mut ctx ← Rewriter.replaceValue? ctx oldVal lhsValuePtr sorry sorry sorry
  ctx ← Rewriter.eraseOp ctx sorry op sorry sorry
  return ctx

@[grind]
def AddWF (ctx: IRContext) : Prop :=
  ∀ op opInBounds,
    OperationPtr.getOpType op ctx opInBounds = OpCode.addi →
    (OperationPtr.get op ctx opInBounds).results.size = 1 ∧
    (OperationPtr.get op ctx opInBounds).operands.size = 2

@[grind]
def ConstantWF (ctx: IRContext) : Prop :=
  ∀ op opInBounds,
    OperationPtr.getOpType op ctx opInBounds = OpCode.constant →
    (OperationPtr.get op ctx opInBounds).results.size = 1 ∧
    (OperationPtr.get op ctx opInBounds).operands.size = 0

theorem onlyChangeWhenMatches :
    AddWF ctx →
    ConstantWF ctx →
    addIZeroFolding ctx op = some ctx' →
    ctx = ctx' ∨ ∃ lhs rhs, addIZeroFolding_matchingCondition ctx op lhs rhs := by
  intros addWF cstWF h
  simp only [addIZeroFolding] at h
  split at h; any_goals grind
  simp only [Option.pure_def, ne_eq, Option.isNone_iff_eq_none, Option.bind_eq_bind,
    Option.bind_some, Option.bind_fun_some, ite_not, Option.bind_none] at h
  split at h; any_goals grind
  split at h; any_goals grind
  split at h; any_goals grind
  rename_i lhs rhs _ _ _
  right
  exists op.getOperand ctx (by grind) 0 (by grind)
  exists rhs.op
  constructor <;> try grind
  · have : (op.getOperand ctx (by grind) 1 (by grind)).InBounds ctx := by grind
    have : rhs.InBounds ctx := by grind
    simp only [AddWF] at addWF
    have := addWF op (by grind) (by grind)
    have : rhs.index = 0 := by sorry -- small lemma missing
    cases rhs <;> grind

theorem matchesMeansChange :
    AddWF ctx →
    ConstantWF ctx →
    addIZeroFolding_matchingCondition ctx op lhs rhs →
    addIZeroFolding ctx op = some ctx' →
    ctx ≠ ctx' := by
  intros addWF cstWF h
  simp only [addIZeroFolding]
  simp only [h.opIsAdd, ne_eq, not_true_eq_false, ↓reduceIte, Option.pure_def, h.rhsIsRhs,
    h.lhsIsLhs, Option.bind_eq_bind, Option.bind_some,
    Option.bind_fun_some, ite_not, h.rhsOpIsCst, h.rhsOpIsZero]
  intros hctx'
  -- Should be easy proof, need 1-2 theorems for it but that's fine
  sorry

theorem matchesMeansChangeo :
    IRContext.WellFormed ctx →
    AddWF ctx →
    ConstantWF ctx →
    addIZeroFolding_matchingCondition ctx op lhs rhs →
    addIZeroFolding ctx op = some ctx' →
    ∀ (otherOp : OperationPtr) otherOpInBounds operandInBounds, otherOp ≠ op →
      otherOp.getOperand ctx' otherOpInBounds 0 operandInBounds =
      let operand := otherOp.getOperand ctx (by sorry) 0 (by sorry) --small lemmas about the rewrite for them
      if operand = ValuePtr.opResult (OpResultPtr.mk op 0) then
        lhs
      else
        operand
       := by
  intros ctxWf addWf cstWf h
  simp only [addIZeroFolding]
  simp only [h.opIsAdd, ne_eq, not_true_eq_false, ↓reduceIte, Option.pure_def, h.rhsIsRhs,
    h.lhsIsLhs, Option.bind_eq_bind, Option.bind_some,
    Option.bind_fun_some, ite_not, h.rhsOpIsCst, h.rhsOpIsZero]
  intros hctx' otherOp otherOpInBounds operandInBounds hne
  simp only [Option.bind_eq_some_iff] at hctx'
  have ⟨ctx'₂, ⟨hctx'₂, hctx'⟩⟩ := hctx'
  simp only [Option.some.injEq] at hctx'
  simp (disch := grind) only [OperationPtr.getOperand_Rewriter_eraseOp hctx']
  rw [OperationPtr.getOperand_replaceValue? ctxWf hctx'₂] <;> try grind
  · grind [OperationPtr.getResult]
  · intros hlhs
    subst lhs
    cases h
    sorry -- prove this with 1-2 small lemmas
