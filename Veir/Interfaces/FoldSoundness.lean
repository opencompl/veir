module

public import Veir.Interfaces.FoldInterfaces
public import Veir.Interpreter.Refinement.Basic

import all Veir.Interfaces.FoldInterfaces
import all Veir.Interpreter.Evaluate
import Veir.Interpreter.Refinement.Lemmas
import all Veir.Data.LLVM.Int.Basic

/-!
# Fold soundness contract

`OpCode.foldsTo` decides that an operation folds. This file relates that
decision to `interpretOp'`, which is the project's only concrete semantics,
states the contract, and discharges it leg by leg.

The contract is stated against an interpreter *outcome* rather than a value.
-/

public section

namespace Veir

/-- The runtime value a fold decision claims for a result. -/
@[expose]
def FoldDecision.valueFor (decision : FoldDecision) (operands : Array RuntimeValue)
    : Option RuntimeValue :=
  match decision with
  | .useOperand j => operands[j]?
  | .useConstant value => some value

/-- Interpret an operation at empty memory, keeping only the result values. -/
@[expose]
def interpretPure (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    : Interp (Array RuntimeValue) :=
  (interpretOp' opType properties resultTypes operands #[] MemoryState.empty).map
    (fun (results, _, _) => results)

/-- `constOperands` agrees with the real operands wherever it claims a value. -/
@[expose]
def ConstOperandsAgree (constOperands : Array (Option RuntimeValue))
    (operands : Array RuntimeValue) : Prop :=
  ∀ (i : Nat) (v : RuntimeValue), constOperands[i]? = some (some v) → operands[i]? = some v

/--
The fold-soundness contract for one result, as a refinement.

Whenever the interpreter produces a value `actual` for result `i`, the decision
must name a value `claimed` that refines it (`actual ⊒ claimed`): the same value,
or, where `actual` is poison, any value of its type. `.ub` and `.fail` impose no
constraint: the source program's behaviour is unconstrained there, so replacing
it with any value — poison included — is likewise a refinement.
-/
@[expose]
def FoldDecision.SoundFor (decision : FoldDecision) (operands : Array RuntimeValue)
    (outcome : Interp (Array RuntimeValue)) (i : Nat) : Prop :=
  match outcome with
  | .ok results =>
      match results[i]? with
      | some actual => ∃ claimed, decision.valueFor operands = some claimed ∧ actual ⊒ claimed
      | none => True
  | .ub _ => True
  | .fail _ => True

/-- An integer poison is refined by every integer of its width. -/
theorem RuntimeValue.int_poison_isRefinedBy (w : Nat) (x : Data.LLVM.Int w) :
    RuntimeValue.int w .poison ⊒ RuntimeValue.int w x :=
  ⟨rfl, by simp [Data.LLVM.Int.cast]⟩

/-- Every fold decision is sound for UB. -/
@[simp]
theorem FoldDecision.soundFor_ub (decision : FoldDecision) (operands : Array RuntimeValue)
    (i : Nat) {op : Option OperationPtr} : decision.SoundFor operands (.ub op) i := by
  simp [FoldDecision.SoundFor]

/-- Every fold decision is sound for an interpreter failure. -/
@[simp]
theorem FoldDecision.soundFor_fail (decision : FoldDecision) (operands : Array RuntimeValue)
    (i : Nat) {op : Option OperationPtr} : decision.SoundFor operands (.fail op) i := by
  simp [FoldDecision.SoundFor]

/-- A successful `mapM` in `Option` computes each entry by `f`. -/
theorem List.getElem?_of_mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ∀ (i : Nat), xs[i]?.bind f = ys[i]?
  | [], ys, h, i => by
      simp at h; subst h; simp
  | x :: xs, ys, h, i => by
      cases hx : f x with
      | none => simp [hx] at h
      | some y =>
        cases hRest : xs.mapM f with
        | none => simp [hx, hRest] at h
        | some zs =>
          simp [hx, hRest] at h
          subst h
          cases i with
          | zero => simp [hx]
          | succ i => simpa using List.getElem?_of_mapM_eq_some hRest i

/-- A successful `mapM` in `Option` preserves length. -/
theorem List.length_of_mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], ys, h => by
      simp at h; subst h; rfl
  | x :: xs, ys, h => by
      cases hx : f x with
      | none => simp [hx] at h
      | some y =>
        cases hRest : xs.mapM f with
        | none => simp [hx, hRest] at h
        | some zs =>
          simp [hx, hRest] at h
          subst h
          simp [List.length_of_mapM_eq_some hRest]

/-- A successful `mapM` in `Option` preserves size. -/
theorem Array.size_of_mapM_eq_some {α β : Type} {f : α → Option β}
    {xs : Array α} {ys : Array β} (h : xs.mapM f = some ys) : ys.size = xs.size := by
  have hList := congrArg (·.map Array.toList) h
  simp only [Array.mapM_eq_mapM_toList, Functor.map, Option.map_map] at hList
  simp at hList
  simpa using List.length_of_mapM_eq_some hList

/-- A successful `mapM` in `Option` computes each entry by `f`. -/
theorem Array.getElem?_of_mapM_eq_some {α β : Type} {f : α → Option β}
    {xs : Array α} {ys : Array β} (h : xs.mapM f = some ys) (i : Nat) :
    xs[i]?.bind f = ys[i]? := by
  have hList := congrArg (·.map Array.toList) h
  simp only [Array.mapM_eq_mapM_toList, Functor.map, Option.map_map] at hList
  simp at hList
  simpa using List.getElem?_of_mapM_eq_some hList i

/--
When every entry of `constOperands` is known, and each agrees with `operands`,
the sequenced array is exactly `operands`.
-/
theorem ConstOperandsAgree.mapM_id_eq
    {constOperands : Array (Option RuntimeValue)} {operands values : Array RuntimeValue}
    (hAgree : ConstOperandsAgree constOperands operands)
    (hSize : constOperands.size = operands.size)
    (hValues : constOperands.mapM id = some values) :
    values = operands := by
  apply Array.ext_getElem?
  intro i
  have hEntry := Array.getElem?_of_mapM_eq_some hValues i
  cases hv : values[i]? with
  | none =>
      have hValuesSize := Array.size_of_mapM_eq_some hValues
      have hLt : ¬ i < operands.size := by
        intro hLt
        have : i < values.size := by omega
        simp [this] at hv
      simp [hLt]
  | some v =>
      refine (hAgree i v ?_).symm
      cases hc : constOperands[i]? with
      | none => simp [hc, hv] at hEntry
      | some c => simp_all

/-- A successful `foldEvaluate` agrees with the empty-memory interpretation. -/
theorem interpretPure_of_foldEvaluate_ok {opType : OpCode} {properties : propertiesOf opType}
    {resultTypes : Array TypeAttr} {operands results : Array RuntimeValue}
    (h : foldEvaluate opType properties resultTypes operands = .ok results) :
    interpretPure opType properties resultTypes operands = .ok results := by
  simp only [foldEvaluate] at h
  split at h
  · simp [liftM, monadLift, MonadLift.monadLift] at h
  · simp only [interpretPure]
    cases hInterp : interpretOp' opType properties resultTypes operands #[] MemoryState.empty with
    | fail _ => simp [hInterp, bind] at h
    | ub _ => simp [hInterp, bind] at h
    | ok triple =>
      obtain ⟨rs, mem, action⟩ := triple
      cases action <;> simp_all [bind, liftM, monadLift, MonadLift.monadLift]

/-- `foldEvaluate` reports UB only when the empty-memory interpretation does. -/
theorem interpretPure_of_foldEvaluate_ub {opType : OpCode} {properties : propertiesOf opType}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {op : Option OperationPtr}
    (h : foldEvaluate opType properties resultTypes operands = .ub op) :
    interpretPure opType properties resultTypes operands = .ub op := by
  simp only [foldEvaluate] at h
  split at h
  · simp [liftM, monadLift, MonadLift.monadLift] at h
  · simp only [interpretPure]
    cases hInterp : interpretOp' opType properties resultTypes operands #[] MemoryState.empty with
    | fail _ => simp [hInterp, bind] at h
    | ub _ => simp_all [bind]
    | ok triple =>
      obtain ⟨rs, mem, action⟩ := triple
      cases action <;> simp_all [bind, liftM, monadLift, MonadLift.monadLift]

/-- The evaluation leg: decisions produced by interpreting the operation are sound. -/
private theorem foldByEvaluation_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hSize : constOperands.size = operands.size)
    (hFold : foldByEvaluation opType properties resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  simp only [foldByEvaluation, bind, Option.bind] at hFold
  cases hValues : constOperands.mapM id with
  | none => simp [hValues] at hFold
  | some values =>
    have hEq := ConstOperandsAgree.mapM_id_eq hAgree hSize hValues
    subst hEq
    simp only [hValues] at hFold
    cases hEval : foldEvaluate opType properties resultTypes values with
    | fail _ => simp [hEval] at hFold
    | ub _ => simp [interpretPure_of_foldEvaluate_ub hEval]
    | ok results =>
      simp only [hEval, pure] at hFold
      cases hFold
      have hDecisionEq : decision = .useConstant results[i]! := by
        grind
      rw [interpretPure_of_foldEvaluate_ok hEval]
      simp only [FoldDecision.SoundFor]
      cases hResult : results[i]? with
      | none => trivial
      | some actual =>
        subst hDecisionEq
        simp [FoldDecision.valueFor]
        grind

/--
The `propagatesPoison` flag is sound for `opType`: whenever some operand is
wholly poison, interpretation either fails, is UB, or produces wholly poison
results of the declared types.

This is the semantic content the flag asserts. It is a per-opcode obligation:
nothing in `Veir/IR/OpInfo.lean` enforces it.
-/
@[expose]
def PropagatesPoisonSound (opType : OpCode) : Prop :=
  opType.propagatesPoison = true →
  ∀ (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (results : Array RuntimeValue),
    operands.any RuntimeValue.isPoison = true →
    interpretPure opType properties resultTypes operands = .ok results →
    ∀ (i : Nat) (actual : RuntimeValue), results[i]? = some actual →
      resultTypes[i]?.bind RuntimeValue.getPoisonForType = some actual

/--
The poison leg: poison-propagating folds are sound, given that the
`propagatesPoison` flag is (`PropagatesPoisonSound`).
-/
private theorem foldPoisonedOperand_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hPoison : PropagatesPoisonSound opType)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hFold : foldPoisonedOperand opType resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  simp only [foldPoisonedOperand] at hFold
  simp [guard, Option.bind_eq_some_iff] at hFold
  obtain ⟨hPropagates, ⟨j, hj, hConstPoison⟩, hFold⟩ := hFold
  have hOperandPoison : operands.any RuntimeValue.isPoison = true := by
    cases hc : constOperands[j] with
    | none => simp [hc] at hConstPoison
    | some value =>
      simp only [hc] at hConstPoison
      have hOp := hAgree j value (by simp [hj, hc])
      obtain ⟨hjOp, hOpEq⟩ := Array.getElem?_eq_some_iff.mp hOp
      exact Array.any_eq_true.mpr ⟨j, hjOp, by simp [hOpEq, hConstPoison]⟩
  simp only [allResultsPoison, bind, Option.bind, pure] at hFold
  cases hPoisons : resultTypes.mapM RuntimeValue.getPoisonForType with
  | none => simp [hPoisons] at hFold
  | some poisons =>
    simp only [hPoisons, Option.some.injEq] at hFold
    subst hFold
    have hEntry := Array.getElem?_of_mapM_eq_some hPoisons i
    simp only [Array.getElem?_map, Option.map_eq_some_iff] at hDecision
    obtain ⟨poison, hPoisonAt, rfl⟩ := hDecision
    cases hInterp : interpretPure opType properties resultTypes operands with
    | fail _ => trivial
    | ub _ => trivial
    | ok results =>
      simp only [FoldDecision.SoundFor]
      cases hResult : results[i]? with
      | none => trivial
      | some actual =>
        have := hPoison hPropagates properties resultTypes operands results hOperandPoison
          hInterp i actual hResult
        refine ⟨actual, ?_, RuntimeValue.isRefinedBy_refl actual⟩
        simp only [FoldDecision.valueFor]
        rw [← this, hEntry, hPoisonAt]

/--
The dialect fold table for `opType` satisfies the contract.

This is a per-dialect obligation. It is discharged for `arith` by
`Arith.tryFold_sound` in `Veir/Dialects/Arith/FoldProofs.lean`, and is open for
`llvm` and `riscv`, the other dialects that override `tryFold`.
-/
@[expose]
def FoldTableSound (opType : OpCode) : Prop :=
  ∀ (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision),
    ConstOperandsAgree constOperands operands →
    HasOpInfo.tryFold opType properties resultTypes constOperands = some decisions →
    decisions[i]? = some decision →
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i

/-- `preferredFold` returns one of its two arguments unchanged. -/
private theorem preferredFold_eq (first second : Option (Array FoldDecision)) :
    preferredFold first second = first ∨ preferredFold first second = second := by
  unfold preferredFold
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/--
Fold soundness for `OpCode.foldsTo`: every decision it returns refines the
value the interpreter produces, whenever the interpreter produces one.

`hTable` and `hPoison` are the per-opcode obligations of the dialect fold table
and of the `propagatesPoison` flag. `hAgree` and `hSize` say the constant
operands the caller supplies describe the real operands.
-/
theorem foldsTo_sound
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (constOperands : Array (Option RuntimeValue))
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hTable : FoldTableSound opType)
    (hPoison : PropagatesPoisonSound opType)
    (hAgree : ConstOperandsAgree constOperands operands)
    (hSize : constOperands.size = operands.size)
    (hFold : OpCode.foldsTo opType properties resultTypes constOperands = some decisions)
    (hDecision : decisions[i]? = some decision) :
    decision.SoundFor operands (interpretPure opType properties resultTypes operands) i := by
  simp only [OpCode.foldsTo] at hFold
  cases hPoisonFold : foldPoisonedOperand opType resultTypes constOperands with
  | some poisonDecisions =>
    have hEq : decisions = poisonDecisions := by
      cases hConst : opType.isConstantLike <;> simp_all [guard, bind, Option.bind]
    subst hEq
    exact foldPoisonedOperand_sound opType properties resultTypes operands constOperands
      decisions i decision hPoison hAgree hPoisonFold hDecision
  | none =>
    have hPreferred : preferredFold (foldByTable opType properties resultTypes constOperands)
        (foldByEvaluation opType properties resultTypes constOperands) = some decisions := by
      cases hConst : opType.isConstantLike <;> simp_all [guard, bind, Option.bind]
    rcases preferredFold_eq (foldByTable opType properties resultTypes constOperands)
        (foldByEvaluation opType properties resultTypes constOperands) with h | h <;>
      rw [h] at hPreferred
    · exact hTable properties resultTypes operands constOperands decisions i decision
        hAgree hPreferred hDecision
    · exact foldByEvaluation_sound opType properties resultTypes operands constOperands
        decisions i decision hAgree hSize hPreferred hDecision

end Veir
