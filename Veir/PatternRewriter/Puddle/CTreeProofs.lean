module

public meta import Lean
public import Veir.IR.Simp
public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTree
import all Veir.IR.Attribute
import all Veir.Data.Refinement
import Veir.PatternRewriter.Puddle.Definitions
import Veir.PatternRewriter.Puddle.Validity

/-!
# Proving CTree validity of Puddle patterns

Shared support for the proofs of `Puddle.CTree.Pattern.Valid` for the patterns of a pass. A proof
normalizes the pattern's semantics with `simpPuddleValid` and `simpPatternSemantics`, splits the
matched inputs and substitutes the results of matched operations with `normalizePatternValid`, and
closes the remaining value goal with the pattern's local correctness lemma
(`provePatternValid using`). `probePatternValid` prints the normalized goals, from which the local
lemmas are stated.

A pass's registry of patterns is certified either by `Certificates`, indexed by a list of patterns,
or by a `Status` for every pattern a registry function can return.
-/

namespace Veir.Puddle.CTree

open _root_.CTree

public section

/-- Bind a type equation introduced by a `TypeAttr` matcher.
Copied from `math-fehr/puddle-ctree-wip` (`InstructionSelection/Proofs/Utils.lean`). -/
@[simp, ctree_semantics]
theorem TypeAttr.forall_of_eq_imp_iff {T : Type} [IsTypeAttr T] {P : TypeAttr → T → Prop} :
    (∀ (type : TypeAttr) (x : T), TypeAttr.of T x = type → P type x) ↔
      (∀ (x : T), P (TypeAttr.of T x) x) := by
  grind

/-- Expose the outcome of an `Interp` computation forming the entire source tree.
Copied from `math-fehr/puddle-ctree-wip` (`InstructionSelection/Proofs/Utils.lean`), where it is
tagged `ctree_semantics`. Here it is passed explicitly by `simpPatternSemantics`, because some
proofs (e.g. of stores) must keep the source lifted. -/
theorem Sim.bind_monadLift_right_iff {EIn : Type} {E : EIn → Type}
    [HasUB EIn] [ErrorE -< E] [UBE -< E]
    {CIn C'In : Type} {C : CIn → Type} {C' : C'In → Type}
    {α β : Type} (relation : α → β → Prop)
    (other : CTree E C α) (func : Interp β) :
    CTree.Sim relation other (monadLift func : CTree E C' β) ↔
      match func with
      | .ok value => CTree.Sim relation other (pure value : CTree E C' β)
      | .ub _ => CTree.Sim relation other (ub : CTree E C' β)
      | .fail _ => CTree.Sim relation other (fail : CTree E C' β) := by
  cases func <;> rfl

/-- A lifted failing source is simulated by any target. -/
@[simp]
theorem sim_monadLift_fail_right {α β : Type} (R : α → β → Prop) (target : Tree α)
    (location : Option OperationPtr) :
    CTree.Sim R target (monadLift (Interp.fail location : Interp β) : Tree β) := by
  simp [monadLift, MonadLift.monadLift]

/-- A lifted source with undefined behavior is simulated by any target. -/
@[simp]
theorem sim_monadLift_ub_right {α β : Type} (R : α → β → Prop) (target : Tree α)
    (location : Option OperationPtr) :
    CTree.Sim R target (monadLift (Interp.ub location : Interp β) : Tree β) := by
  simp [monadLift, MonadLift.monadLift]

/-- A failing tree has no successful outcome, so a matched operation whose semantics fail is not
matched. -/
@[simp]
theorem PureOrErr.canInterpretTo_fail_ok {EIn CIn R} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E] (v : R) :
    PureOrErr.CanInterpretTo (fail : CTree E C R) (.ok v) ↔ False := by
  simp [Veir.fail, CTree.trigger_def, Bind.bind, CTree.CTree.bind_vis]

end

open Lean Meta in
/-- Case-split, recursively in every resulting goal, each local runtime value `v` that has a
hypothesis `v.Conforms _`. These are the matched input values; the results of matched
operations are then fixed by their interpretation equations. -/
meta partial def casesConformingValues (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type ← instantiateMVars decl.type
      unless type.isAppOfArity ``RuntimeValue.Conforms 2 do continue
      let .fvar value := type.appFn!.appArg! | continue
      let subgoals ← goal.cases value
      return (← subgoals.toList.mapM fun subgoal => casesConformingValues subgoal.mvarId).flatten
    return [goal]

open Lean Elab Tactic in
/-- Case-split every matched input value of a normalized Puddle validity goal. -/
elab "casesConformingValues" : tactic => do
  let goals ← getGoals
  setGoals (← goals.flatMapM fun goal => casesConformingValues goal)

/-- A width guard `W ≤ w` of an extension is false for a matched width `w < W`. -/
public theorem le_eq_false_of_lt {w W : Nat} (h : w < W) : (W ≤ w) = False := by
  simp only [eq_iff_iff, iff_false, Nat.not_le]
  exact h

/-- A guard `a < b` is false when `b ≤ a`, e.g. after the other branch of a split guard. -/
public theorem lt_eq_false_of_le {a b : Nat} (h : b ≤ a) : (a < b) = False := by
  simp only [eq_iff_iff, iff_false, Nat.not_lt]
  exact h

open Lean Meta in
/-- Case-split, recursively, each local integer type into its width and signedness, so that the
widths of matched values are variables that width equalities can substitute. -/
meta partial def casesIntegerTypes (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless (← instantiateMVars decl.type).isConstOf ``IntegerType do continue
      let subgoals ← goal.cases decl.fvarId
      return (← subgoals.toList.mapM fun subgoal => casesIntegerTypes subgoal.mvarId).flatten
    return [goal]

open Lean Elab Tactic in
/-- Case-split every local integer type of a normalized gMIR validity goal. -/
elab "casesIntegerTypes" : tactic => do
  let goals ← getGoals
  setGoals (← goals.flatMapM fun goal => casesIntegerTypes goal)

open Lean Meta in
/-- Case-split, recursively, each local existential and conjunction, e.g. the choice of high bits
by which a matched `g_anyext` produced its result, or a width equation of a type check. -/
meta partial def casesExistsAnd (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type ← instantiateMVars decl.type
      unless type.isAppOfArity ``Exists 2 || type.isAppOfArity ``And 2 do continue
      let subgoals ← goal.cases decl.fvarId
      return (← subgoals.toList.mapM fun subgoal => casesExistsAnd subgoal.mvarId).flatten
    return [goal]

open Lean Elab Tactic in
/-- Case-split every local existential and conjunction. -/
elab "casesExistsAnd" : tactic => do
  let goals ← getGoals
  setGoals (← goals.flatMapM fun goal => casesExistsAnd goal)

open Lean Meta in
/-- Whether `c` compares two natural numbers. -/
meta def isNatGuard (c : Expr) : Bool :=
  !c.hasLooseBVars &&
    ((c.isAppOfArity ``Eq 3 && (c.getArg! 0).isConstOf ``Nat) ||
      (c.isAppOfArity ``LT.lt 4 && (c.getArg! 0).isConstOf ``Nat) ||
      (c.isAppOfArity ``LE.le 4 && (c.getArg! 0).isConstOf ``Nat) ||
      /- A boolean check of an interpreter, e.g. whether a division has undefined behavior. -/
      (c.isAppOfArity ``Eq 3 && (c.getArg! 0).isConstOf ``Bool &&
        (c.getArg! 2).isConstOf ``Bool.true))

open Lean Elab Tactic in
/-- Case-split on the condition of the first `if` of the goal that compares two natural numbers,
such as an interpreter's check that two operand widths agree, or that is a boolean check, such as
whether a division has undefined behavior. -/
elab "splitGuards" : tactic => withMainContext do
  let isGuarded (e : Expr) : Bool :=
    (e.isAppOfArity ``dite 5 || e.isAppOfArity ``ite 5) && isNatGuard (e.getArg! 1)
  /- Look in the goal first, then in the hypotheses, which describe the results of matched
  operations. -/
  let mut found := (← instantiateMVars (← getMainTarget)).find? isGuarded
  if found.isNone then
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if let some ite := (← instantiateMVars decl.type).find? isGuarded then
        found := some ite
        break
  let some ite := found | throwError "splitGuards: no width guard"
  let condition ← Term.exprToSyntax (ite.getArg! 1)
  evalTactic (← `(tactic| by_cases _guard : $condition))

open Lean Meta in
/-- Case-split, recursively, each local type `t : TypeAttr` whose attribute `t.val` an
interpreter matches on, into the constructors of `Attribute`. -/
meta partial def casesResultTypes (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let some val := target.find? fun e =>
        e.isAppOfArity ``Subtype.val 3 && (e.getArg! 2).isFVar
      | return [goal]
    let fvarId := (val.getArg! 2).fvarId!
    unless (← instantiateMVars (← fvarId.getType)).isConstOf ``TypeAttr do return [goal]
    let subgoals ← goal.cases fvarId
    let mut goals := []
    for subgoal in subgoals do
      let some (Expr.fvar attr) := (subgoal.fields[0]? : Option Expr)
        | goals := goals ++ [subgoal.mvarId]; continue
      for attrGoal in ← subgoal.mvarId.cases attr do
        goals := goals ++ (← casesResultTypes attrGoal.mvarId)
    return goals

open Lean Elab Tactic in
/-- Case-split the attribute of every local type that an interpreter matches on. -/
elab "casesResultTypes" : tactic => do
  let goals ← getGoals
  setGoals (← goals.flatMapM fun goal => casesResultTypes goal)

/-- Unfold the operation semantics of a goal produced by `simpPuddleValid`. The operation
interpreters to unfold are added to `ctree_semantics` locally by each proof file. -/
macro "simpPatternSemantics" : tactic => `(tactic|
  simp [ctree_semantics, Sim.bind_monadLift_right_iff])

/-- Split the matched inputs of a normalized validity goal, then substitute the results of the
matched operations. Each round resolves one more level of nested matched operations: an
operation's result equation only appears once its operands are known values. -/
macro "normalizePatternValid" : tactic => `(tactic| (
  intros
  casesConformingValues
  iterate 4 (all_goals (try simp_all [RuntimeValue.isRefinedBy]); all_goals (try subst_vars))))

/-- Prove the validity of a pattern whose builders have been unfolded, closing each remaining
value goal with the local correctness lemma `lemma`. The lemma's conclusion must match the
normalized goal; its hypotheses (the matcher's guards) are discharged from the matched
properties. -/
macro "provePatternValid" "using" lemma:term : tactic => `(tactic| (
  simpPuddleValid
  simpPatternSemantics
  normalizePatternValid
  all_goals (apply $lemma <;> simp_all)))

/-- Print the normalized goals of a validity proof. Used to state local lemmas. -/
macro "probePatternValid" : tactic => `(tactic| (
  simpPuddleValid
  simpPatternSemantics
  normalizePatternValid
  trace_state
  all_goals sorry))

public section

/-! ## Certificates -/

/-- A certificate for each pattern of a list, in order: a CTree validity proof, or a `Reason` why
there is none. A registry of patterns is certified by a value indexed by the registry, so
registering, removing or reordering a pattern without updating the certificates does not build. -/
inductive Certificates (Reason : Type) : List (Pattern OpCode) → Type 1 where
  | nil : Certificates Reason []
  | proven {pattern : Pattern OpCode} {patterns : List (Pattern OpCode)}
      (valid : Pattern.Valid pattern) (rest : Certificates Reason patterns) :
      Certificates Reason (pattern :: patterns)
  | unproven {pattern : Pattern OpCode} {patterns : List (Pattern OpCode)}
      (reason : Reason) (rest : Certificates Reason patterns) :
      Certificates Reason (pattern :: patterns)

namespace Certificates

variable {Reason : Type}

/-- The patterns that have a validity proof. -/
def provenPatterns : {patterns : List (Pattern OpCode)} → Certificates Reason patterns →
    List (Pattern OpCode)
  | _, .nil => []
  | _, .proven (pattern := pattern) _ rest => pattern :: rest.provenPatterns
  | _, .unproven _ rest => rest.provenPatterns

/-- The patterns that have no validity proof, with the reason. -/
def unprovenPatterns : {patterns : List (Pattern OpCode)} → Certificates Reason patterns →
    List (Pattern OpCode × Reason)
  | _, .nil => []
  | _, .proven _ rest => rest.unprovenPatterns
  | _, .unproven (pattern := pattern) reason rest => (pattern, reason) :: rest.unprovenPatterns

/-- Every pattern with a proof certificate satisfies the CTree validity predicate. -/
theorem valid : {patterns : List (Pattern OpCode)} → (certificates : Certificates Reason patterns) →
    ∀ pattern ∈ certificates.provenPatterns, Pattern.Valid pattern
  | _, .nil => by simp [provenPatterns]
  | _, .proven h rest => by
    simp only [provenPatterns, List.mem_cons, forall_eq_or_imp]
    exact ⟨h, valid rest⟩
  | _, .unproven _ rest => by simpa [provenPatterns] using valid rest

/-- Every pattern of the list is either proven or recorded as unproven. -/
theorem covers : {patterns : List (Pattern OpCode)} → (certificates : Certificates Reason patterns) →
    ∀ pattern ∈ patterns, pattern ∈ certificates.provenPatterns ∨
      pattern ∈ certificates.unprovenPatterns.map Prod.fst
  | _, .nil => by simp
  | _, .proven _ rest => by
    simp only [List.mem_cons, forall_eq_or_imp, provenPatterns, true_or, true_and]
    intro pattern h
    rcases covers rest pattern h with h | h
    · exact .inl (.inr h)
    · exact .inr h
  | _, .unproven _ rest => by
    simp only [List.mem_cons, forall_eq_or_imp, unprovenPatterns, List.map_cons, true_or,
      or_true, true_and]
    intro pattern h
    rcases covers rest pattern h with h | h
    · exact .inl h
    · exact .inr (.inr h)

end Certificates

/-- The certificate of one pattern, as a proposition: a CTree validity proof, or a `Reason` why
there is none. A registry that is a function (e.g. of an opcode) is certified by a `Status` for
every pattern it can return. -/
inductive Status (Reason : Type) (pattern : Pattern OpCode) : Prop where
  | proven (valid : Pattern.Valid pattern)
  | unproven (reason : Reason)

end

end Veir.Puddle.CTree
