module

public import Lean

/-! ## Simpsets -/

register_simp_attr veir_bv_normalize
register_simp_attr veir_bv_normalize_post

/-! ## Veir Bitblasting Tactic -/

/--
`veir_bv_normalize` preprocesses a goal with `LLVM.Int`s and other bitblastable
Veir types into a form suitable for bitblasting, using the `veir_bv_normalize`
simpset followed by the `veir_bv_normalize_post` simpset.

Note: Preprocessing lemmas should almost always be added to `veir_bv_normalize`.
Preprocessing happens in two stages because rewrites are generally
easier to state with the dependently-typed `Int.getValue`, but `bv_decide` works
better with the non-dependent `Int.getValueD`. Thus, `veir_bv_normalize_post`
contains `Int.getValue_eq_getValueD`, which rewrites the former into the latter.
-/
@[expose] macro "veir_bv_normalize" : tactic =>
  `(tactic| ((
      simp -failIfUnchanged only [veir_bv_normalize] <;>
      simp +contextual -failIfUnchanged [veir_bv_normalize_post, -BitVec.extractLsb_toNat])))
/- TODO: Tighten the last `simp` into a `simp only`.
The lack of `only` is copied from the previous version of this tactic, and indeed
some of the tests seem to rely on certain simp-lemmas from the default simp-set.
We should figure out which ones, and add just those to `veir_bv_normalize_post`.
-/

/--
`veir_bv_decide` preprocesses a goal with `LLVM.Int`s and other bitblastable
Veir types into a form suitable for bitblasting, via `veir_bv_normalize`, and
then calls `bv_decide` to automatically close the goal.
-/
@[expose] macro "veir_bv_decide" : tactic =>
  `(tactic| ((veir_bv_normalize <;> bv_decide)))

open Lean Elab Tactic Meta

public section

/--
Runs a TacticM sequence on a specific target goal (MVarId).
If the tactic fails or does not fully close the goal, it rolls back any partial state changes.
-/
meta def runTactic (mvarId : MVarId) (tac : TacticM Unit) : TermElabM (Option (List MVarId)) := do
  let mctx ← getMCtx
  try
    let leftover ← Tactic.run mvarId tac
    if leftover.isEmpty then
      return some []
    else
      setMCtx mctx
      return none
  catch _ =>
    setMCtx mctx
    return none

/--
Core loop that splits `x < n` (represented as `Nat.le (Nat.succ x) n`)
or `x ≤ n` (represented as `Nat.le x n`) directly in MetaM.
Returns a list of all subgoals that failed to solve automatically.
-/
meta partial def unrollNatCases (mvarId : MVarId) (hId : FVarId) (solver : TacticM Unit) : TacticM (List MVarId) := do
  mvarId.withContext do
    let localDecl ← hId.getDecl
    let type ← whnf localDecl.type

    match type.getAppFnArgs with
    -- Under whnf, both `<` and `≤` resolve to the primitive `Nat.le` relation
    | (``Nat.le, #[_, n]) =>
      let nVal ← whnf n
      if nVal.rawNatLit?.isSome then
        -- FIX: We no longer run the solver on the abstract parent goal here.
        -- This prevents the SMT/SAT solver from running on generic, non-instantiated bitwidths
        -- and avoids the "potentially spurious counterexample" error entirely.

        -- Split this level directly
        let subgoals ← mvarId.cases hId
        let mut remainingGoals := []
        for subgoal in subgoals do
          if subgoal.fields.isEmpty then
            -- This is the 'refl' case (variable instantiated to a concrete numeral).
            -- We run the solver directly on this fully instantiated subgoal.
            let solverRes ← runTactic subgoal.mvarId solver
            if solverRes.isSome then
              remainingGoals := remainingGoals ++ []
            else
              remainingGoals := remainingGoals ++ [subgoal.mvarId]
          else
            -- This is the 'step' case (the remaining upper bound).
            -- Search the fields to find the actual recursive Nat.le hypothesis
            let unclosed ← subgoal.mvarId.withContext do
              let mut newHId? : Option FVarId := none
              for field in subgoal.fields do
                if let .fvar fvarId := field then
                  let fieldType ← whnf (← fvarId.getType)
                  if fieldType.isAppOf ``Nat.le then
                    newHId? := some fvarId
                    break

              match newHId? with
              | some newHId =>
                unrollNatCases subgoal.mvarId newHId solver
              | none =>
                -- Fallback: if we somehow couldn't find the Nat.le hypothesis, run the solver
                let solverRes ← runTactic subgoal.mvarId solver
                if solverRes.isSome then
                  pure []
                else
                  pure [subgoal.mvarId]
            remainingGoals := remainingGoals ++ unclosed
        return remainingGoals
      else
        -- If upper bound is zero (contradiction case), let omega clean it up
        let omegaRes ← runTactic mvarId (evalTactic (← `(tactic| omega)))
        if omegaRes.isSome then
          return []
        else
          return [mvarId]
    | _ =>
      -- Fallback to omega if it's some other relation
      let omegaRes ← runTactic mvarId (evalTactic (← `(tactic| omega)))
      if omegaRes.isSome then
        return []
      else
        return [mvarId]

syntax (name := veirBvDecideUpto) "veir_bv_decide_upto " ident : tactic

@[tactic veirBvDecideUpto]
meta def evalVeirBvDecideUpto : Tactic := fun stx => do
  let hId ← match stx with
    | `(tactic| veir_bv_decide_upto $h:ident) => pure h.getId
    | _ => throwUnsupportedSyntax

  let mvarId ← getMainGoal

  mvarId.withContext do
    let lctx ← getLCtx
    let localDecl ← match lctx.findFromUserName? hId with
      | some d => pure d
      | none => throwError "Hypothesis {hId} not found"

    let solver : TacticM Unit := do
      evalTactic (← `(tactic| veir_bv_decide))

    -- Collect all goals that could not be proved
    let leftoverGoals ← unrollNatCases mvarId localDecl.fvarId solver
    setGoals leftoverGoals
