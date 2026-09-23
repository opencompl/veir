module

public meta import Lean
public import Veir.PatternRewriter.Puddle.CTreeValidity

namespace Veir.Puddle.CTree

public section

namespace CreationM

/-- Keep a construction obligation in the program without carrying an assignment. -/
@[expose]
def check (condition : Prop) : CreationM Unit := checked condition ()

/-- Substitute a deterministic assignment update while retaining its safety check. -/
theorem checked_bind_check (condition : Prop) (a : α) (next : α → CreationM β) :
    (checked condition a).bind next = (check condition).bind (fun _ => next a) := by
  apply ext <;> simp [check, checked, CreationM.bind]

theorem models_check_bind (condition : Prop) (next : Unit → CreationM α)
    (k : Interp α → Prop) :
    ((check condition).bind next).Models k ↔ condition ∧ (next ()).Models k := by
  simp [check, models_bind]

theorem models_check (condition : Prop) (k : Interp Unit → Prop) :
    (check condition).Models k ↔ condition ∧ k (.ok ()) := by
  simp [check]

end CreationM

open Lean in
@[app_unexpander CreationM.bind]
meta def unexpandCreationBind : PrettyPrinter.Unexpander
  | `($_ $m $next) => `($m >>= $next)
  | _ => throw ()

section

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr

/-- Collect concrete creation binds into a single `do` block. -/
meta partial def delabCreationDoElems : DelabM (List (TSyntax `doElem)) := do
  let e ← getExpr
  if e.isAppOfArity ``CreationM.bind 4 then
    let α := e.getAppArgs[0]!
    let m ← withAppFn <| withAppArg delab
    withAppArg do
      let Expr.lam _ _ body _ ← getExpr | failure
      withBindingBodyUnusedName fun n => do
        if body.hasLooseBVars then
          prependAndRec `(doElem|let $(⟨n⟩):term ← $m:term)
        else if α.isConstOf ``Unit || α.isConstOf ``PUnit then
          prependAndRec `(doElem|$m:term)
        else
          prependAndRec `(doElem|let _ ← $m:term)
  else if e.isLet then
    let Expr.letE n t v b nondep ← getExpr | failure
    let n ← getUnusedName n b
    let stxT ← descend t 0 delab
    let stxV ← descend v 1 delab
    withLetDecl n t v (nondep := nondep) fun fvar =>
      descend (b.instantiate1 fvar) 2 <|
        if nondep then
          prependAndRec `(doElem|have $(mkIdent n) : $stxT := $stxV)
        else
          prependAndRec `(doElem|let $(mkIdent n) : $stxT := $stxV)
  else
    let stx ← delab
    return [← `(doElem|$stx:term)]
where
  prependAndRec x : DelabM _ := List.cons <$> x <*> delabCreationDoElems

/-- Print folded creation programs using `do`, retaining `>>=` as a fallback. -/
@[app_delab CreationM.bind]
meta def delabCreationDo : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
    guard <| (← getExpr).isAppOfArity ``CreationM.bind 4
    let elems ← delabCreationDoElems
    let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
    `(do $items:doSeqItem*)

end

/--
Expose an assignment-free creation program with one final postcondition.
Unlike `simpPuddleSemantics`, this keeps operation choices and binds intact.
Result-count obligations remain as `CreationM.check` steps.
-/
macro "simpPuddleProgram" : tactic =>
  `(tactic| simpPuddleCore [↓CreationM.checked_bind_check])

/-- Opt in to proving validity by consuming the creation program one operation at a time. -/
macro "provePuddleValid" "program" "=>" body:tacticSeq : tactic =>
  `(tactic| (
    try unfoldPuddleBuilder
    constructor
    · provePuddleSupported
    · cbv
    · native_decide
    simpPuddleProgram
    ($body)))

/--
Consume the next `CreationM.choose` using the supplied interpretation rules.
Only its outcome relation is simplified with those rules, leaving later operations intact.
Successful outcomes discharge concrete result-count checks and substitute their values.
Nondeterministic choices remain universally quantified; UB and failure still require the
final postcondition. An unknown outcome stays folded for the caller to analyze.
-/
macro "puddleStep" "[" rules:Lean.Parser.Tactic.simpArg,* "]" : tactic => do
  let rules : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar,
      `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] "," := ⟨rules.elemsAndSeps⟩
  `(tactic| (
    rw [CreationM.models_bind, CreationM.models_choose]
    conv =>
      intro outcome
      lhs
      simp only [$rules,*]
    simp only [forall_exists_index, and_imp, forall_eq_apply_imp_iff, forall_eq,
      CreationM.forall_result_eq,
      Interp.foldProp_ok, Interp.foldProp_ub, Interp.foldProp_fail,
      CreationM.models_check_bind, CreationM.models_check, CreationM.models_pure,
      List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.lt_add_one, getElem!_pos, List.getElem_toArray, List.getElem_cons_zero,
      true_and, and_true]))

end

end Veir.Puddle.CTree
