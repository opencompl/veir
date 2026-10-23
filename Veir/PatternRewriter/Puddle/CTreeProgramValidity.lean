module

public meta import Lean
public import Veir.PatternRewriter.Puddle.CTreeValidity
-- Legacy outcome-monad proof helpers, retained until downstream proofs migrate.
public import Veir.PatternRewriter.Puddle.CreationM

namespace Veir.Puddle.CTree

public section

/-- Continuation passing only eliminates assignment plumbing; operation execution
still has exactly the ordinary CTree bind semantics. -/
theorem CreateDecl.interpretWith_eq_bind (decl : CreateDecl OpCode)
    (assignment : SemanticAssignment) (memory : MemoryState)
    (next : SemanticAssignment → MemoryState → Tree α) :
    CreateDecl.interpretWith decl assignment memory next =
      (CreateDecl.interpret decl assignment memory >>= fun (assignment, memory) =>
        next assignment memory) := by
  cases decl <;> simp only [CreateDecl.interpret, CreateDecl.interpretWith]
  all_goals try simp only [pure_bind]
  all_goals split <;> try simp only [bind_assoc, pure_bind]
  all_goals simp [Bind.bind]

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

end

end Veir.Puddle.CTree
