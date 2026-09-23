module

public meta import Lean
public import CTree.Sim

/-! Pretty-print CTree simulations as pairs of programs in `do` notation. -/

public section

namespace CTree

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr

/-- Print a bind whose continuation is not a lambda. The current expression is the continuation. -/
private meta def delabTreeDoContinuation (action : TSyntax `term) :
    DelabM (List (TSyntax `doElem)) := do
  let name ← getUnusedName `value (← getExpr)
  let next ← delab
  let call ← `($next $(mkIdent name))
  return [← `(doElem|let $(mkIdent name) ← $action:term),
    ← `(doElem|$call:term)]

/--
Reconstruct a flat sequence of `do` statements without unfolding operation semantics.

Adapted from Lean's `PrettyPrinter.Delaborator.delabDoElems`, with support for explicit
`CTree.bind`, non-lambda continuations, and `return` notation for `pure` and `CTree.ret`.
Unused bind results are always written as `let _ ← action`, regardless of their type.
-/
meta partial def delabTreeDoElems : DelabM (List (TSyntax `doElem)) := do
  let e ← getExpr
  if e.isAppOfArity ``CTree.bind 8 || e.isAppOfArity ``Bind.bind 6 then
    -- In either bind representation, the last two arguments are the action and continuation.
    let action ← withAppFn <| withAppArg delab
    withAppArg do
      let Expr.lam _ _ body _ ← getExpr | delabTreeDoContinuation action
      withBindingBodyUnusedName fun name => do
        if body.hasLooseBVars then
          prependAndRec `(doElem|let $(⟨name⟩):term ← $action:term)
        else
          prependAndRec `(doElem|let _ ← $action:term)
  else if let Expr.letE name type value body nondep := e then
    let name ← getUnusedName name body
    let typeStx ← descend type 0 delab
    let valueStx ← descend value 1 delab
    withLetDecl name type value (nondep := nondep) fun fvar =>
      descend (body.instantiate1 fvar) 2 <|
        if nondep then
          prependAndRec `(doElem|have $(mkIdent name) : $typeStx := $valueStx)
        else
          prependAndRec `(doElem|let $(mkIdent name) : $typeStx := $valueStx)
  else if e.isAppOf ``Pure.pure || e.isAppOf ``CTree.CTree.ret then
    let value ← withAppArg delab
    return [← `(doElem|return $value)]
  else
    let action ← delab
    return [← `(doElem|$action:term)]
where
  prependAndRec elem : DelabM _ := List.cons <$> elem <*> delabTreeDoElems

meta def delabTreeDo : Delab := do
  let elems ← delabTreeDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(do $items:doSeqItem*)

/-- Show both sides of refinement as programs, including a single-operation side. -/
@[app_delab Sim]
meta def delabSim : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
    guard <| (← getExpr).isAppOfArity ``Sim 12
    let sim ← withAppFn <| withAppFn <| withAppFn delab
    let relation ← withAppFn <| withAppFn <| withAppArg delab
    let target ← withAppFn <| withAppArg delabTreeDo
    let source ← withAppArg delabTreeDo
    `($sim $relation $target $source)

end CTree
