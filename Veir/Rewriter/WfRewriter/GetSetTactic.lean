module

public import Lean

public section

/-!
# `@[simp_getset]` attribute and `simp_getset` tactics

This module defines the `simp_getset` and `simp_getset?` tactics, which try to apply all
`@[simp_getset]`-tagged theorems. Unconditional theorems are used as ordinary simp rules. For
theorems whose only explicit argument is an equality of the form `f ... = ...`, the tactic looks
for hypotheses matching this shape and applies the theorems with these hypotheses as arguments.
-/

namespace Veir

open Lean Meta

/-!
## `@[simp_getset]` attribute
-/

/-- State of the `simp_getset` attribute: unconditional theorem names together with a map from
    a head constant to the theorem names whose only explicit hypothesis is an equality with that
    constant at the head of its LHS. -/
meta structure SimpGetSetState where
  unconditional : Array Name := #[]
  conditional : Std.HashMap Name (Array Name) := {}
  deriving Inhabited

/-- Add an unconditional theorem or a theorem to the given `headFun` entry. -/
private meta def SimpGetSetState.add
    (s : SimpGetSetState) (headFun : Option Name) (th : Name) : SimpGetSetState :=
  match headFun with
  | none => { s with unconditional := s.unconditional.push th }
  | some headFun =>
      { s with conditional :=
          s.conditional.insert headFun ((s.conditional.get? headFun |>.getD #[]).push th) }

/-- A persistent environment variable that holds a `SimpGetSetState`. -/
public meta initialize simpGetSetExt :
    SimplePersistentEnvExtension (Option Name × Name) SimpGetSetState ←
  registerSimplePersistentEnvExtension {
    name          := `simpGetSetExt
    addImportedFn := fun ass => ass.foldl (init := default) fun s as =>
      as.foldl (init := s) fun s (target, th) => s.add target th
    addEntryFn    := fun s (target, th) => s.add target th
  }

/-- Infer the target head function of a `@[simp_getset]` theorem. If its only explicit argument
    is an equality, return the head constant of its LHS; otherwise returns `none`. -/
private meta def inferGetSetTarget (declName : Name) : MetaM (Option Name) := do
  let info ← getConstInfo declName
  forallTelescopeReducing info.type fun xs _ => do
    for x in xs do
      let ldecl ← x.fvarId!.getDecl
      unless ldecl.binderInfo.isExplicit do continue
      let some (_, lhs, _) := (← whnf ldecl.type).eq? | return none
      let some head := lhs.getAppFn.constName?
        | throwError
          "@[simp_getset]: LHS of the only explicit argument must be an constant application"
      return some head
    return none

/-- Register the `@[simp_getset]` attribute. -/
meta initialize registerBuiltinAttribute {
  name  := `simp_getset
  descr := "Get-set theorem; used by the `simp_getset` tactic. If its first explicit argument \
            is a `f ... = _` hypothesis, the theorem \
            is only applied when the local context contains a matching hypothesis."
  applicationTime := .afterCompilation
  add   := fun decl _stx kind => do
    unless kind == .global do
      throwError "@[simp_getset] only supports the global attribute kind"
    let target ← MetaM.run' (inferGetSetTarget decl)
    setEnv (simpGetSetExt.addEntry (← getEnv) (target, decl))
}

/-!
## `simp_getset` tactics
-/

/-- Collect simp lemma arguments for the `simp_getset` family of tactics: add unconditional
    theorems directly and, for every hypothesis `h : f ... = _` in the local context, add one
    `lem h` argument per conditional theorem registered for `f`. -/
private meta def collectSimpGetSetArgs :
    Elab.Tactic.TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let state := simpGetSetExt.getState (← getEnv)
  let mut simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for n in state.unconditional do
    let lem := mkIdent n
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| $lem:ident))
  for ldecl in ← getLCtx do
    let some (_, lhs, _) := ldecl.type.eq? | continue
    let some head := lhs.getAppFn.constName? | continue
    let some lemmas := state.conditional.get? head | continue
    let h := mkIdent ldecl.userName
    for n in lemmas do
      let lem := mkIdent n
      simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| $lem:ident $h:ident))
  return simpArgs

open Elab Tactic in
/-- For every hypothesis `h : f ... = _` in the local context where `f` is the
    head constant of some `@[simp_getset]`-tagged theorem, applies all the matching
    theorems with `h` plugged in via a single `simp only` invocation. -/
elab "simp_getset" : tactic => withMainContext do
  let simpArgs ← collectSimpGetSetArgs
  if simpArgs.isEmpty then
    logWarning "simp_getset: no hypothesis matching a registered `@[simp_getset]` target found in context"
    return
  evalTactic <| ← `(tactic| simp only [$simpArgs,*])

open Elab Tactic in
/-- For every hypothesis `h : f ... = _` in the local context where `f` is the
    head constant of some `@[simp_getset]`-tagged theorem, applies all the matching
    theorems with `h` plugged in via a single `simp only?` invocation. -/
elab "simp_getset?" : tactic => withMainContext do
  let simpArgs ← collectSimpGetSetArgs
  if simpArgs.isEmpty then
    logWarning "simp_getset?: no hypothesis matching a registered `@[simp_getset]` target found in context"
    return
  evalTactic <| ← `(tactic| simp? only [$simpArgs,*])


end Veir
