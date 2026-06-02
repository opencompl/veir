module

public import Lean

public section

/-!
# `@[simp_getset]` attribute and `simp_getset` tactics

This module defines the `simp_getset` and `simp_getset?` tactics, which tries to apply all
`@[simp_getset]`-tagged theorems. These theorems are equalities with a single explicit argument
of the form `f ... = ...`. The tactic then looks for hypotheses matching this shape, and
applies the theorems with these hypothesese passed as arguments.
-/

namespace Veir

open Lean Meta

/-!
## `@[simp_getset]` attribute
-/

/-- State of the `simp_getset` attribute: a map from a head constant
    to the array of theorem names tagged with `@[simp_getset]`
    that have that constant as the head of the LHS of their first explicit
    hypothesis. -/
abbrev SimpGetSetState := Std.HashMap Name (Array Name)

/-- Add a theorem to the `headFun` entry. -/
private meta def SimpGetSetState.add (s : SimpGetSetState) (headFun th : Name) : SimpGetSetState :=
  s.insert headFun ((s.get? headFun |>.getD #[]).push th)

/-- A persistent environment variable that holds a `SimpGetSetState`. -/
public meta initialize simpGetSetExt :
    SimplePersistentEnvExtension (Name × Name) SimpGetSetState ←
  registerSimplePersistentEnvExtension {
    name          := `simpGetSetExt
    addImportedFn := fun ass => ass.foldl (init := {}) fun s as =>
      as.foldl (init := s) fun s (target, th) => s.add target th
    addEntryFn    := fun s (target, th) => s.add target th
  }

/-- Infer the target head function of a `@[simp_getset]` theorem: take its first explicit
    argument, require it to be an equality, and return the head constant of the LHS. -/
private meta def inferWfGetSetTarget (declName : Name) : MetaM Name := do
  let info ← getConstInfo declName
  forallTelescopeReducing info.type fun xs _ => do
    for x in xs do
      let ldecl ← x.fvarId!.getDecl
      unless ldecl.binderInfo.isExplicit do continue
      let some (_, lhs, _) := (← whnf ldecl.type).eq?
        | throwError "@[simp_getset]: first explicit argument must be an equality"
      let some head := lhs.getAppFn.constName?
        | throwError
          "@[simp_getset]: LHS of the first explicit argument must be an constant application"
      return head
    throwError "@[simp_getset]: theorem has no explicit argument"

/-- Register the `@[simp_getset]` attribute. -/
meta initialize registerBuiltinAttribute {
  name  := `simp_getset
  descr := "Get-set theorem; used by the `simp_getset` tactic. The theorem must take a \
            `f ... = _` hypothesis as its first explicit argument, and the theorem \
            conclusion must be an equality."
  applicationTime := .afterCompilation
  add   := fun decl _stx kind => do
    unless kind == .global do
      throwError "@[simp_getset] only supports the global attribute kind"
    let target ← MetaM.run' (inferWfGetSetTarget decl)
    setEnv (simpGetSetExt.addEntry (← getEnv) (target, decl))
}

/-!
## `simp_getset` tactics
-/

/-- Collect simp lemma arguments for the `simp_getset` family of tactics: for every
    hypothesis `h : f ... = _` in the local context where `f` is the head constant
    of some `@[simp_getset]`-tagged theorem, produce one `lem h` simp argument per
    matching theorem `lem`. -/
private meta def collectSimpGetSetArgs :
    Elab.Tactic.TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let state := simpGetSetExt.getState (← getEnv)
  let mut simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for ldecl in ← getLCtx do
    let some (_, lhs, _) := ldecl.type.eq? | continue
    let some head := lhs.getAppFn.constName? | continue
    let some lemmas := state.get? head | continue
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
