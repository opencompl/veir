/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Leo Stefanesco
-/
module

prelude
public import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.Toposort

open Std (HashMap HashSet)

public section


namespace Lean.Compiler.LCNF.Extras
/-!
# Function arity reduction

This module finds "used" parameters in a declaration, and then
create an auxiliary declaration that contains only used parameters.
For example:
```
def f (x y : Nat) : Nat :=
  let _x.1 := Nat.add x x
  let _x.2 := Nat.mul _x.1 _x.1
  _x.2
```
is converted into
```
def f._redArg (x : Nat) : Nat :=
  let _x.1 := Nat.add x x
  let _x.2 := Nat.mul _x.1 _x.1
  _x.2
def f (x y : Nat) : Nat :=
  let _x.1 := f._redArg x
  _x.1
```
Note that any `f` full application is going to be inlined in the next `simp` pass.

This module does not have similar support for mutual recursive applications.
We assume this limitation is irrelevant in practice.

New features:
- handle recursive functions (cf https://github.com/leanprover/lean4/issues/13355)
  ```
    def ff (x y : Nat) : Nat := 
      match x with
      | 0 => 0 
      | x + 1 => 1 + ff x (x + y)
  ```
- add track dependencies for cases with a single alternative
- errors out if a parameter whose name starts with `GHOST` remains in a function
whose name ends with Impl.
-/

namespace FindUsed

/-- The context keeps track of the name and parameters of the function we are
  compiling to handle recursive calls. -/
structure Context where
  decl : Decl .pure
  params : FVarIdSet

/-- Denotes that rhs depends on lhs. -/
structure Equation where
  lhs : Array FVarId
  rhs : FVarId

structure State where
  decls : HashMap FVarId (Array FVarId)
  equations : HashMap FVarId (Array FVarId)
  facts : HashSet FVarId

def printEqs (s : State) : CompilerM Unit := do
  trace[Compiler.reduceArity2] "Before: "
  trace[Compiler.reduceArity2] "Facts"
  for f in s.facts do
    trace[Compiler.reduceArity2] "{mkFVar f}"
  trace[Compiler.reduceArity2] "Equations"
  for (var, vars) in s.equations do
    trace[Compiler.reduceArity2] "{mkFVar var} --> {vars.toList.map mkFVar}"

abbrev FindUsedM := ReaderT Context <| StateRefT State CompilerM

/-- Record the fact that `rhs` depends on `lhs` to the system. -/
def emitEq (lhs : Array FVarId) (rhs : FVarId) : FindUsedM Unit :=
  modify (fun s => {s with 
    equations := s.equations.insert rhs <| (s.equations.getD rhs #[]) ++ lhs})

/-- Record the fact that `rhs` is needed. -/
def emitFact (rhs : FVarId) : FindUsedM Unit :=
  modify (fun s => {s with facts := s.facts.insert rhs})

def emitFactArg (rhs : Arg .pure) : FindUsedM Unit :=
  match rhs with
  | .fvar fvarId => emitFact fvarId
  | .erased | .type .. => return ()

def emitEqArg (lhs : Arg .pure) (rhs : FVarId) : FindUsedM Unit := do
  match lhs with
  | .fvar fvarId => emitEq #[fvarId] rhs
  | .erased | .type .. => return ()

def addDecl (decl : FunDecl .pure) : FindUsedM Unit := 
  modify (fun s => {s with decls := s.decls.insert decl.fvarId (decl.params.map (·.fvarId))})

def gatherArgs (init : Array FVarId := #[]) (args : Array (Arg .pure)) :=
  args.foldl (init := init) (fun a v => match v with | .fvar fvar => a.push fvar | _ => a)

def visitLetValue (var : FVarId) (e : LetValue .pure) : FindUsedM Unit := do
  match e with
  | .erased | .lit .. => pure ()
  | .proj _ _ fvarId => emitEq #[fvarId] var
  | .fvar fvarId args => emitEq (gatherArgs (init := #[fvarId]) args) var
  | .const declName _ args =>
    let decl := (← read).decl
    if declName == decl.name then
      for param in decl.params, arg in args do
        emitEqArg arg param.fvarId
      -- over-application
      for arg in args[decl.params.size...*] do
        emitEqArg arg var
      -- partial-application
      for param in decl.params[args.size...*] do
        -- If recursive function is partially applied, we assume missing
        -- parameters are used because we don't want to eta-expand.
        emitEq #[param.fvarId] var
    else
      args.forM (emitEqArg · var)

partial def visit (code : Code .pure) : FindUsedM Unit := do
  match code with
  | .let decl k =>
    visitLetValue decl.fvarId decl.value
    visit k
  | .jp decl k | .fun decl k =>
    addDecl decl
    visit k
    visit decl.value
  | .cases c =>
    if c.alts.size = 1 then
      for p in c.alts[0]!.getParams do
        emitEq #[c.discr] p.fvarId
      visit c.alts[0]!.getCode
    else
      emitFact c.discr
      c.alts.forM fun alt => visit alt.getCode
  | .jmp id args => 
    let params ← getFunDecl (pu := .pure) id
    for param in params.params, arg in args do
      emitEqArg arg param.fvarId
  | .return fvarId => emitFact fvarId
  | .unreach _ => return ()

def collectEquations (decl : Decl .pure) : CompilerM State := do
  let params := decl.params.foldl (init := {}) fun s p => s.insert p.fvarId
  let (_, eqs) ← decl.value.forCodeM visit |>.run { decl, params } |>.run ⟨{}, {}, {}⟩
  printEqs eqs
  return eqs

partial def solve (eqs : State) : FVarIdHashSet := Id.run do
  match eqs with
  | ⟨_, eqs, state⟩ =>
    let wl := state.toArray
    pure <| go eqs state wl
where
  go eqs state wl := Id.run do
    let .some var := wl.back? | pure state
    let mut wl := wl.pop
    let some vars := eqs[var]? | go eqs state wl
    let mut state := state
    for v in vars do
      if ¬ state.contains v then
        state := state.insert v
        wl := wl.push v
    go eqs state wl

def collectUsedParams (decl : Decl .pure) : CompilerM FVarIdHashSet := do
  let eqs ← collectEquations decl
  pure (solve eqs)

end FindUsed

namespace ReduceArity

structure Context where
  decl : Decl .pure
  auxDeclName : Name
  liveVars : FVarIdHashSet

structure State where
  used : HashMap FVarId (Array Bool)

abbrev ReduceM := ReaderT Context <| StateT State CompilerM

partial def reduce (code : Code .pure) : ReduceM (Code .pure) := do
  match code with
  | .let decl k =>
    let .const declName _ args := decl.value | do return code.updateLet! decl (← reduce k)
    unless declName == (← read).decl.name do return code.updateLet! decl (← reduce k)
    let liveVars := (← read).liveVars
    let params := (← read).decl.params
    let mut argsNew := #[]
    for param in params, arg in args do
      if liveVars.contains param.fvarId then
        argsNew := argsNew.push arg
    -- over application
    for arg in args[params.size...*] do
      argsNew := argsNew.push arg
    let decl ← decl.updateValue (.const (← read).auxDeclName [] argsNew)
    return code.updateLet! decl (← reduce k)
  | .fun decl k  =>
    let decl ← decl.updateValue (← reduce decl.value)
    return code.updateFun! decl (← reduce k)
  | .jp decl k =>
    let liveVars := (← read).liveVars
    let mut paramsNew := #[]
    let mut used := #[]
    for p in decl.params do
      if liveVars.contains p.fvarId then
        used := used.push true
        paramsNew := paramsNew.push p
      else
        used := used.push false
    modify fun s => { s with used := s.used.insert decl.fvarId used }
    let decl := FunDecl.mk decl.fvarId decl.binderName paramsNew decl.type (← reduce decl.value)
    modifyLCtx fun lctx => lctx.addFunDecl decl
    return .jp decl (← reduce k)
  | .cases c =>
    if c.alts.size = 1 ∧ ¬ (← read).liveVars.contains c.discr then
      eraseParams c.alts[0]!.getParams
      reduce c.alts[0]!.getCode
    else
      let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← reduce alt.getCode)
      return code.updateAlts! alts
  | .unreach .. | .return .. => return code
  | .jmp fvarId args =>
    let liveVars := (← read).liveVars
    let used := (← get).used[fvarId]!
    let mut argsNew := #[]
    for (a, i) in args.zipIdx do
      if used[i]! = true then
        argsNew := argsNew.push a
    return .jmp fvarId argsNew

end ReduceArity

open FindUsed ReduceArity Internalize

/-- Emit an error in case the function is called `...Impl` and still has arguments
whose names are of the form `GHOST...`. -/
def checkParamsForGhosts (params : Array (Param .pure)) (decl : Decl .pure) : CompilerM Unit := do
  let .str _ name := decl.name | return
  unless name.endsWith "Impl" do return
  for param in params do
    trace[Compiler.reduceArity2] "vetting {param.binderName}"
    if let .str _ s := param.binderName then
      if s.startsWith "GHOST" then
        logError  m!"Ghost parameter {param.binderName} has not been eliminated in {decl.name}!"

def Decl.reduceArity (decl : Decl .pure) : CompilerM (Array (Decl .pure)) := do
  match decl.value with
  | .code code =>
    let used ← collectUsedParams decl
    trace[Compiler.reduceArity2] "{decl.name}, {← ppDecl decl}"
    trace[Compiler.reduceArity2] "{decl.name}, used params: {used.toList.map mkFVar}"
    if decl.params.all (fun p => used.contains p.fvarId) || used.size == 0 then
      -- Do nothing if all params were used, or if no params were used. In the latter case,
      -- this would promote the decl to a constant, which could execute unreachable code.
      return #[decl]
    else
      let mask := decl.params.map fun param => used.contains param.fvarId
      let auxName := decl.name ++ `_redArg
      let mkAuxDecl : CompilerM (Decl .pure) := do
        let params := decl.params.filter fun param => used.contains param.fvarId
        checkParamsForGhosts params decl
        let value  ← decl.value.mapCodeM reduce |>.run { liveVars := used, decl := decl, auxDeclName := auxName } |>.run' ⟨{}⟩
        let type ← code.inferType
        let type ← mkForallParams params type
        let auxDecl := { decl with name := auxName, levelParams := [], type, params, value }
        auxDecl.saveMono
        return auxDecl
      let updateDecl : InternalizeM .pure (Decl .pure) := do
        let params ← decl.params.mapM internalizeParam
        let mut args := #[]
        for used in mask, param in params do
          if used then
            args := args.push param.toArg
        let letDecl ← mkAuxLetDecl (.const auxName [] args)
        let value := .code (.let letDecl (.return letDecl.fvarId))
        let decl := { decl with params, value, inlineAttr? := some .inline, recursive := false }
        decl.saveMono
        return decl
      let unusedParams := decl.params.filter fun param => !used.contains param.fvarId
      let auxDecl ← mkAuxDecl
      let decl ← updateDecl |>.run' {}
      eraseParams unusedParams
      return #[auxDecl, decl]
  | .extern .. => return #[decl]

def reduceArity (occ := 0) : Pass where
  phase := .mono
  phaseOut := .mono
  occurrence := occ
  name  := `reduceArity2
  run   := fun decls => do
    let decls ← toposortDecls decls
    decls.foldlM (init := #[]) fun decls decl => return decls ++ (← Decl.reduceArity decl)

initialize registerTraceClass `Compiler.reduceArity2 (inherited := true)

end Lean.Compiler.LCNF.Extras
