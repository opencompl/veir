/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.LCNF.PrettyPrinter

open Std (HashMap HashSet)

public section

namespace Lean.Compiler.LCNF.Extras

/-!
# Spurious construction eleminitation.

Changes programs which contain patterns of the form:

```
jp x1 .. y ... xn :=
  ...
  cases y with
  .mk z1 .... zk
  ...


x = mk x1 ... xk
jp ... x ....

t = mk t1 ... tk
jp ... t ....
```

into:

```
jp x1 .. z1 ... zk ... xn :=
  ...

jp ... x` ... xk ....

jp ... t1 ... tk ....
```

-/

namespace SpuriousConstr

namespace GatherInfo

structure Context where

structure State where
  /-- Variables that are only used to be destructed, a single time and with a
    single alternative. Such variables are mapped to the variables in the
    corresponding pattern. Not modified during the modification phase. -/
  onlyDestructed : HashMap FVarId (Option (Array (Param .pure)))
  /-- Variables that are constructed, and their associated components.
      Not modified during the modification phase. -/
  constructed : HashMap FVarId (Array (Arg .pure))
  /-- Associates jps with its variables that are only destructed once.
      Not modified during the modification phase. -/
  jps : HashMap FVarId (HashSet Nat)
  /-- Keeps track of which variables have been removed. This is only used during
    the modification phase, it's empty during the analysis phase. -/
  deletedVars : HashSet FVarId

def State.dump (s : State) : CompilerM Unit := do
  trace[Compiler.removeSpuriousConstr] "constructed"
  for v in s.constructed do
    trace[Compiler.removeSpuriousConstr] m!"  {mkFVar v.1} -> ..."
  for (jp, ps) in s.jps do
    trace[Compiler.removeSpuriousConstr] "  {mkFVar jp} -> {ps.toList}"

abbrev GatherM :=  ReaderT Context <| StateRefT State CompilerM

def addOrRemoveOnlyCase (x : FVarId) (args : Array (Param .pure)) : GatherM Unit :=
  modify fun s =>
    match s.onlyDestructed[x]? with
    | none => {s with onlyDestructed := s.onlyDestructed.insert x (some args) }
    | some (some _) | some none => {s with onlyDestructed := s.onlyDestructed.insert x none }
def removeOnlyCase (x : FVarId) : GatherM Unit :=
  modify fun s => {s with onlyDestructed := s.onlyDestructed.insert x none }
def getOnlyDestructed (x : FVarId) : GatherM (Option (Array (Param .pure))) := do
  match (← get).onlyDestructed[x]? with
  | none | some none => pure none
  | some info => pure info

def addConstr (x : FVarId) (args : Array (Arg .pure)) : GatherM Unit :=
  modify fun s => {s with constructed := s.constructed.insert x args }

def markJpDestructedVars (x : FVarId) (ps : HashSet Nat) : GatherM Unit :=
  modify fun s => {s with jps := s.jps.insert x ps }

def unmarkJpConstrVar (x : FVarId) (pos : Nat) : GatherM Unit :=
  modify fun s =>
    if let some ps := s.jps[x]? then
      let ps := ps.erase pos
      {s with jps := s.jps.insert x ps }
    else
      s

def markAsDeleted (x : FVarId) : GatherM Unit :=
  modify fun s => {s with deletedVars := s.deletedVars.insert x }

def visitLetValue (var : FVarId) (e : LetValue .pure) : GatherM Unit := do
  match e with
  | .erased | .lit .. => pure ()
  | .proj _ _ fvarId =>
    removeOnlyCase fvarId
  | .fvar _fvarId args =>
    args.forM fun arg => if let .fvar x := arg then removeOnlyCase x else pure ()
  | .const declName _ args =>
    args.forM fun arg => if let .fvar x := arg then removeOnlyCase x else pure ()
    if let some (.ctorInfo info) := (← getEnv).find? declName then
      if args.size = info.numParams + info.numFields then
        addConstr var (args.drop info.numParams)

def getCaseArgs (c : Cases .pure) : Option (Array (Param .pure)) := do
  if c.alts.size != 1 then none else
  c.alts[0]!.getParams

def visitCase (c : Cases .pure) : GatherM Unit := do
  if let some args := getCaseArgs c then
    addOrRemoveOnlyCase c.discr args

def markJp (decl : FunDecl .pure) : GatherM Unit := do
  let mut candidates := {}
  for (param, i) in decl.params.zipIdx do
    let var := param.fvarId
    if (← getOnlyDestructed var) |>.isSome then
      candidates := candidates.insert i
  markJpDestructedVars decl.fvarId candidates

partial def visit (code : Code .pure) : GatherM Unit := do
  match code with
  | .let decl k =>
    visitLetValue decl.fvarId decl.value
    visit k
  | .jp decl k =>
    visit decl.value
    markJp decl
    visit k
  | .fun decl k =>
    visit decl.value
    visit k
  | .cases c =>
    visitCase c
    c.alts.forM fun alt => visit alt.getCode
  | .jmp jp args =>
    for (arg, i) in args.zipIdx do
      if let .fvar x := arg then
        removeOnlyCase x
        if x ∉ (←get).constructed then
          unmarkJpConstrVar jp i
    pure ()
  | .return _ => pure ()
  | .unreach _ => pure ()

def shouldModifyJp (jp : FVarId) : GatherM (Option (HashSet Nat)) := do
  let some jpInfo := (←get).jps[jp]? | return none
  if jpInfo.isEmpty then return none else return jpInfo

def shedForall (type : Expr) : CompilerM Expr := match type with
  | .forallE _ _ t _ => pure t
  | _ => throwError "should be a forall"

mutual
partial def modifyJp (decl : FunDecl .pure) : GatherM (FunDecl .pure) := do
  let some jpInfo ← shouldModifyJp decl.fvarId | return ← decl.updateValue (← modifyCode decl.value)
  let mut type := decl.type
  let mut ps := #[]
  for (p, i) in decl.params.zipIdx do
    type ← shedForall type
    if i ∈ jpInfo then
      let reps := (← getOnlyDestructed p.fvarId).get!
      markAsDeleted p.fvarId
      eraseParam p
      reps.forM fun p => eraseParam p
      reps.forM fun p => modifyLCtx fun lctx => lctx.addParam p
      ps := ps.append reps
    else
      ps := ps.push p
  for p in ps.reverse do
    type := .forallE p.binderName p.type type .default
  return ← decl.update type ps (← modifyCode decl.value)

partial def modifyCode (code : Code .pure) : GatherM (Code .pure) := do
  match code with
  | .let _ k =>
    return code.updateCont! (← modifyCode k)
  | .jp decl k =>
    let k ← modifyCode k
    let decl ← modifyJp decl
    return .jp decl k
  | .fun _ k =>
    return code.updateCont! (← modifyCode k)
  | .cases c =>
    if (← getOnlyDestructed c.discr).isSome ∧ c.discr ∈ (← get).deletedVars then
      modifyCode c.alts[0]!.getCode
    else
      let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← modifyCode alt.getCode)
      return code.updateAlts! alts
  | .jmp jp args =>
    if let some jpInfo ← shouldModifyJp jp then
      let mut newArgs := #[]
      for (arg, i) in args.zipIdx do
        if i ∈ jpInfo then
          let .fvar fvar := arg | panic "changed parameter must be an fvar"
          newArgs := newArgs.append (← get).constructed[fvar]!
        else
          newArgs := newArgs.push arg
      return .jmp jp newArgs
    else
      pure code
  | .return _ => pure code
  | .unreach _ => pure code
end

def run (decl : DeclValue .pure) : GatherM (DeclValue .pure) := do
  decl.mapCodeM fun code => do
    visit code
    modifyCode code

end GatherInfo

def run (decl : Decl .pure) : CompilerM (Decl .pure) := do
  let value ← GatherInfo.run decl.value |>.run ⟨⟩ |>.run' ⟨{}, {}, {}, {}⟩
  return { decl with value }

end SpuriousConstr

open SpuriousConstr

partial
def Decl.removeSpuriousConstr (decl : Decl .pure) : CompilerM (Decl .pure) := do
  trace[Compiler.removeSpuriousConstr] "Compiling {decl.name}... with def {← ppDecl decl}"
  let decl ← go decl
  trace[Compiler.removeSpuriousConstr] "After compiling: {← ppDecl decl}"
  pure decl
where
  -- TODO: this is inefficient
  go decl : CompilerM (Decl .pure) := do
    let new ← SpuriousConstr.run decl
    if new == decl then pure decl else go new

def removeSpuriousConstr : Pass where
  phase := .mono
  phaseOut := .mono
  name  := `removeSpuriousConstr
  run   := fun decls => do
    decls.mapM fun decl => Decl.removeSpuriousConstr decl

initialize
  registerTraceClass `Compiler.removeSpuriousConstr (inherited := true)
