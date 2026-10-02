module

import QPFTypes.Meta.QPFExpr.AddDecl
import QPFTypes.Meta.QPFExpr.OfTypeExpr

/-!
# `QPFExpr.ofTypeExpr` Unit Tests

Each test builds a target type expression out of a set of live variables, runs
it through the pipeline, and registers the resulting QPF under a fresh name
with `QPFExpr.addDecls`. The desired properties of that declaration are then
asserted as ordinary Lean commands, against the declarations `addDecls`
produces (see `QPFExpr.addDecls`'s docstring for their names and types):

* `#gcheck` on `$name.Uncurried` pins down the arity and universe of the
  uncurried type function;
* `example ... := rfl` on `$name` pins down its curried meaning, i.e. what the
  target expression abstracted over the live variables actually was; and
* `#gsynth` confirms that the generated `QPF` instance is actually found by
  instance search, not merely well-typed.
-/

namespace QPFTypes.Test.OfTypeExpr
open Lean Meta Elab QPFExpr

set_option QPFTypes.debug true

/-!
## Test harness
-/

/--
`#gcheck t` is `#check t` with the reported type dropped: it asserts only that
`t` elaborates, turning any elaboration failure into a test failure.
-/
macro "#gcheck " t:term : command =>
  `(command| #guard_msgs (drop info) in #check $t)

/--
`#gsynth t` is `#synth t` with the reported instance dropped: it asserts only
that instance synthesis for `t` succeeds.
-/
macro "#gsynth " t:term : command =>
  `(command| #guard_msgs (drop info) in #synth $t)

/--
Derive a QPF via `QPFExpr.ofTypeExpr`, then add it to the environment with
the given name (in the `QPFTypes.Test.OfTypeExpr` namespace), via `QPFExpr.addDecls`.
-/
private meta def defineQPF (declName : Name) (liveNames : Vector Name n)
    (mkTarget : Vector Expr n → TermElabM Expr)
    (deadVars : Array Expr := #[]) (scopeLevelNames : List Name := [])
    (u : Option Level := none) :
    TermElabM Unit :=
  withLiveVars u liveNames fun xs => do
    let ⟨_, actual⟩ ← ofTypeExpr (xs.map (·.fvarId!)) (← mkTarget xs)
    actual.addDeclsInferringLevelParams (`QPFTypes.Test.OfTypeExpr ++ declName) deadVars scopeLevelNames
where
  withLiveVars (u : Option Level) (liveNames : Vector Name n) (k : Vector Expr n → TermElabM Unit) : TermElabM Unit := do
    let u ← u.getDM mkFreshLevelMVar
    let decls := liveNames.toArray.map fun name =>
      (name, fun _ => pure (Expr.sort u.succ))
    withLocalDeclsD decls fun xs => do
      if h : xs.size = n then
        k ⟨xs, h⟩
      else
        throwError "test harness: expected {n} live variables, got {xs.size}"

/-!
## Fixtures

Heads to compose with. The pipeline only ever finds a head through instance
synthesis, so these are registered exactly like the pipeline's own output is:
with `QPFExpr.addDecls`.

* `Fst α β = α`, a binary QPF, and
* `Fin' k α = Fin k`, a unary QPF with one dead parameter.
-/

run_elab addDecls (mkProj 0 (1 : Fin 2)) `QPFTypes.Test.OfTypeExpr.Fst []

run_elab withLocalDeclD `k (mkConst ``Nat) fun k =>
  addDecls (mkConstant 0 1 (mkApp (mkConst ``Fin) k)) `QPFTypes.Test.OfTypeExpr.Fin' [] #[k]

/-- A head that is not a QPF, used to test that head selection rejects it. -/
def NotAQpf : CurriedTypeFun.{0} 1 := fun α => α

/-- A head that is dead but higher-order, used to test the live-variable check. -/
def Indexed (_ : Type) : CurriedTypeFun.{0} 1 := fun β => β

/-!
## Projections

A target that is exactly a live variable becomes a `QPF.Prj`. Note the index:
the pipeline reverses binder order, since `TypeFun.ofCurried` reads the *first*
curried argument from the *last* component of the type vector.
-/

-- The first of two binders.
run_elab defineQPF `Proj1Of2 #v[`α, `β] (fun αs => pure αs[0])

#gcheck (Proj1Of2.Uncurried : TypeFun 2)
example : Proj1Of2 = fun (α _β : Type) => α := rfl
#gsynth QPF (TypeFun.ofCurried Proj1Of2)

-- The second of two binders.
run_elab defineQPF `Proj2Of2 #v[`α, `β] (fun αs => pure αs[1])

#gcheck (Proj2Of2.Uncurried : TypeFun 2)
example : Proj2Of2 = fun (_α β : Type) => β := rfl
#gsynth QPF (TypeFun.ofCurried Proj2Of2)

-- The middle of three binders.
run_elab defineQPF `ProjMidOf3 #v[`α, `β, `γ] (fun αs => pure αs[1])

#gcheck (ProjMidOf3.Uncurried : TypeFun 3)
example : ProjMidOf3 = fun (_α β _γ : Type) => β := rfl
#gsynth QPF (TypeFun.ofCurried ProjMidOf3)

-- The sole binder of a unary QPF.
run_elab defineQPF `ProjSoleOf1 #v[`α] (fun αs => pure αs[0])

#gcheck (ProjSoleOf1.Uncurried : TypeFun 1)
example : ProjSoleOf1 = fun (α : Type) => α := rfl
#gsynth QPF (TypeFun.ofCurried ProjSoleOf1)

/-!
## Constants

A target that mentions no live variable becomes a `QPF.Const`, whatever its
shape; in particular the pipeline does not look inside it.
-/

-- A closed target.
run_elab defineQPF `ConstClosed #v[`α, `β] (fun _ => pure (mkConst ``Int))

#gcheck (ConstClosed.Uncurried : TypeFun 2)
example : ConstClosed = fun (_ _ : Type) => Int := rfl
#gsynth QPF (TypeFun.ofCurried ConstClosed)

-- With no live variables at all, *every* target is a constant.
run_elab defineQPF `ConstNoLive #v[] (fun _ => pure (mkConst ``Int))

#gcheck (ConstNoLive.Uncurried : TypeFun 0)
example : ConstNoLive = Int := rfl
#gsynth QPF (TypeFun.ofCurried ConstNoLive)

-- A free variable that is not among the live ones is dead, so a target
-- mentioning it is still a constant, even though it is an application.
run_elab do
  withLocalDeclD `k (mkConst ``Nat) fun k =>
    defineQPF `ConstDeadFree #v[`α]
      (fun _ => pure (mkApp (mkConst ``Fin) k))
      #[k] []

#gcheck (ConstDeadFree.Uncurried : Nat → TypeFun 1)
example (k : Nat) : ConstDeadFree k = fun (_ : Type) => Fin k := rfl
#gsynth QPF (TypeFun.ofCurried (ConstDeadFree 3))

-- A function type whose domain *and* codomain are dead is a constant too: the
-- constant case is checked before the function-type case, so no `QPF.Pi` is built.
run_elab do
  let arrow := Expr.forallE `a (mkConst ``Nat) (mkConst ``Int) .default
  defineQPF `ConstDeadArrow #v[`α] (fun _ => pure arrow)

#gcheck (ConstDeadArrow.Uncurried : TypeFun 1)
example : ConstDeadArrow = fun (_ : Type) => (Nat → Int) := rfl
#gsynth QPF (TypeFun.ofCurried ConstDeadArrow)

/-!
## Compositions
-/

-- The trivial-application optimization: a head applied to exactly the live
-- variables, in order, is returned as-is, rather than composed with a tuple of
-- projections.
run_elab do
  defineQPF `TrivialApp #v[`α, `β]
    (fun αs => pure (mkApp2 (mkConst ``Fst) αs[0] αs[1]))

#gcheck (TrivialApp.Uncurried : TypeFun 2)
example : TrivialApp = fun (α β : Type) => Fst α β := rfl
#gsynth QPF (TypeFun.ofCurried TrivialApp)

-- Reordered arguments do go through `QPF.Comp`. The arguments are reversed
-- exactly once: `Fst β α` composes `Fst` with `⟨Prj 1, Prj 0⟩`, i.e. with the
-- translations of `α` and `β`, in that order.
run_elab do
  defineQPF `ReorderedApp #v[`α, `β]
    (fun αs => pure (mkApp2 (mkConst ``Fst) αs[1] αs[0]))

#gcheck (ReorderedApp.Uncurried : TypeFun 2)
example : ReorderedApp = fun (α β : Type) => Fst β α := rfl
#gsynth QPF (TypeFun.ofCurried ReorderedApp)

-- Arguments may be constants.
run_elab do
  defineQPF `ArgConstant #v[`α]
    (fun αs => pure (mkApp2 (mkConst ``Fst) (mkConst ``Int) αs[0]))

#gcheck (ArgConstant.Uncurried : TypeFun 1)
example : ArgConstant = fun (α : Type) => Fst Int α := rfl
#gsynth QPF (TypeFun.ofCurried ArgConstant)

-- Compositions nest, with the inner one translated recursively.
run_elab do
  defineQPF `NestedComp #v[`α, `β]
    (fun αs => pure (mkApp2 (mkConst ``Fst) αs[1] (mkApp2 (mkConst ``Fst) αs[1] αs[0])))

#gcheck (NestedComp.Uncurried : TypeFun 2)
example : NestedComp = fun (α β : Type) => Fst β (Fst β α) := rfl
#gsynth QPF (TypeFun.ofCurried NestedComp)

-- The head need not be a constant: `parseApp` works outwards from the largest
-- head, so `Fin' 3` is taken as a *unary* head, rather than `Fin'` as a binary
-- one (which is not even type-correct).
run_elab do
  let head := mkApp (mkConst ``Fin') (mkNatLit 3)
  defineQPF `UnaryHeadParseApp #v[`α] (fun αs => pure (mkApp head αs[0]))

#gcheck (UnaryHeadParseApp.Uncurried : TypeFun 1)
example : UnaryHeadParseApp = fun (α : Type) => Fin' 3 α := rfl
#gsynth QPF (TypeFun.ofCurried UnaryHeadParseApp)

/-!
## Function types

A function type is functorial in its codomain only, so it becomes a `QPF.Pi`
over the (necessarily dead) domain.
-/

-- A non-dependent arrow.
run_elab do
  defineQPF `PiNonDep #v[`α]
    (fun αs => pure (.forallE `a (mkConst ``Nat) αs[0] .default))

#gcheck (PiNonDep.Uncurried : TypeFun 1)
example : PiNonDep = fun (α : Type) => Nat → α := rfl
#gsynth QPF (TypeFun.ofCurried PiNonDep)

-- A dependent function type: the codomain may mention the bound variable.
run_elab do
  defineQPF `PiDep #v[`α]
    (fun αs => pure (.forallE `a (mkConst ``Nat)
      (mkApp2 (mkConst ``Fst) αs[0] (mkApp (mkConst ``Fin) (.bvar 0))) .default))

#gcheck (PiDep.Uncurried : TypeFun 1)
example : PiDep = fun (α : Type) => (a : Nat) → Fst α (Fin a) := rfl
#gsynth QPF (TypeFun.ofCurried PiDep)

-- Function types nest, with the codomain translated recursively.
run_elab do
  defineQPF `PiNested #v[`α]
    (fun αs => pure (.forallE `a (mkConst ``Nat)
      (.forallE `b (mkConst ``Int) αs[0] .default) .default))

#gcheck (PiNested.Uncurried : TypeFun 1)
example : PiNested = fun (α : Type) => Nat → Int → α := rfl
#gsynth QPF (TypeFun.ofCurried PiNested)

/-!
## Normalization

A target that is none of the supported shapes is retried after `whnfR`, once.
There is no surface syntax that reaches this branch (an application or function
type is dispatched on before it), but elaboration can still produce, say, a
`let`-expression.
-/

-- `let T := Nat; T → α` only becomes a function type after zeta reduction.
run_elab do
  defineQPF `NormalizeLetPi #v[`α]
    (fun αs => pure (.letE `T (mkSort Level.one) (mkConst ``Nat)
      (.forallE `a (.bvar 0) αs[0] .default) false))

#gcheck (NormalizeLetPi.Uncurried : TypeFun 1)
example : NormalizeLetPi = fun (α : Type) => Nat → α := rfl
#gsynth QPF (TypeFun.ofCurried NormalizeLetPi)

-- `let T := α; T` only becomes a projection after zeta reduction.
run_elab do
  defineQPF `NormalizeLetProj #v[`α]
    (fun αs => pure (.letE `T (mkSort Level.one) αs[0] (.bvar 0) false))

#gcheck (NormalizeLetProj.Uncurried : TypeFun 1)
example : NormalizeLetProj = fun (α : Type) => α := rfl
#gsynth QPF (TypeFun.ofCurried NormalizeLetProj)

/-!
## Universes

The universe is threaded through unchanged; it is not inferred from the target.
-/
section
universe v

-- Every construction is built at the level it is given.
run_elab defineQPF `UniverseProj #v[`α, `β] (fun αs => pure αs[0]) #[] [`v]

#gcheck (UniverseProj.Uncurried : TypeFun 2)
example : UniverseProj = fun (α _β : Type v) => α := rfl
#gsynth QPF (TypeFun.ofCurried UniverseProj)

-- Including underneath a `QPF.Pi`, whose domain must live in that same
-- universe; `A : Type v` does, while `Type v` itself would not.
run_elab do
  let v := Level.param `v
  withLocalDeclD `A (.sort v.succ) fun A =>
    defineQPF (u:=v) `UniversePi #v[`α]
      (fun αs => pure (.forallE `a A αs[0] .default))
      #[A] [`v]

variable (A : Type v)

#gcheck (UniversePi.Uncurried : Type v → TypeFun 1)
example : UniversePi A = fun (α : Type v) => A → α := rfl
#gsynth QPF (TypeFun.ofCurried (UniversePi A))

end

/-!
## Rejected targets
-/

/--
error: While deriving a QPF from type expression:
  α → Nat
With live free variables:
  [α]

the domain of a function type may not mention live variables:
  α
a function type is not functorial in its domain.
-/
#guard_msgs in
run_elab do
  defineQPF `Fails #v[`α]
    (fun αs => pure (.forallE `a αs[0] (mkConst ``Nat) .default))

/--
error: While deriving a QPF from type expression:
  Indexed α α
With live free variables:
  [α]

the head of the application still contains live variables:
  Indexed α
-/
#guard_msgs in
run_elab do
  defineQPF `Fails #v[`α] (fun αs => pure (mkApp2 (mkConst ``Indexed) αs[0] αs[0]))

/--
error: While deriving a QPF from type expression:
  NotAQpf α
With live free variables:
  [α]

failed to find a QPF in the head of the application:
  NotAQpf α
note that the head, after applying it to zero or more of the arguments, must be a type function with a `QPF` instance
-/
#guard_msgs in
run_elab do
  defineQPF `Fails #v[`α]
    (fun αs => pure (mkApp (mkConst ``NotAQpf) αs[0]))

-- A target that is neither a live variable, nor live-free, nor an application,
-- nor a function type, and that `whnfR` does not change, hits the catch-all.
/--
error: While deriving a QPF from type expression:
  fun x => α
With live free variables:
  [α]

type expected
  fun x => α
-/
#guard_msgs in
run_elab do
  defineQPF `Fails #v[`α]
    (fun αs => pure (.lam `x (mkConst ``Nat) αs[0] .default))

end QPFTypes.Test.OfTypeExpr
