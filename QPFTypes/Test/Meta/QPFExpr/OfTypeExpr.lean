module

import QPFTypes.Meta.QPFExpr.AddDecl
import QPFTypes.Meta.QPFExpr.OfTypeExpr

/-!
# `QPFExpr.ofTypeExpr` Unit Tests

Each test is an ordinary type definition, whose live parameters are marked with
`liveParam`. The defined typefunction is then shown to be a QPF with `deriveQPF`,
which composes `QPFExpr.ofTypeDef` with `QPFExpr.addDecls`.
We then assert for each test case that an uncurried type function was generated,
as `$name.Uncurried`, and that the original definition now has an associated
instance of `QPF` and (if expected) `QPF.IsPolynomial`.
-/

namespace QPFTypes.Test.OfTypeExpr
open Lean Meta Elab QPFExpr

set_option QPFTypes.debug true

/-!
## Test harness
-/

-- Short-hands for #guard_msgs (drop info)
macro "#gcheck " t:term : command => `(command| #guard_msgs (drop info) in #check $t)
macro "#gsynth " t:term : command => `(command| #guard_msgs (drop info) in #synth $t)

/--
Derive a QPF from the existing type definition `declName` via
`QPFExpr.ofTypeDef`, and add it to the environment via `QPFExpr.addDecls`.
-/
private meta def deriveQPF (declName : Name) : TermElabM Unit :=
  QPFExpr.ofTypeDef declName (·.addDecls declName · <| ·.map Expr.fvar)

/-!
## Fixtures

Heads to compose with. The pipeline only ever finds a head through instance
synthesis, so these are registered exactly like the pipeline's own output is:
with `QPFExpr.addDecls`.

* `Fst α β = α`, a binary QPF, and
* `Fin' k α = Fin k`, a unary, constant QPF with one dead parameter.
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
def Proj1Of2.{v} (_ : Type v) (α _β : liveParam (Type u)) := α
run_elab deriveQPF ``Proj1Of2

#gcheck (Proj1Of2.Uncurried : Type → TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 (Proj1Of2 Nat))
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 (Proj1Of2 Nat))

-- The second of two binders.
def Proj2Of2 (_α β : liveParam (Type u)) := β
run_elab deriveQPF ``Proj2Of2

#gcheck (Proj2Of2.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 Proj2Of2)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 Proj2Of2)

-- The middle of three binders.
def ProjMidOf3 (_α β _γ : liveParam (Type u)) := β
run_elab deriveQPF ``ProjMidOf3

#gcheck (ProjMidOf3.Uncurried : TypeFun 3)
#gsynth QPF (@TypeFun.ofCurried 3 ProjMidOf3)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 3 ProjMidOf3)

-- The sole binder of a unary QPF.
def ProjSoleOf1 (α : liveParam (Type u)) := α
run_elab deriveQPF ``ProjSoleOf1

#gcheck (ProjSoleOf1.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 ProjSoleOf1)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 ProjSoleOf1)

/-!
## Constants

A target that mentions no live variable becomes a `QPF.Const`, whatever its
shape; in particular the pipeline does not look inside it.
-/

-- A closed target.
def ConstClosed (_α _β : liveParam Type) := Int
run_elab deriveQPF ``ConstClosed

#gcheck (ConstClosed.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 ConstClosed)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 ConstClosed)

-- With no live variables at all, *every* target is a constant.
def ConstNoLive := Int
run_elab deriveQPF ``ConstNoLive

#gcheck (ConstNoLive.Uncurried : TypeFun 0)
#gsynth QPF (@TypeFun.ofCurried 0 ConstNoLive)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 0 ConstNoLive)

-- A parameter that is not live is dead, so a target mentioning it is still a
-- constant, even though it is an application.
def ConstDeadFree (k : Nat) (_α : liveParam Type) := Fin k
run_elab deriveQPF ``ConstDeadFree

#gcheck (ConstDeadFree.Uncurried : Nat → TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 (ConstDeadFree 3))
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 (ConstDeadFree 3))

-- A function type whose domain *and* codomain are dead is a constant too: the
-- constant case is checked before the function-type case, so no `QPF.Pi` is built.
def ConstDeadArrow (_α : liveParam Type) := Nat → Int
run_elab deriveQPF ``ConstDeadArrow

#gcheck (ConstDeadArrow.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 ConstDeadArrow)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 ConstDeadArrow)

/-!
## Compositions
-/

-- The trivial-application optimization: a head applied to exactly the live
-- variables, in order, is returned as-is, rather than composed with a tuple of
-- projections.
def TrivialApp (α β : liveParam Type) := Fst α β
run_elab deriveQPF ``TrivialApp

#gcheck (TrivialApp.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 TrivialApp)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 TrivialApp)

-- Reordered arguments do go through `QPF.Comp`. The arguments are reversed
-- exactly once: `Fst β α` composes `Fst` with `⟨Prj 1, Prj 0⟩`, i.e. with the
-- translations of `α` and `β`, in that order.
def ReorderedApp (α β : liveParam Type) := Fst β α
run_elab deriveQPF ``ReorderedApp

#gcheck (ReorderedApp.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 ReorderedApp)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 ReorderedApp)

-- Arguments may be constants.
def ArgConstant (α : liveParam Type) := Fst Int α
run_elab deriveQPF ``ArgConstant

#gcheck (ArgConstant.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 ArgConstant)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 ArgConstant)

-- Compositions nest, with the inner one translated recursively.
def NestedComp (α β : liveParam Type) := Fst β (Fst β α)
run_elab deriveQPF ``NestedComp

#gcheck (NestedComp.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 NestedComp)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 NestedComp)

-- The head need not be a constant: `parseApp` works outwards from the largest
-- head, so `Fin' 3` is taken as a *unary* head, rather than `Fin'` as a binary
-- one (which is not even type-correct).
def UnaryHeadParseApp (α : liveParam Type) := Fin' 3 α
run_elab deriveQPF ``UnaryHeadParseApp

#gcheck (UnaryHeadParseApp.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 UnaryHeadParseApp)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 UnaryHeadParseApp)

/-!
## Function types

A function type is functorial in its codomain only, so it becomes a `QPF.Pi`
over the (necessarily dead) domain.
-/

-- A non-dependent arrow.
def PiNonDep (α : liveParam Type) := Nat → α
run_elab deriveQPF ``PiNonDep

#gcheck (PiNonDep.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 PiNonDep)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 PiNonDep)

-- A dependent function type: the codomain may mention the bound variable.
def PiDep (α : liveParam Type) := (a : Nat) → Fst α (Fin a)
run_elab deriveQPF ``PiDep

#gcheck (PiDep.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 PiDep)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 PiDep)

-- Function types nest, with the codomain translated recursively.
def PiNested (α : liveParam Type) := Nat → Int → α
run_elab deriveQPF ``PiNested

#gcheck (PiNested.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 PiNested)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 PiNested)

/-!
## Normalization

The target is put in weak head normal form, at reducible transparency, before
it is dispatched on; for instance, a `let`-expression is zeta-reduced.
-/

-- `let T := Nat; T → α` only becomes a function type after zeta reduction.
def NormalizeLetPi (α : liveParam Type) := let T := Nat; T → α
run_elab deriveQPF ``NormalizeLetPi

#gcheck (NormalizeLetPi.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 NormalizeLetPi)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 NormalizeLetPi)

-- `let T := α; T` only becomes a projection after zeta reduction.
def NormalizeLetProj (α : liveParam Type) := let T := α; T
run_elab deriveQPF ``NormalizeLetProj

#gcheck (NormalizeLetProj.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 NormalizeLetProj)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 NormalizeLetProj)

/-!
## Universes

The universe level parameters of the definition are kept as-is.
-/
section
universe v

-- Every construction is built at the level of the definition.
def UniverseProj (α _β : liveParam (Type v)) := α
run_elab deriveQPF ``UniverseProj

#gcheck (UniverseProj.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 UniverseProj.{v})
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 UniverseProj.{v})

-- Including underneath a `QPF.Pi`, whose domain must live in that same
-- universe; `A : Type v` does, while `Type v` itself would not.
def UniversePi (A : Type v) (α : liveParam (Type v)) := A → α
run_elab deriveQPF ``UniversePi

variable (A : Type v)

#gcheck (UniversePi.Uncurried : Type v → TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 (UniversePi A))
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 (UniversePi A))

end

/-!
## Rejected targets
-/

def FailsLiveDomain (α : liveParam Type) := α → Nat

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
run_elab deriveQPF ``FailsLiveDomain

def FailsLiveHead (α : liveParam Type) := Indexed α α

/--
error: While deriving a QPF from type expression:
  Indexed α α
With live free variables:
  [α]

the head of the application still contains live variables:
  Indexed α
-/
#guard_msgs in
run_elab deriveQPF ``FailsLiveHead

def FailsNotAQpf (α : liveParam Type) := NotAQpf α

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
run_elab deriveQPF ``FailsNotAQpf

-- A target that is not a type at all. The `let` keeps `ofTypeDef` from treating
-- the lambda's binder as just another (dead) parameter.
def FailsNotAType (α : liveParam Type) : Nat → Type := let f := fun (_ : Nat) => α; f

/--
error: While deriving a QPF from type expression:
  have f := fun x => α;
  f
With live free variables:
  [α]

type expected
  have f := fun x => α;
  f
-/
#guard_msgs in
run_elab deriveQPF ``FailsNotAType

end QPFTypes.Test.OfTypeExpr
