module

import QPFTypes.Meta.QPFAttr
import QPFTypes.Instances.Prod

/-!
# `@[qpf]` Attribute Tests

Each test is an ordinary type definition, whose live parameters are marked with
`liveParam`, and which is shown to be a QPF with the `@[qpf]` attribute.
This exercises both the composition pipeline (`QPFExpr.ofTypeDef`) and the
addition of the result to the environment (`QPFExpr.addDecls`).
We then assert for each test case that an uncurried type function was generated,
as `$name.Uncurried`, and that the original definition now has an associated
instance of `QPF` and (if expected) `QPF.IsPolynomial`.
-/

namespace QPFTypes.Test.QPFAttr
open QPFExpr

set_option QPFTypes.debug true

-- Short-hands for #guard_msgs (drop info)
macro "#gcheck " t:term : command => `(command| #guard_msgs (drop info) in #check $t)
macro "#gsynth " t:term : command => `(command| #guard_msgs (drop info) in #synth $t)

/-!
## Fixtures

Heads to compose with. The pipeline only ever finds a head through instance
synthesis, so these are themselves registered with `@[qpf]`.

* `Fst α β = α`, a binary QPF, and
* `Fin' k α = Fin k`, a unary, constant QPF with one dead parameter.
-/

@[qpf] def Fst (α _β : liveParam Type) := α
@[qpf] def Fin' (k : Nat) (_α : liveParam Type) := Fin k

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
@[qpf] def Proj1Of2.{v} (_ : Type v) (α _β : liveParam (Type u)) := α

#gcheck (Proj1Of2.Uncurried : Type → TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 (Proj1Of2 Nat))
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 (Proj1Of2 Nat))

-- The second of two binders.
@[qpf] def Proj2Of2 (_α β : liveParam (Type u)) := β

#gcheck (Proj2Of2.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 Proj2Of2)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 Proj2Of2)

-- The middle of three binders.
@[qpf] def ProjMidOf3 (_α β _γ : liveParam (Type u)) := β

#gcheck (ProjMidOf3.Uncurried : TypeFun 3)
#gsynth QPF (@TypeFun.ofCurried 3 ProjMidOf3)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 3 ProjMidOf3)

-- The sole binder of a unary QPF.
@[qpf] def ProjSoleOf1 (α : liveParam (Type u)) := α

#gcheck (ProjSoleOf1.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 ProjSoleOf1)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 ProjSoleOf1)

/-!
## Constants

A target that mentions no live variable becomes a `QPF.Const`, whatever its
shape; in particular the pipeline does not look inside it.
-/

-- A closed target.
@[qpf] def ConstClosed (_α _β : liveParam Type) := Int

#gcheck (ConstClosed.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 ConstClosed)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 ConstClosed)

-- With no live variables at all, *every* target is a constant.
@[qpf] def ConstNoLive := Int

#gcheck (ConstNoLive.Uncurried : TypeFun 0)
#gsynth QPF (@TypeFun.ofCurried 0 ConstNoLive)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 0 ConstNoLive)

-- A parameter that is not live is dead, so a target mentioning it is still a
-- constant, even though it is an application.
@[qpf] def ConstDeadFree (k : Nat) (_α : liveParam Type) := Fin k

#gcheck (ConstDeadFree.Uncurried : Nat → TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 (ConstDeadFree 3))
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 (ConstDeadFree 3))

-- A function type whose domain *and* codomain are dead is a constant too: the
-- constant case is checked before the function-type case, so no `QPF.Pi` is built.
@[qpf] def ConstDeadArrow (_α : liveParam Type) := Nat → Int

#gcheck (ConstDeadArrow.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 ConstDeadArrow)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 ConstDeadArrow)

/-!
## Compositions
-/

-- The trivial-application optimization: a head applied to exactly the live
-- variables, in order, is returned as-is, rather than composed with a tuple of
-- projections.
@[qpf] def TrivialApp (α β : liveParam Type) := Fst α β

#gcheck (TrivialApp.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 TrivialApp)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 TrivialApp)

-- Reordered arguments do go through `QPF.Comp`. The arguments are reversed
-- exactly once: `Fst β α` composes `Fst` with `⟨Prj 1, Prj 0⟩`, i.e. with the
-- translations of `α` and `β`, in that order.
@[qpf] def ReorderedApp (α β : liveParam Type) := Fst β α

#gcheck (ReorderedApp.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 ReorderedApp)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 ReorderedApp)

-- Arguments may be constants.
@[qpf] def ArgConstant (α : liveParam Type) := Fst Int α

#gcheck (ArgConstant.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 ArgConstant)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 ArgConstant)

-- Compositions nest, with the inner one translated recursively.
@[qpf] def NestedComp (α β : liveParam Type) := Fst β (Fst β α)

#gcheck (NestedComp.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 NestedComp)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 NestedComp)

-- The head need not be a constant: `parseApp` works outwards from the largest
-- head, so `Fin' 3` is taken as a *unary* head, rather than `Fin'` as a binary
-- one (which is not even type-correct).
@[qpf] def UnaryHeadParseApp (α : liveParam Type) := Fin' 3 α

#gcheck (UnaryHeadParseApp.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 UnaryHeadParseApp)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 UnaryHeadParseApp)

/-!
## Function types

A function type is functorial in its codomain only, so it becomes a `QPF.Pi`
over the (necessarily dead) domain.
-/

-- A non-dependent arrow.
@[qpf] def PiNonDep (α : liveParam Type) := Nat → α

#gcheck (PiNonDep.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 PiNonDep)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 PiNonDep)

-- A dependent function type: the codomain may mention the bound variable.
@[qpf] def PiDep (α : liveParam Type) := (a : Nat) → Fst α (Fin a)

#gcheck (PiDep.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 PiDep)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 PiDep)

-- Function types nest, with the codomain translated recursively.
@[qpf] def PiNested (α : liveParam Type) := Nat → Int → α

#gcheck (PiNested.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 PiNested)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 PiNested)

/-!
## Products

A product `A × B` is just an application of `Prod`, which has a QPF instance
(see `QPFTypes.Instances.Prod`), so it becomes a composition of
`TypeFun.ofCurried Prod` with the translations of `A` and `B`.
-/

-- A product of two live variables.
@[qpf] def ProdLive (α β : liveParam Type) := α × β

#gcheck (ProdLive.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 ProdLive)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 ProdLive)

-- Either component may be a constant.
@[qpf] def ProdConst (α : liveParam Type) := Nat × α

#gcheck (ProdConst.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 ProdConst)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 ProdConst)

-- Products nest, with each component translated recursively.
@[qpf] def ProdNested (α β : liveParam Type) := α × (Nat → β) × Fst β α

#gcheck (ProdNested.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 ProdNested)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 ProdNested)

/-!
## Normalization

The target is put in weak head normal form, at reducible transparency, before
it is dispatched on; for instance, a `let`-expression is zeta-reduced.
-/

-- `let T := Nat; T → α` only becomes a function type after zeta reduction.
@[qpf] def NormalizeLetPi (α : liveParam Type) := let T := Nat; T → α

#gcheck (NormalizeLetPi.Uncurried : TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 NormalizeLetPi)
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 NormalizeLetPi)

-- `let T := α; T` only becomes a projection after zeta reduction.
@[qpf] def NormalizeLetProj (α : liveParam Type) := let T := α; T

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
@[qpf] def UniverseProj (α _β : liveParam (Type v)) := α

#gcheck (UniverseProj.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 UniverseProj.{v})
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 UniverseProj.{v})

-- Including underneath a product.
@[qpf] def UniverseProd (α β : liveParam (Type v)) := α × β

#gcheck (UniverseProd.Uncurried : TypeFun 2)
#gsynth QPF (@TypeFun.ofCurried 2 UniverseProd.{v})
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 2 UniverseProd.{v})

-- Including underneath a `QPF.Pi`, whose domain must live in that same
-- universe; `A : Type v` does, while `Type v` itself would not.
@[qpf] def UniversePi (A : Type v) (α : liveParam (Type v)) := A → α

variable (A : Type v)

#gcheck (UniversePi.Uncurried : Type v → TypeFun 1)
#gsynth QPF (@TypeFun.ofCurried 1 (UniversePi A))
#gsynth QPF.IsPolynomial (@TypeFun.ofCurried 1 (UniversePi A))

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
@[qpf] def FailsLiveDomain (α : liveParam Type) := α → Nat

-- Both components of a product must live in the universe of the QPF, as the
-- `QPF` instance only exists for `Prod.{u, u}`.
/--
error: While deriving a QPF from type expression:
  Nat × α
With live free variables:
  [α]

failed to find a QPF in the head of the application:
  Nat × α
note that the head, after applying it to zero or more of the arguments, must be a type function with a `QPF` instance
-/
#guard_msgs in
@[qpf] def FailsProdUniverse (α : liveParam (Type 1)) := Nat × α
-- FIXME: the `FailsProdUniverse` really ought to work, since the `Nat` is dead.
--        that is, we should have a `QPF` instance for `Prod Nat`


/--
error: While deriving a QPF from type expression:
  Indexed α α
With live free variables:
  [α]

the head of the application still contains live variables:
  Indexed α
-/
#guard_msgs in
@[qpf] def FailsLiveHead (α : liveParam Type) := Indexed α α

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
@[qpf] def FailsNotAQpf (α : liveParam Type) := NotAQpf α

-- A target that is not a type at all. The `let` keeps `ofTypeDef` from treating
-- the lambda's binder as just another (dead) parameter.
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
@[qpf] def FailsNotAType (α : liveParam Type) : Nat → Type := let f := fun (_ : Nat) => α; f

/-!
## Attribute kinds

`@[local qpf]` and `@[scoped qpf]` register the generated instances as local,
resp. scoped, instances. The generated definitions are always added.
-/

section
@[local qpf] def Local (α : liveParam (Type u)) := α
#gsynth QPF (@TypeFun.ofCurried 1 Local)
end

-- The definitions are still there, but the instance is not
#gcheck (Local.Uncurried : TypeFun 1)
/--
error: failed to synthesize
  QPF (TypeFun.ofCurried Local)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth QPF (@TypeFun.ofCurried 1 Local)

namespace Scope
@[scoped qpf] def Scoped (α : liveParam (Type u)) := α
end Scope

#guard_msgs (drop error) in #synth QPF (@TypeFun.ofCurried 1 Scope.Scoped)

open Scope in
#gsynth QPF (@TypeFun.ofCurried 1 Scope.Scoped)

/-!
## Attribute misuse
-/

/-- error: @[qpf] can only be applied to definitions, but 'Ind' is not -/
#guard_msgs in
@[qpf] inductive Ind (α : liveParam (Type u)) | mk : α → Ind α

@[qpf] def Erasable (α : liveParam (Type u)) := α

/-- error: @[qpf] cannot be erased from 'Erasable' -/
#guard_msgs in
attribute [-qpf] Erasable

end QPFTypes.Test.QPFAttr
