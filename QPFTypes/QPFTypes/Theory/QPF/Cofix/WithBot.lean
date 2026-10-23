module

public import QPFTypes.Theory.QPF.Cofix.Order
public import QPFTypes.Theory.QPF.Comp
public import QPFTypes.Instances.Option

/-!
# Coinductive types with a freely added bottom element

`Cofix.instCCPO` needs a `HasBot F α` instance: a shape of `F` that carries no recursive
data, from which the least element is built. Not every functor has one (e.g. streams,
`F (α ::: X) = α₀ × X`, have no shape that avoids `α₀`).

`CofixWithBot F α` sidesteps this by taking the fixpoint of `Option ∘ F` instead of `F`:
every layer may additionally be `none`, and `none` is a canonical bottom shape. Thus the
resulting type is a `CCPO` (whenever `F` is polynomial) and `partial_fixpoint` can define
functions into it, with non-productive recursion yielding a `none` layer.

## Main definitions

* `TypeFun.WithBot F` - the functor `fun αs => Option (F αs)`, as a `QPF.Comp`
* `CofixWithBot F`    - `Cofix (F.WithBot)`
* a `HasBot (F.WithBot) α` instance, whose bottom shape is `none`
* `CofixWithBot.HasNoBot x` - coinductively, `x` contains no `none` layer
* `CofixWithBot.cast`       - turns an `x` with `HasNoBot x` into a `Cofix F α`
-/

@[expose] public section

namespace QPFTypes

universe u v

variable {n : Nat}

namespace TypeFun

/--
`TypeFun.WithBot F` is `F` post-composed with `Option`,
that is, `WithBot F αs = Option (F αs)` -/
abbrev WithBot (F : TypeFun n) : TypeFun n :=
  QPF.Comp (TypeFun.ofCurried (n := 1) Option) fun _ => F

/-- `none` is a bottom shape for `WithBot F`, irrespective of `F`. -/
instance WithBot.instHasBot {F : TypeFun (n + 1)} {α : TypeVec n} :
    HasBot (F.WithBot) α where
  botShape := .mk none

end TypeFun

namespace QPF

/-- The greatest fixpoint of `Option ∘ F`, with respect to the final argument of `F`. -/
abbrev CofixWithBot (F : TypeFun.{u} (n + 1)) [QPF F] (α : TypeVec.{u} n) : Type u :=
  Cofix (F.WithBot) α


namespace CofixWithBot

open TypeVec MvFunctor

variable {F : TypeFun.{u} (n + 1)} [QPF F] {α : TypeVec.{u} n}

/--
`HasNoBot x` holds when `x` contains no `none` layer anywhere, which is to say,
its root is `some y`, and every recursive child of `y` again satisfies `HasNoBot`.
-/
coinductive HasNoBot : CofixWithBot F α → Prop where
  | some {x : CofixWithBot F α} {y : F (α ::: CofixWithBot F α)} :
      (Cofix.dest x).get = .some y →
      (∀ i, HasNoBot (lastFun (QPF.repr y).2 i)) →
      HasNoBot x

@[grind →]
theorem dest_isSome_of_hasNoBot {x : CofixWithBot F α} (h : HasNoBot x) :
    (Cofix.dest x).get.isSome := by
  cases h; simp [*]

/-- Every child of an `x` satisfying `HasNoBot` satisfies `HasNoBot`. -/
@[grind .]
theorem hasNoBot_lastFun {x : CofixWithBot F α} (h : HasNoBot x)
    {y : F (α ::: CofixWithBot F α)} (hd : (Cofix.dest x).get = .some y) (i) :
    HasNoBot (lastFun (QPF.repr y).2 i) := by
  cases h; grind

/--
An inhabitant of `CofixWithBot F α` without any bottom layers is an inhabitant of
`Cofix F α`.
-/
def get (x : CofixWithBot F α) (h : HasNoBot x) : Cofix F α :=
  Cofix.corec step ⟨x, h⟩
where step :
  {x : CofixWithBot F α // HasNoBot x} → F (α ::: {x : CofixWithBot F α // HasNoBot x})
  | ⟨x, h⟩ =>
    let y := (Cofix.dest x).get.get (by grind)
    let yr := (QPF.repr (F := F) y)
    QPF.abs ⟨yr.1, splitFun
      (dropFun yr.2 : _ ⟹ α)
      fun i => ⟨lastFun yr.2 i, by grind⟩
    ⟩

@[grind =]
theorem dest_get (x : CofixWithBot F α) (h : HasNoBot x) :
    Cofix.dest (get x h)
      = (TypeVec.id ::: fun z => get z.1 z.2) <$$> get.step ⟨x, h⟩ :=
  Cofix.dest_corec _ _

end QPF.CofixWithBot

end QPFTypes
