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
* `CofixWithBot.mk`         - the constructor of a non-bottom layer, with monotonicity lemma
                              `CofixWithBot.mk_map_mono`
* `CofixWithBot.ofCofix`    - the inclusion of `Cofix F α` into `CofixWithBot F α`

These are the targets of the `codef` command, see `QPFTypes.Meta.Codef`.
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
      LiftPLast HasNoBot y →
      HasNoBot x

@[grind →]
theorem dest_isSome_of_hasNoBot {x : CofixWithBot F α} (h : HasNoBot x) :
    (Cofix.dest x).get.isSome := by
  cases h; simp [*]

/-- Every recursive child of the root of an `x` satisfying `HasNoBot` satisfies
`HasNoBot`. -/
theorem HasNoBot.liftP_of_dest {x : CofixWithBot F α} (h : HasNoBot x)
    {y : F (α ::: CofixWithBot F α)} (hd : (Cofix.dest x).get = .some y) :
    LiftPLast HasNoBot y := by
  cases h with
  | some hd' hc =>
    rw [hd] at hd'
    cases hd'
    exact hc

/--
An inhabitant of `CofixWithBot F α` without any bottom layers is an inhabitant of
`Cofix F α`.
-/
def get [IsPolynomial F] (x : CofixWithBot F α) (h : HasNoBot x) : Cofix F α :=
  Cofix.corec step ⟨x, h⟩
where
  step : {x : CofixWithBot F α // HasNoBot x} → F (α ::: {x : CofixWithBot F α // HasNoBot x})
  | ⟨x, h⟩ =>
    QPF.attach ((Cofix.dest x).get.get (dest_isSome_of_hasNoBot h))
      (h.liftP_of_dest (Option.some_get _).symm)

@[grind =]
theorem dest_get [IsPolynomial F] (x : CofixWithBot F α) (h : HasNoBot x) :
    Cofix.dest (get x h)
      = (TypeVec.id ::: fun z => get z.1 z.2) <$$> get.step ⟨x, h⟩ :=
  Cofix.dest_corec _ _

/-- `get.step`, at an `x` whose root is known to be `some y`. -/
theorem get_step_of_dest [IsPolynomial F] {x : CofixWithBot F α} (h : HasNoBot x)
    {y : F (α ::: CofixWithBot F α)} (hd : (Cofix.dest x).get = some y) :
    get.step ⟨x, h⟩ = QPF.attach y (h.liftP_of_dest hd) := by
  -- `get.step` mentions `(Cofix.dest x).get.get _` inside the proof passed to `attach` too,
  -- so it cannot be rewritten to `y` directly; abstract over that proof instead.
  have key : ∀ z, z = y → ∀ p : LiftP (α.PredLast HasNoBot) z,
      QPF.attach z p = QPF.attach y (h.liftP_of_dest hd) := by
    rintro _ rfl _; rfl
  exact key _ (by simp only [hd]; rfl) (h.liftP_of_dest (Option.some_get _).symm)

/-! ## Constructors -/

/-- The constructor of `CofixWithBot F α`: a non-bottom layer `x`. -/
def mk (x : F (α ::: CofixWithBot F α)) : CofixWithBot F α :=
  Cofix.mk (Comp.mk (some x))

/-- The inclusion of total values into possibly-partial ones. -/
def ofCofix : Cofix F α → CofixWithBot F α :=
  Cofix.corec fun x => (Comp.mk (some (Cofix.dest x)) : F.WithBot (α ::: Cofix F α))

@[simp, grind =]
theorem dest_mk (x : F (α ::: CofixWithBot F α)) :
    (Cofix.dest (mk x)).get = some x := by
  simp only [mk, Cofix.dest_mk]; rfl

@[simp, grind =]
theorem dest_ofCofix (x : Cofix F α) :
    (Cofix.dest (ofCofix x)).get = some ((TypeVec.id ::: ofCofix) <$$> Cofix.dest x) := by
  rw [ofCofix, Cofix.dest_corec]; rfl

/-- Total values, lifted with `ofCofix`, contain no bottom layer. -/
theorem HasNoBot.ofCofix [IsPolynomial F] (x : Cofix F α) :
    HasNoBot (CofixWithBot.ofCofix x) := by
  apply HasNoBot.coinduct (fun z => ∃ x, z = CofixWithBot.ofCofix x) _ _ ⟨x, rfl⟩
  rintro _ ⟨x, rfl⟩
  refine ⟨_, dest_ofCofix x, (QPF.liftP_iff _ _).2 ?_⟩
  rcases h : repr x.dest with ⟨a, f⟩
  refine ⟨a, (TypeVec.id ::: CofixWithBot.ofCofix) ⊚ f, ?_, fun i => ?_⟩
  · rw [← abs_repr x.dest, h]; exact (abs_map _ _).symm
  cases i using Fin.cases
  · exact fun j => ⟨_, rfl⟩
  · exact fun _ => trivial

/-- Unfolding `get` on a constructor: its children, which have no bottom layers since
`mk x` has none, are mapped with `get`. -/
theorem get_mk [IsPolynomial F] (x : F (α ::: CofixWithBot F α)) (h : (mk x).HasNoBot) :
    get (mk x) h
      = Cofix.mk ((TypeVec.id ::: fun z => get z.1 z.2) <$$>
          QPF.attach x (h.liftP_of_dest (dest_mk x))) := by
  rw [← Cofix.mk_dest (get _ _), dest_get, get_step_of_dest h (dest_mk x)]

/-- `Cofix.mk_map_mono`, for `CofixWithBot.mk`: a fixed layer `s`, whose recursive positions
`ι` are filled in monotonically. Concrete constructors, such as
`fun y => mk (x, f y)`, are (definitionally) instances of this with `ι := PUnit`. -/
@[partial_fixpoint_monotone]
theorem mk_map_mono {γ : Type v} [Lean.Order.PartialOrder γ] [IsPolynomial F] {ι : Type u}
    (s : F (α ::: ι)) (f : γ → ι → CofixWithBot F α) (hf : Lean.Order.monotone f) :
    Lean.Order.monotone (fun y => mk ((TypeVec.id ::: f y) <$$> s)) :=
  Cofix.mk_map_mono (Comp.mk (some s) : F.WithBot (α ::: ι)) f hf

end QPF.CofixWithBot

end QPFTypes
