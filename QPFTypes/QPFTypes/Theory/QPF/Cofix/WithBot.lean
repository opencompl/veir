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

/-- `get.step`, at an `x` whose root is known to be `some y`. -/
theorem get_step_of_dest {x : CofixWithBot F α} (h : HasNoBot x)
    {y : F (α ::: CofixWithBot F α)} (hd : (Cofix.dest x).get = some y) :
    get.step ⟨x, h⟩ = QPF.abs (F := F) (α := α ::: {x : CofixWithBot F α // HasNoBot x})
      ⟨(QPF.repr y).1, splitFun (dropFun (QPF.repr y).2 : _ ⟹ α)
        fun i => ⟨lastFun (QPF.repr y).2 i, hasNoBot_lastFun h hd i⟩⟩ := by
  -- `get.step` mentions `(Cofix.dest x).get.get _` inside the proofs of its subtypes too,
  -- so it cannot be rewritten to `y` directly; abstract over those proofs instead.
  have key : ∀ z, z = y → ∀ p : ∀ i, HasNoBot (lastFun (QPF.repr z).2 i),
      QPF.abs (F := F) (α := α ::: {x : CofixWithBot F α // HasNoBot x})
        ⟨(QPF.repr z).1, splitFun (dropFun (QPF.repr z).2 : _ ⟹ α)
          fun i => ⟨lastFun (QPF.repr z).2 i, p i⟩⟩
      = QPF.abs (F := F) (α := α ::: {x : CofixWithBot F α // HasNoBot x})
        ⟨(QPF.repr y).1, splitFun (dropFun (QPF.repr y).2 : _ ⟹ α)
          fun i => ⟨lastFun (QPF.repr y).2 i, hasNoBot_lastFun h hd i⟩⟩ := by
    rintro _ rfl _; rfl
  have e : ∀ pf, ((Cofix.dest x).get).get pf = y := by
    intro pf; simp only [hd]; rfl
  exact key _ (e _) _

/-! ## Constructors -/

/-- The constructor of `CofixWithBot F α`: a non-bottom layer `x`. -/
def mk (x : F (α ::: CofixWithBot F α)) : CofixWithBot F α :=
  Cofix.mk (Comp.mk (some x))

@[simp, grind =]
theorem dest_mk (x : F (α ::: CofixWithBot F α)) :
    (Cofix.dest (mk x)).get = some x := by
  simp only [mk, Cofix.dest_mk]; rfl

/-- The inclusion of total values into possibly-partial ones. -/
def ofCofix : Cofix F α → CofixWithBot F α :=
  Cofix.corec fun x => (Comp.mk (some (Cofix.dest x)) : F.WithBot (α ::: Cofix F α))

@[simp, grind =]
theorem dest_ofCofix (x : Cofix F α) :
    (Cofix.dest (ofCofix x)).get = some ((TypeVec.id ::: ofCofix) <$$> Cofix.dest x) := by
  rw [ofCofix, Cofix.dest_corec]; rfl

/-- For polynomial functors, `QPF.repr` commutes with `map`. -/
theorem _root_.QPFTypes.QPF.IsPolynomial.repr_map {F : TypeFun.{u} n} [QPF F] [IsPolynomial F]
    {β γ : TypeVec n} (g : β ⟹ γ) (y : F β) :
    QPF.repr (g <$$> y) = g <$$> QPF.repr y := by
  conv => lhs; rw [← QPF.abs_repr y, ← QPF.abs_map, IsPolynomial.repr_abs]

/-- Total values, lifted with `ofCofix`, contain no bottom layer. -/
theorem HasNoBot.ofCofix [IsPolynomial F] (x : Cofix F α) :
    HasNoBot (CofixWithBot.ofCofix x) := by
  apply HasNoBot.coinduct (fun z => ∃ x, z = CofixWithBot.ofCofix x) _ _ ⟨x, rfl⟩
  rintro _ ⟨x, rfl⟩
  refine ⟨_, dest_ofCofix x, ?_⟩
  rw [IsPolynomial.repr_map]
  generalize QPF.repr (Cofix.dest x) = p
  rcases p with ⟨a, f⟩
  exact fun i => ⟨_, rfl⟩

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
