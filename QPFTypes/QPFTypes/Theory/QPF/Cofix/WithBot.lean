module

public import QPFTypes.Theory.QPF.Cofix.Order
public import QPFTypes.Theory.QPF.Comp
public import QPFTypes.Instances.Option
import all Init.Internal.Order.Basic

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
* `CofixWithBot.elim`       - case analysis on the root layer, into another `CofixWithBot`
                              type, which sends `⊥` to `⊥`; with monotonicity lemma
                              `CofixWithBot.elim_mono`

These are the targets of the `codef` command, see `QPFTypes.Meta.Codef`.
-/

@[expose] public section

namespace QPFTypes

universe u v w

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

/-! ## `get` and `ofCofix` are mutually inverse -/

theorem dest_eq_of_get {x : CofixWithBot F α} {y : F (α ::: CofixWithBot F α)}
    (hd : (Cofix.dest x).get = some y) : Cofix.dest x = Comp.mk (some y) := by
  rw [← hd]; rfl

theorem map_mk_some {β γ : TypeVec (n + 1)} (f : β ⟹ γ) (y : F β) :
    (f <$$> (Comp.mk (some y : Option (F β)) : F.WithBot β))
      = (Comp.mk (some (f <$$> y) : Option (F γ)) : F.WithBot γ) :=
  rfl

@[simp, grind =]
theorem ofCofix_mk (y : F (α ::: Cofix F α)) :
    ofCofix (Cofix.mk y) = mk ((TypeVec.id ::: ofCofix) <$$> y) := by
  apply Cofix.ext
  rw [dest_eq_of_get (dest_ofCofix _), dest_eq_of_get (dest_mk _), Cofix.dest_mk]

/-- Pulling a total value out of `CofixWithBot`, and including it back, is the identity. -/
@[simp, grind =]
theorem ofCofix_get [IsPolynomial F] (x : CofixWithBot F α) (h : HasNoBot x) :
    ofCofix (get x h) = x := by
  let r (a b : CofixWithBot F α) : Prop := ∃ x h, a = ofCofix (get x h) ∧ b = x
  refine Cofix.bisim_rel r ?_ _ _ ⟨x, h, rfl, rfl⟩
  clear h x
  rintro a b ⟨x, h, rfl, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : F (α ::: CofixWithBot F α), (Cofix.dest b).get = some y :=
    Option.isSome_iff_exists.1 (dest_isSome_of_hasNoBot h)
  rw [dest_eq_of_get (dest_ofCofix _), dest_get, get_step_of_dest h hy, dest_eq_of_get hy,
    map_mk_some, map_mk_some]
  congr 2
  conv => rhs; rw [← val_attach y (h.liftP_of_dest hy)]
  simp only [MvFunctor.map_map, ← TypeVec.appendFun_comp_id]
  congr 2
  funext ⟨z, hz⟩
  exact Quot.sound ⟨z, hz, rfl, rfl⟩

theorem ofCofix_injective [IsPolynomial F] : Function.Injective (ofCofix (F := F) (α := α)) := by
  intro a b hab
  let r (a b : Cofix F α) : Prop := ofCofix a = ofCofix b
  refine Cofix.bisim_rel r ?_ _ _ hab
  intro a b hab
  have e := (dest_ofCofix a).symm.trans (hab ▸ dest_ofCofix b)
  replace e := Option.some.inj e
  -- `Quot.mk r` factors through `ofCofix`.
  open Classical in
  let φ (c : CofixWithBot F α) : Quot r :=
    if h : ∃ z, ofCofix z = c then Quot.mk r h.choose else Quot.mk r a
  have hφ : Quot.mk r = φ ∘ ofCofix := by
    funext z
    have h : ∃ w, ofCofix w = ofCofix z := ⟨z, rfl⟩
    simp only [Function.comp_apply, φ, dite_eq_left h]
    exact Quot.sound h.choose_spec.symm
  rw [hφ, TypeVec.appendFun_comp_id, ← MvFunctor.map_map, ← MvFunctor.map_map, e]

@[simp, grind =]
theorem get_ofCofix [IsPolynomial F] (x : Cofix F α) (h : HasNoBot (ofCofix x)) :
    get (ofCofix x) h = x :=
  ofCofix_injective (ofCofix_get _ h)

theorem get_eq_iff [IsPolynomial F] {x : CofixWithBot F α} {h : HasNoBot x} {y : Cofix F α} :
    get x h = y ↔ x = ofCofix y := by
  constructor
  · rintro rfl; exact (ofCofix_get x h).symm
  · rintro rfl; exact get_ofCofix y h

/-- `Cofix.mk_map_mono`, for `CofixWithBot.mk`: a fixed layer `s`, whose recursive positions
`ι` are filled in monotonically. Concrete constructors, such as
`fun y => mk (x, f y)`, are (definitionally) instances of this with `ι := PUnit`. -/
@[partial_fixpoint_monotone]
theorem mk_map_mono {γ : Sort w} [Lean.Order.PartialOrder γ] [IsPolynomial F] {ι : Type u}
    (s : F (α ::: ι)) (f : γ → ι → CofixWithBot F α) (hf : Lean.Order.monotone f) :
    Lean.Order.monotone (fun y => mk ((TypeVec.id ::: f y) <$$> s)) :=
  Cofix.mk_map_mono (Comp.mk (some s) : F.WithBot (α ::: ι)) f hf

/-- Monotonicity of a family of children `Fin (k + 1) → β`, given by `Fin.cases`. Used by
`qpf_mk_mono`, which instantiates `mk_map_mono` with `ι := Fin k`, see `QPFTypes.Meta.QPFCtor`. -/
theorem monotone_finCases {γ : Sort v} [Lean.Order.PartialOrder γ] {β : Sort w}
    [Lean.Order.PartialOrder β] {k : Nat} (v : γ → β) (f : γ → Fin k → β)
    (hv : Lean.Order.monotone v) (hf : Lean.Order.monotone f) :
    Lean.Order.monotone (fun z => Fin.cases (motive := fun _ => β) (v z) (f z)) := by
  apply Lean.Order.monotone_of_monotone_apply
  intro i
  induction i using Fin.cases with
  | zero => simpa using hv
  | succ i => simpa using Lean.Order.monotone_apply i f hf

/-- Monotone functions into a `CCPO` form an admissible predicate. `codef` uses this to prove,
by fixpoint induction, that the functions it defines with `partial_fixpoint` are monotone in
their possibly-partial arguments, see `QPFTypes.Meta.Codef`. -/
theorem admissible_monotone {γ : Sort v} [Lean.Order.PartialOrder γ] {β : Sort w}
    [Lean.Order.CCPO β] : Lean.Order.admissible (fun f : γ → β => Lean.Order.monotone f) := by
  unfold Lean.Order.admissible Lean.Order.monotone
  intro c hc h a b hab
  rw [← Lean.Order.fun_csup_eq]
  apply Lean.Order.csup_le
  rintro _ ⟨f, hf, rfl⟩
  exact Lean.Order.PartialOrder.rel_trans (h f hf a b hab)
    (Lean.Order.le_csup (Lean.Order.chain_apply hc b) ⟨f, hf, rfl⟩)

/-! ## Eliminator -/

section Elim

variable {m : Nat} {G : TypeFun.{v} (m + 1)} [QPF G] {β : TypeVec.{v} m}

/-- Case analysis on the root layer of `x`: `k y` if the root is `some y`, and `⊥` otherwise.

The result lives in a `CofixWithBot` type, so that there is a `⊥` to return. This is what
`@[qpf_elim]` translates the destructors of total values into, see `QPFTypes.Meta.QPFElim`. -/
def elim (x : CofixWithBot F α) (k : F (α ::: CofixWithBot F α) → CofixWithBot G β) :
    CofixWithBot G β :=
  (Cofix.dest x).get.elim (Cofix.bot _) k

@[simp, grind =]
theorem elim_mk (y : F (α ::: CofixWithBot F α))
    (k : F (α ::: CofixWithBot F α) → CofixWithBot G β) : elim (mk y) k = k y := by
  simp only [elim, dest_mk]; rfl

theorem elim_bot [IsPolynomial F] (k : F (α ::: CofixWithBot F α) → CofixWithBot G β) :
    elim (Cofix.bot F.WithBot (α := α)) k = Cofix.bot _ := by
  simp only [elim, Cofix.bot]
  erw [Cofix.dest_corec]
  rfl

@[simp, grind =]
theorem elim_ofCofix (x : Cofix F α) (k : F (α ::: CofixWithBot F α) → CofixWithBot G β) :
    elim (ofCofix x) k = k ((TypeVec.id ::: ofCofix) <$$> Cofix.dest x) := by
  simp only [elim, dest_ofCofix]; rfl

/-- `elim` is monotone in the scrutinee and in the continuation. Monotonicity of the
continuation `k z` is stated on layers `(TypeVec.id ::: g) <$$> s`, in `z` and in the
children `g` separately, since that is the form in which two related layers are given. -/
@[partial_fixpoint_monotone]
theorem elim_mono [IsPolynomial F] [IsPolynomial G] {δ : Sort w} [Lean.Order.PartialOrder δ]
    (x : δ → CofixWithBot F α) (hx : Lean.Order.monotone x)
    (k : δ → F (α ::: CofixWithBot F α) → CofixWithBot G β)
    (hk₁ : ∀ {ι : Type u} (s : F (α ::: ι)) (g : ι → CofixWithBot F α),
      Lean.Order.monotone (fun z => k z ((TypeVec.id ::: g) <$$> s)))
    (hk₂ : ∀ {ι : Type u} (s : F (α ::: ι)) (z : δ),
      Lean.Order.monotone (fun g : ι → CofixWithBot F α => k z ((TypeVec.id ::: g) <$$> s))) :
    Lean.Order.monotone (fun z => elim (x z) (k z)) := by
  intro z₁ z₂ hz
  rcases Cofix.le_step (hx z₁ z₂ hz) with hb | ⟨a, fd, g, g', h₁, h₂, hg⟩
  · show Lean.Order.PartialOrder.rel (elim _ _) _
    rw [hb, elim_bot]; exact Cofix.bot_le _
  · -- Both roots are the layer `⟨a, fd⟩`, with the children `g`, resp. `g'`, filled in.
    have key : ∀ (x : CofixWithBot F α) (g : _ → CofixWithBot F α),
        QPF.repr (Cofix.dest x) = ⟨a, splitFun fd g⟩ →
        Cofix.dest x = (TypeVec.id ::: g) <$$>
          (QPF.abs ⟨a, splitFun fd _root_.id⟩ : F.WithBot (α ::: _)) := by
      intro x g h
      rw [← QPF.abs_repr (Cofix.dest x), h]
      symm
      erw [← QPF.abs_map, MvPFunctor.map_eq, appendFun_comp_splitFun, id_comp]
      rfl
    simp only [elim, key _ _ h₁, key _ _ h₂]
    generalize (QPF.abs ⟨a, splitFun fd _root_.id⟩ : F.WithBot (α ::: _)) = s
    rcases s with _ | s
    · exact Lean.Order.PartialOrder.rel_refl
    · exact Lean.Order.PartialOrder.rel_trans (hk₁ s g z₁ z₂ hz) (hk₂ s z₂ g g' hg)

end Elim

end QPF.CofixWithBot

end QPFTypes
