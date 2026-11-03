module

public import QPFTypes.Theory.QPF.Cofix.Basic
public import QPFTypes.Theory.PFunctor.Multivariate.M.Order

/-!
# A chain-complete partial order on `Cofix`

This file transports the order of `QPFTypes.Theory.PFunctor.Multivariate.M.Order` from
`q.P.M α` to `Cofix F α`, so that Lean's `partial_fixpoint` can define corecursive — and in
particular *non-productive* — functions into a coinductive type built with `Cofix`.

## Main definitions

* `Cofix.le`          - the order on `Cofix F α`, pulled back along `Cofix.repr`
* `Cofix.bot`         - the least element
* `Cofix.ReprChainClosed` - the hypothesis under which `Cofix F α` is chain-complete
* instances `Lean.Order.PartialOrder (Cofix F α)` and `Lean.Order.CCPO (Cofix F α)`
* `Cofix.mk_mono`     - the `@[partial_fixpoint_monotone]` lemma for the constructor
* `Cofix.mk_map_mono` - the same, stated at the level of `F`; concrete constructors are
                        instances of it

## Implementation notes

`Cofix F α` is `Quot Mcongr` over `q.P.M α`, and `QPF.abs` is only required to be a
retraction (`abs_repr`), not an isomorphism. So the "same shape" relation that the order
rests on is *not* canonical at the level of `F`: `QPF.liftR_iff` produces some polynomial
decomposition, and two separate facts about the same pair of values need not produce the
same one. That is why the order is built on `q.P.M α`, where shapes are unique, and pulled
back along `Cofix.repr`, which is a section of `Quot.mk Mcongr` (`Cofix.abs_repr`) and hence
injective. `Cofix.dest_repr` is the bridge: it rewrites one step of `M.dest ∘ Cofix.repr`
into one step of `QPF.repr ∘ Cofix.dest`.

Injectivity of `Cofix.repr` is all that `PartialOrder` needs, so that instance is
unconditional. Chain-completeness needs more: the supremum is built in `q.P.M α` and has to
be carried back, which requires `QPF.repr` applied to the supremum of a chain of representatives to be in the codomain of `QPF.repr` again; this condition is
formalized in the `Cofix.ReprChainClosed` type class. The condition holds,
in particular, for every polynomial `F` (`QPF.IsPolynomial F`).

## Reference

Adapted from `Coinductive/CoInd.lean` and `ITree/Definition.lean` of
[ISTA-PLV/coinductive](https://github.com/ISTA-PLV/coinductive).
-/

@[expose] public section

namespace QPFTypes

open MvFunctor

namespace QPF

open TypeVec MvPFunctor Lean.Order
open HasBot (botShape)

universe u v

variable {n : Nat} {F : TypeVec.{u} (n + 1) → Type u} [q : QPF F] {α : TypeVec.{u} n}
/-- A bottom shape for `F` yields one for the underlying polynomial functor. -/
instance instHasBotP [HasBot F α] : HasBot q.P α :=
  ⟨QPF.repr (botShape : F (α ::: PUnit))⟩

/-! ## `Cofix.repr` as an order embedding -/

theorem Cofix.repr_injective : Function.Injective (Cofix.repr : Cofix F α → q.P.M α) := by
  intro x y h
  rw [← Cofix.abs_repr x, ← Cofix.abs_repr y, h]

/-- One step of `Cofix.repr`. This is the bridge between the two destructors: the M-type's
`M.dest` on the representative, and `Cofix`'s own `Cofix.dest`. -/
theorem Cofix.dest_repr (y : Cofix F α) :
    M.dest q.P (Cofix.repr y) = (TypeVec.id ::: Cofix.repr) <$$> QPF.repr (Cofix.dest y) := by
  rw [Cofix.repr, M.dest_corec]
  rfl

theorem Cofix.dest_abs (m : q.P.M α) :
    Cofix.dest (Cofix.abs m : Cofix F α)
      = (TypeVec.id ::: Cofix.abs) <$$> QPF.abs (M.dest q.P m) :=
  rfl

/-! ## The order on `Cofix` -/

/-- The order on `Cofix F α`: `x` approximates `y` when their canonical M-type
representatives do. -/
abbrev Cofix.le [HasBot F α] (x y : Cofix F α) : Prop :=
  M.le q.P (Cofix.repr x) (Cofix.repr y)

instance Cofix.instPartialOrder [HasBot F α] : PartialOrder (Cofix F α) where
  rel := Cofix.le
  rel_refl := M.le_refl q.P _
  rel_trans h₁ h₂ := M.le_trans q.P h₁ h₂
  rel_antisymm h₁ h₂ := Cofix.repr_injective (M.le_antisymm q.P h₁ h₂)

@[simp]
theorem Cofix.rel_eq [HasBot F α] (x y : Cofix F α) :
    (x ⊑ y) ↔ (Cofix.repr x) ⊑ (Cofix.repr y) := by
  rfl

variable (F α) in
/--
An instance of `ReprChainClosed F` asserts the condition under which the partial
order on `Cofix F α` is chain-complete.
-/
class Cofix.ReprChainClosed extends HasBot F α where
  /--
  The supremum of a chain whose elements are all representatives of some
  equivalence class of must itself be the representative of another equivalence
  class.
  -/
  csup_mem (c : q.P.M α → Prop) (hc : chain c)
    (h : ∀ m, c m → ∃ x : Cofix F α, x.repr = m) :
    ∃ x : Cofix F α, x.repr = M.csup q.P c

instance [HasBot F α] [IsPolynomial F] : Cofix.ReprChainClosed F α where
  csup_mem c _ _ := ⟨Cofix.abs (M.csup q.P c), Cofix.repr_abs _⟩

/-! ## The bottom element -/

/-- The least element of `Cofix F α`. -/
def Cofix.bot (F : TypeVec.{u} (n + 1) → Type u) [q : QPF F] {α : TypeVec.{u} n}
    [HasBot F α] : Cofix F α :=
  Cofix.abs (M.bot q.P)

theorem Cofix.repr_bot [Cofix.ReprChainClosed F α] :
    (bot F (α := α)).repr = M.bot q.P := by
  obtain ⟨z, hz⟩ := Cofix.ReprChainClosed.csup_mem (F := F) (α := α) (fun _ => False)
    (fun _ _ h => h.elim) (fun _ h => h.elim)
  rw [M.csup_eq_bot q.P (by simp)] at hz
  rw [bot, ← hz, Cofix.abs_repr, hz]

theorem Cofix.bot_le [Cofix.ReprChainClosed F α] (y : Cofix F α) :
    bot F ⊑ y := by
  rw [Cofix.rel_eq, Cofix.repr_bot]
  exact M.bot_le q.P _

/-! ## `Cofix F α` is chain-complete -/

/--
The CCPO instance on `Cofix F α`, which enables the definition of functions via
`partial_fixpoint`.
-/
instance (priority := default + 100) Cofix.instCCPO
    [Cofix.ReprChainClosed F α] : CCPO (Cofix F α) where
  has_csup {c} hc := by
    let c' := fun m => ∃ m', c m' ∧ Cofix.repr m' = m
    have hc' : chain c' := by
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact hc _ _ hx hy
    obtain ⟨z, hz⟩ := Cofix.ReprChainClosed.csup_mem c' hc'
      (by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩)
    exists z
    intro x
    rw [Cofix.rel_eq, hz, M.csup_spec q.P hc']
    constructor
    · intro h y hy
      exact h _ ⟨y, hy, rfl⟩
    · rintro h _ ⟨m', hm', rfl⟩
      exact h m' hm'

/-! ## Coinduction for the order

These are what make the order usable without dropping down to `q.P.M α`: one step of
`Cofix.le` expressed with `Cofix`'s own destructor, plus the coinduction principle it
feeds. They are the `Cofix` analogues of the reference's `CoInd.le_unfold` and
`CoInd.le.coinduct`.
-/

/-- Every value decomposes as `⟨a, splitFun fd g⟩` under `QPF.repr ∘ Cofix.dest`. -/
theorem Cofix.exists_repr_dest (x : Cofix F α) :
    ∃ (a : q.P.A) (fd : q.P.drop.B a ⟹ α) (g : q.P.last.B a → Cofix F α),
      QPF.repr (Cofix.dest x) = ⟨a, splitFun fd g⟩ := by
  rcases h : QPF.repr (Cofix.dest x) with ⟨a, hf⟩
  exact ⟨a, dropFun hf, lastFun hf, by rw [split_dropFun_lastFun]⟩

/-- Transfer a decomposition of `QPF.repr (Cofix.dest x)` to one of
`M.dest (Cofix.repr x)`. -/
theorem Cofix.dest_repr_split {x : Cofix F α} {a : q.P.A}
    {fd : q.P.drop.B a ⟹ α} {g : q.P.last.B a → Cofix F α}
    (h : QPF.repr (Cofix.dest x) = ⟨a, splitFun fd g⟩) :
    M.dest q.P (Cofix.repr x) = ⟨a, splitFun fd (fun i => Cofix.repr (g i))⟩ := by
  erw [Cofix.dest_repr, h, MvPFunctor.appendFun_map_splitFun, id_comp]
  rfl

/-- One coinductive step of the order, stated with `Cofix.dest` rather than with the
M-type's destructor: `x` is `⊥`, or `x` and `y` have the same shape and the same
non-recursive content, and their children are related by `pred`. -/
def Cofix.LeStep [HasBot F α] (pred : Cofix F α → Cofix F α → Prop)
    (x y : Cofix F α) : Prop :=
  x = Cofix.bot F ∨
    ∃ (a : q.P.A) (fd : q.P.drop.B a ⟹ α) (g g' : q.P.last.B a → Cofix F α),
      QPF.repr (Cofix.dest x) = ⟨a, splitFun fd g⟩ ∧
      QPF.repr (Cofix.dest y) = ⟨a, splitFun fd g'⟩ ∧
      ∀ i, pred (g i) (g' i)

/-- Coinduction for `⊑`: a relation closed under `Cofix.LeStep` is contained in the
order. -/
theorem Cofix.le_coinduct [Cofix.ReprChainClosed F α]
    (pred : Cofix F α → Cofix F α → Prop)
    (step : ∀ x y, pred x y → Cofix.LeStep pred x y)
    {x y : Cofix F α} (h : pred x y) : x ⊑ y := by
  rw [Cofix.rel_eq]
  let R (u v) := ∃ x y, pred x y ∧ u = Cofix.repr x ∧ v = Cofix.repr y
  apply M.le.coinduct q.P R ?_ _ _ ⟨x, y, h, rfl, rfl⟩
  rintro _ _ ⟨x, y, hp, rfl, rfl⟩
  rcases step _ _ hp with rfl | ⟨a, fd, g, g', hx, hy, h₃⟩
  · exact Or.inl Cofix.repr_bot
  · exact Or.inr ⟨a, fd, _, _, Cofix.dest_repr_split hx, Cofix.dest_repr_split hy,
      fun i => ⟨g i, g' i, h₃ i, rfl, rfl⟩⟩

/-- The converse of `Cofix.le_coinduct`: the order itself satisfies one step. -/
theorem Cofix.le_step [Cofix.ReprChainClosed F α] {x y : Cofix F α}
    (h : x ⊑ y) : Cofix.LeStep (· ⊑ ·) x y := by
  obtain ⟨a, fd, g, hx⟩ := Cofix.exists_repr_dest x
  rw [Cofix.rel_eq] at h
  rcases M.le_dest q.P h (Cofix.dest_repr_split hx) with hb | ⟨k', hy, h₃⟩
  · exact Or.inl (Cofix.repr_injective (hb.trans Cofix.repr_bot.symm))
  · obtain ⟨b, fd', g', hy'⟩ := Cofix.exists_repr_dest y
    have hy'' := Cofix.dest_repr_split hy'
    have hab : b = a := congrArg Sigma.fst (hy''.symm.trans hy)
    subst b
    obtain ⟨hfd, hk⟩ := splitFun_inj (eq_of_heq (Sigma.mk.inj (hy''.symm.trans hy)).2)
    subst fd'
    subst k'
    exact Or.inr ⟨a, fd, g, g', hx, hy', fun i => h₃ i⟩


/-! ## Monotonicity of the constructor

`partial_fixpoint` discharges its monotonicity side conditions with the lemmas tagged
`@[partial_fixpoint_monotone]`. `Cofix.mk_mono` is stated for a *fixed* shape `a` and fixed
non-recursive content `fd`, which is exactly the form every concrete constructor
instantiates to — compare `tau_mono` and `vis_mono` in the reference's
`ITree/Definition.lean`.
-/

@[partial_fixpoint_monotone]
theorem Cofix.mk_mono {γ : Type v} [PartialOrder γ]
    [HasBot F α] [IsPolynomial F]
    (a : q.P.A) (fd : q.P.drop.B a ⟹ α) (fl : γ → q.P.last.B a → Cofix F α)
    (hfl : monotone fl) :
    monotone (fun x => Cofix.mk (QPF.abs ⟨a, splitFun fd (fl x)⟩) : γ → Cofix F α) := by
  intro x y hxy
  rw [Cofix.rel_eq]
  refine M.le.step q.P (f := fd) (g := fun i => Cofix.repr (fl x i))
    (g' := fun i => Cofix.repr (fl y i)) ?_ ?_ fun i => hfl x y hxy i
  · erw [Cofix.dest_repr, Cofix.dest_mk, IsPolynomial.repr_abs]
    set_option backward.isDefEq.respectTransparency false in
    simp only [MvPFunctor.map_eq, appendFun_comp_splitFun, id_comp, Function.comp_def]
    rfl
  · erw [Cofix.dest_repr, Cofix.dest_mk, IsPolynomial.repr_abs]
    set_option backward.isDefEq.respectTransparency false in
    simp only [MvPFunctor.map_eq, appendFun_comp_splitFun, id_comp, Function.comp_def]
    rfl

/-- `Cofix.mk_mono`, stated at the level of `F` instead of its polynomial functor: a fixed
layer `s`, whose recursive positions `ι` are filled in monotonically. A concrete constructor,
such as `cons x xs = Cofix.mk (.inr (x, xs))`, is (definitionally) of this form with
`ι := PUnit`, so its monotonicity lemma is a direct instance. -/
theorem Cofix.mk_map_mono {γ : Type v} [PartialOrder γ]
    [HasBot F α] [IsPolynomial F] {ι : Type u}
    (s : F (α ::: ι)) (f : γ → ι → Cofix F α) (hf : monotone f) :
    monotone (fun x => Cofix.mk ((TypeVec.id ::: f x) <$$> s)) := by
  rcases h : QPF.repr s with ⟨a, g⟩
  obtain rfl : s = QPF.abs ⟨a, g⟩ := by rw [← h, QPF.abs_repr]
  obtain ⟨gd, gl, rfl⟩ : ∃ gd gl, g = splitFun gd gl :=
    ⟨dropFun g, lastFun g, (split_dropFun_lastFun g).symm⟩
  have key : ∀ x, (TypeVec.id ::: f x) <$$> (QPF.abs ⟨a, splitFun gd gl⟩ : F (α ::: ι))
      = QPF.abs (⟨a, splitFun gd (fun i => f x (gl i))⟩ : q.P (α ::: Cofix F α)) := by
    intro x
    erw [← abs_map, MvPFunctor.map_eq, appendFun_comp_splitFun, id_comp]
    rfl
  simp only [key]
  exact Cofix.mk_mono (α := α) a gd _ (fun x y hxy i => hf x y hxy _)

end QPF

end QPFTypes
