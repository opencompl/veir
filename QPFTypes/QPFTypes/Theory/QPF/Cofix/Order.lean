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
be carried back, which requires `Cofix.repr` to be onto as well — i.e.
`QPF.IsPolynomial F`. This mirrors the reference implementation, whose `PF` class likewise
demands an isomorphism to a polynomial functor and explicitly does not support quotients.

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

@[simp]
theorem Cofix.abs_repr_eq (x : Cofix F α) : Cofix.abs (Cofix.repr x) = x :=
  Cofix.abs_repr x

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
theorem Cofix.rel_eq_le [HasBot F α] (x y : Cofix F α) :
    (x ⊑ y) = M.le q.P (Cofix.repr x) (Cofix.repr y) :=
  rfl

/-! ## The bottom element -/

/-- The least element of `Cofix F α`: corecursively repeat `botShape` forever. -/
def Cofix.bot (F : TypeVec.{u} (n + 1) → Type u) [q : QPF F] {α : TypeVec.{u} n}
    [HasBot F α] : Cofix F α :=
  Cofix.corec (fun _ : PUnit => (botShape : F (α ::: PUnit))) ⟨⟩

theorem Cofix.bot_eq_abs [HasBot F α] :
    Cofix.bot F (α := α) = Cofix.abs (M.bot q.P) :=
  rfl

theorem Cofix.repr_bot [HasBot F α] [IsPolynomial F] :
    Cofix.repr (Cofix.bot F (α := α)) = M.bot q.P := by
  rw [Cofix.bot_eq_abs, Cofix.repr_abs]

theorem Cofix.bot_le [HasBot F α] [IsPolynomial F] (y : Cofix F α) :
    Cofix.bot F ⊑ y := by
  rw [Cofix.rel_eq_le, Cofix.repr_bot]
  exact M.bot_le q.P _

/-! ## `Cofix F α` is chain-complete -/

theorem Cofix.chain_comap [HasBot F α] [IsPolynomial F]
    {c : Cofix F α → Prop} (hc : chain c) : chain (fun m : q.P.M α => c (Cofix.abs m)) := by
  intro m₁ m₂ h₁ h₂
  rcases hc _ _ h₁ h₂ with h | h
  · exact Or.inl (by simpa [Cofix.repr_abs] using h)
  · exact Or.inr (by simpa [Cofix.repr_abs] using h)

/-- `Cofix F α` is a chain-complete partial order, which is what lets Lean's
`partial_fixpoint` target a coinductive type built with `Cofix`.

The supremum is computed in `q.P.M α` and carried back along the bijection; this is where
`IsPolynomial` is needed, since without it `Cofix.repr` need not be onto. -/
instance (priority := default + 100) Cofix.instCCPO
    [HasBot F α] [IsPolynomial F] : CCPO (Cofix F α) where
  has_csup {c} hc := by
    refine ⟨Cofix.abs (M.csup q.P (fun m => c (Cofix.abs m))), fun x => ?_⟩
    rw [Cofix.rel_eq_le, Cofix.repr_abs]
    refine (M.csup_spec q.P (Cofix.chain_comap hc) (Cofix.repr x)).trans ⟨?_, ?_⟩
    · intro h y hy
      rw [Cofix.rel_eq_le]
      exact h (Cofix.repr y) (by rwa [Cofix.abs_repr_eq])
    · intro h m hm
      have hm' := h (Cofix.abs m) hm
      rwa [Cofix.rel_eq_le, Cofix.repr_abs] at hm'
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
theorem Cofix.le_coinduct [HasBot F α] [IsPolynomial F]
    (pred : Cofix F α → Cofix F α → Prop)
    (step : ∀ x y, pred x y → Cofix.LeStep pred x y)
    {x y : Cofix F α} (h : pred x y) : x ⊑ y := by
  rw [Cofix.rel_eq_le]
  apply M.le.coinduct q.P
    (fun u v => ∃ x y : Cofix F α, pred x y ∧ u = Cofix.repr x ∧ v = Cofix.repr y)
    _ _ _ ⟨x, y, h, rfl, rfl⟩
  rintro u v ⟨x', y', hp, rfl, rfl⟩
  rcases step x' y' hp with hb | ⟨a, fd, g, g', hx, hy, h₃⟩
  · exact Or.inl (by rw [hb, Cofix.repr_bot])
  · exact Or.inr ⟨a, fd, _, _, Cofix.dest_repr_split hx, Cofix.dest_repr_split hy,
      fun i => ⟨g i, g' i, h₃ i, rfl, rfl⟩⟩

/-- The converse of `Cofix.le_coinduct`: the order itself satisfies one step. -/
theorem Cofix.le_step [HasBot F α] [IsPolynomial F] {x y : Cofix F α}
    (h : x ⊑ y) : Cofix.LeStep (· ⊑ ·) x y := by
  obtain ⟨a, fd, g, hx⟩ := Cofix.exists_repr_dest x
  rw [Cofix.rel_eq_le] at h
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
  rw [Cofix.rel_eq_le]
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
