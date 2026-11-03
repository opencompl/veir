module

public import QPFTypes.Theory.PFunctor.Multivariate.M
public import QPFTypes.Theory.TypeFun

/-!
# A chain-complete partial order on the M-type of a multivariate polynomial functor

Lean's `partial_fixpoint` elaborator can define a (possibly non-productive) recursive
function into a type `α` as long as `α` has a `Lean.Order.CCPO` instance and the
constructors used in the body are known to be monotone. This file provides that
structure for `MvPFunctor.M P α`, the greatest fixpoint of a polynomial functor.

## Main definitions

* `M.bot`  - the least element: the infinite tree all of whose nodes carry `botShape`
* `M.le`   - the order, defined coinductively: `x ⊑ y` when `x = ⊥`, or `x` and `y` have the
             same shape and identical non-recursive content, and their children are
             pairwise related
* `M.csup` - the supremum of a chain
* instances `Lean.Order.PartialOrder (P.M α)` and `Lean.Order.CCPO (P.M α)`

## Implementation notes

The order needs a bottom element, which is why every declaration here takes an
instance of `[HasBot P α]`, which picks a shape together with its non-recursive
content, and `M.bot` is the infinite tree built from repeating this shape.

## Reference

Adapted from `Coinductive/CoInd.lean` of [ISTA-PLV/coinductive](https://github.com/ISTA-PLV/coinductive),
which does the same for a coinductive type built from a functor that is *isomorphic* to a
polynomial functor.
-/

@[expose] public section

namespace QPFTypes

/-! ## `HasBot` typeclass -/

/--
An instance of `HasBot F α` gives an inhabitant of `F (α ::: PUnit)`,
which is the basic shape from which the bottom element of `Cofix F α` is
constructed.

`HasBot F α` is thus isomorphic to, and implied by, `Inhabited (F (α ::: PUnit))`.
-/
class HasBot (F : TypeFun.{u, v} (n + 1)) (α : TypeVec n) where
  botShape : F (α ::: PUnit)

instance HasBot.ofInhabited [Inhabited (F (α ::: PUnit))] : HasBot F α where
  botShape := default
open HasBot (botShape)

namespace MvPFunctor
open TypeVec MvFunctor Lean.Order

universe u
variable {n : Nat} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n}

/--
Specifically for a polynomial functor, we can decompose botShape into the
underlying sigma type.
-/
private theorem exists_botShape_eq [HasBot P α] :
    ∃ a f g, (botShape : P (α ::: _)) = ⟨a, splitFun f g⟩ := by
  let ⟨a, f'⟩ := (botShape : P (α ::: _))
  exists a, dropFun f', lastFun f'
  grind

/-! ## The bottom element -/

/-- The least element of `P.M α`: the infinite tree every node of which carries
the shape and non-recursive content given by `botShape`. -/
def M.bot [HasBot P α] : P.M α :=
  M.corec P (fun _ : PUnit => botShape) ⟨⟩

@[simp, grind =]
theorem M.dest_bot [HasBot P α] :
    M.dest P (M.bot P (α := α)) = (TypeVec.id ::: fun _ => M.bot P) <$$> botShape := by
  rw [M.bot, M.dest_corec]

/-! ## The order -/

/-- The coinductive order on `P.M α`: `x` approximates `y` when either `x` is `⊥`, or the
two agree on the shape and on all non-recursive content, and each child of `x`
approximates the corresponding child of `y`.
-/
coinductive M.le [HasBot P α] : P.M α → P.M α → Prop where
  | bot {y : P.M α} : M.le (M.bot P) y
  | step {x y : P.M α} {a : P.A} {f : P.drop.B a ⟹ α} {g g' : P.last.B a → P.M α} :
      M.dest P x = ⟨a, splitFun f g⟩ → M.dest P y = ⟨a, splitFun f g'⟩ →
      (∀ i, M.le (g i) (g' i)) → M.le x y

@[grind .]
theorem M.bot_le [HasBot P α] (y : P.M α) : M.le P (M.bot P) y := .bot P

/-- Only `⊥` approximates `⊥`. -/
@[simp, grind =]
theorem M.le_bot_iff [HasBot P α] {x : P.M α} : M.le P x (M.bot P) ↔ x = M.bot P := by
  refine ⟨fun h => ?_, fun h => h ▸ M.bot_le P _⟩
  apply M.bisim
  apply IsBisim.coinduct P (fun u v => M.le P u (M.bot P) ∧ v = M.bot P) _ _ _ ⟨h, rfl⟩
  rintro u v ⟨hu, rfl⟩
  obtain ⟨a₀, f₀, g₀, hbs⟩ := exists_botShape_eq P (α := α)
  have hbot : M.dest P (M.bot P) = ⟨a₀, splitFun f₀ fun _ => M.bot P⟩ := by
    erw [M.dest_bot, hbs, appendFun_map_splitFun, id_comp]; rfl
  cases hu with
  | bot =>
    exact ⟨a₀, f₀, _, _, hbot, hbot, fun _ => ⟨M.bot_le P _, rfl⟩⟩
  | @step _ _ a f g g' h1 h2 h3 =>
    rw [hbot] at h2
    obtain rfl : a = a₀ := (congrArg Sigma.fst h2).symm
    obtain ⟨rfl, rfl⟩ := splitFun_inj (eq_of_heq (Sigma.mk.inj h2).2).symm
    exact ⟨a, f, g, _, h1, hbot, fun i => ⟨h3 i, rfl⟩⟩

/-- Destructing `M.le` against a *chosen* decomposition of `x`.

`M.le` quantifies existentially over the shape, but in practice one always destructs
`M.dest P x` first and then wants the matching decomposition of `M.dest P y`. This lemma
does that re-indexing once, so the proofs below need not each unify shapes by hand. -/
theorem M.le_dest [HasBot P α] {x y : P.M α} {a : P.A}
    {f : P.drop.B a ⟹ α} {g : P.last.B a → P.M α}
    (h : M.le P x y) (hx : M.dest P x = ⟨a, splitFun f g⟩) :
    x = M.bot P ∨ ∃ g' : P.last.B a → P.M α,
      M.dest P y = ⟨a, splitFun f g'⟩ ∧ ∀ i, M.le P (g i) (g' i) := by
  cases h with
  | bot => exact Or.inl rfl
  | @step _ _ b fb gb gb' hx' hy' h3 =>
    obtain rfl : a = b := congrArg Sigma.fst (hx.symm.trans hx')
    obtain ⟨rfl, rfl⟩ := splitFun_inj (eq_of_heq (Sigma.mk.inj (hx.symm.trans hx')).2)
    exact Or.inr ⟨gb', hy', h3⟩

/-- Every element decomposes as `⟨a, splitFun f g⟩`. This is `M.dest` followed by
`split_dropFun_lastFun`; having it as an `∃` keeps the proofs below readable. -/
theorem M.exists_dest (x : P.M α) :
    ∃ (a : P.A) (f : P.drop.B a ⟹ α) (g : P.last.B a → P.M α),
      M.dest P x = ⟨a, splitFun f g⟩ := by
  rcases h : M.dest P x with ⟨a, hf⟩
  exact ⟨a, dropFun hf, lastFun hf, by rw [split_dropFun_lastFun]⟩

/-- If `x` has the same one-step shape as `⊥` and each of its children is below the
corresponding child of `⊥`, then `x = ⊥`. This is the shape in which the `⊥` case shows
up in the transitivity and antisymmetry proofs. -/
theorem M.eq_bot_of_le_dest_bot [HasBot P α] {x : P.M α} {a : P.A}
    {f : P.drop.B a ⟹ α} {g gv : P.last.B a → P.M α}
    (hx : M.dest P x = ⟨a, splitFun f g⟩)
    (hv : M.dest P (M.bot P (α := α)) = ⟨a, splitFun f gv⟩)
    (h3 : ∀ i, M.le P (g i) (gv i)) : x = M.bot P := by
  obtain ⟨a₀, f₀, g₀, hbs⟩ := exists_botShape_eq P (α := α)
  have hbot : M.dest P (M.bot P) = ⟨a₀, splitFun f₀ fun _ => M.bot P⟩ := by
    erw [M.dest_bot, hbs, appendFun_map_splitFun, id_comp]; rfl
  obtain rfl : a = a₀ := congrArg Sigma.fst (hv.symm.trans hbot)
  obtain ⟨rfl, rfl⟩ := splitFun_inj (eq_of_heq (Sigma.mk.inj (hv.symm.trans hbot)).2)
  obtain rfl : g = fun _ => M.bot P (α := α) := funext fun i => (M.le_bot_iff P).mp (h3 i)
  exact M.ext P x _ (hx.trans hbot.symm)

/-! ## `P.M α` is a partial order -/

theorem M.le_refl [HasBot P α] (x : P.M α) : M.le P x x := by
  apply M.le.coinduct P (fun u v => u = v) _ _ _ rfl
  rintro u v rfl
  obtain ⟨a, f, g, hu⟩ := M.exists_dest P u
  exact Or.inr ⟨a, f, g, g, hu, hu, fun _ => rfl⟩

theorem M.le_trans [HasBot P α] {x y z : P.M α}
    (hxy : M.le P x y) (hyz : M.le P y z) : M.le P x z := by
  apply M.le.coinduct P (fun u w => ∃ v, M.le P u v ∧ M.le P v w) _ _ _ ⟨y, hxy, hyz⟩
  rintro u w ⟨v, h1, h2⟩
  obtain ⟨a, f, g, hu⟩ := M.exists_dest P u
  rcases M.le_dest P h1 hu with rfl | ⟨gv, hv, h3⟩
  · exact Or.inl rfl
  rcases M.le_dest P h2 hv with rfl | ⟨gw, hw, h4⟩
  · exact Or.inl (M.eq_bot_of_le_dest_bot P hu hv h3)
  · exact Or.inr ⟨a, f, g, gw, hu, hw, fun i => ⟨gv i, h3 i, h4 i⟩⟩

theorem M.le_antisymm [HasBot P α] {x y : P.M α}
    (hxy : M.le P x y) (hyx : M.le P y x) : x = y := by
  apply M.bisim
  apply IsBisim.coinduct P (fun u v => M.le P u v ∧ M.le P v u) _ _ _ ⟨hxy, hyx⟩
  rintro u v ⟨h1, h2⟩
  obtain ⟨a₀, f₀, g₀, hbs⟩ := exists_botShape_eq P (α := α)
  have hbot : M.dest P (M.bot P) = ⟨a₀, splitFun f₀ fun _ => M.bot P⟩ := by
    erw [M.dest_bot, hbs, appendFun_map_splitFun, id_comp]; rfl
  obtain ⟨a, f, g, hu⟩ := M.exists_dest P u
  rcases M.le_dest P h1 hu with rfl | ⟨gv, hv, h3⟩
  · -- `u = ⊥`, hence `v = ⊥` as well
    obtain rfl : v = M.bot P := (M.le_bot_iff P).mp h2
    exact ⟨a₀, f₀, _, _, hbot, hbot, fun _ => ⟨M.bot_le P _, M.bot_le P _⟩⟩
  rcases M.le_dest P h2 hv with rfl | ⟨gu, hu', h4⟩
  · -- `v = ⊥`, so all children of `u` are `⊥`, hence `u = ⊥` too
    obtain rfl : u = M.bot P := M.eq_bot_of_le_dest_bot P hu hv h3
    exact ⟨a₀, f₀, _, _, hbot, hbot, fun _ => ⟨M.bot_le P _, M.bot_le P _⟩⟩
  · obtain ⟨-, rfl⟩ := splitFun_inj (eq_of_heq (Sigma.mk.inj (hu.symm.trans hu')).2)
    exact ⟨a, f, g, gv, hu, hv, fun i => ⟨h3 i, h4 i⟩⟩

instance M.instPartialOrder [HasBot P α] : PartialOrder (P.M α) where
  rel := M.le P
  rel_refl := M.le_refl P _
  rel_trans := M.le_trans P
  rel_antisymm := M.le_antisymm P


/-! ## Comparing chain elements

The supremum below is built by picking *some* non-`⊥` element of the chain and reading its
shape off. These lemmas say that choice does not matter: any two non-`⊥` elements of a
chain agree on shape and on non-recursive content, and their children are comparable.

Each statement takes the two decompositions `M.dest P tᵢ = ⟨aᵢ, hfᵢ⟩` as hypotheses with
`aᵢ`/`hfᵢ` free, so that callers can `subst` the resulting shape equation and stay
cast-free.
-/

private theorem M.dest_split {x : P.M α} {a : P.A} {hf : P.B a ⟹ (α ::: P.M α)}
    (hd : M.dest P x = ⟨a, hf⟩) :
    M.dest P x = ⟨a, splitFun (dropFun hf) (lastFun hf)⟩ := by
  rw [hd, split_dropFun_lastFun]

/-- A non-`⊥` element has the same shape as anything above it. -/
theorem M.shape_eq_of_le [HasBot P α] {x y : P.M α} {a₁ a₂ : P.A}
    {hf₁ : P.B a₁ ⟹ (α ::: P.M α)} {hf₂ : P.B a₂ ⟹ (α ::: P.M α)}
    (h : M.le P x y) (hx : x ≠ M.bot P)
    (hd₁ : M.dest P x = ⟨a₁, hf₁⟩) (hd₂ : M.dest P y = ⟨a₂, hf₂⟩) : a₁ = a₂ := by
  rcases M.le_dest P h (M.dest_split P hd₁) with hb | ⟨g', hy, _⟩
  · exact absurd hb hx
  · exact congrArg Sigma.fst (hy.symm.trans hd₂)

/-- Once the shapes are known equal, a non-`⊥` element shares its non-recursive content
with anything above it, and its children are pointwise below the other's. -/
theorem M.content_children_of_le [HasBot P α] {x y : P.M α} {a : P.A}
    {hf₁ hf₂ : P.B a ⟹ (α ::: P.M α)}
    (h : M.le P x y) (hx : x ≠ M.bot P)
    (hd₁ : M.dest P x = ⟨a, hf₁⟩) (hd₂ : M.dest P y = ⟨a, hf₂⟩) :
    dropFun hf₁ = dropFun hf₂ ∧ ∀ o, M.le P (lastFun hf₁ o) (lastFun hf₂ o) := by
  rcases M.le_dest P h (M.dest_split P hd₁) with hb | ⟨g', hy, h3⟩
  · exact absurd hb hx
  · have heq : splitFun (dropFun hf₁) g' = hf₂ :=
      eq_of_heq (Sigma.mk.inj (hy.symm.trans hd₂)).2
    subst heq
    set_option backward.isDefEq.respectTransparency false in
    refine ⟨by simp, fun o => ?_⟩
    simp only [lastFun_splitFun]
    exact h3 o

/-- Any two non-`⊥` elements of a chain have the same shape. -/
theorem M.chain_shape_eq [HasBot P α] {c : P.M α → Prop} (hc : chain c)
    {t₁ t₂ : P.M α} (h₁ : c t₁) (h₂ : c t₂) (hb₁ : t₁ ≠ M.bot P) (hb₂ : t₂ ≠ M.bot P)
    {a₁ a₂ : P.A} {hf₁ : P.B a₁ ⟹ (α ::: P.M α)} {hf₂ : P.B a₂ ⟹ (α ::: P.M α)}
    (hd₁ : M.dest P t₁ = ⟨a₁, hf₁⟩) (hd₂ : M.dest P t₂ = ⟨a₂, hf₂⟩) : a₁ = a₂ := by
  rcases hc t₁ t₂ h₁ h₂ with h | h
  · exact M.shape_eq_of_le P h hb₁ hd₁ hd₂
  · exact (M.shape_eq_of_le P h hb₂ hd₂ hd₁).symm

/-- Any two non-`⊥` elements of a chain carry the same non-recursive content, and their
children are comparable. -/
theorem M.chain_content_eq [HasBot P α] {c : P.M α → Prop} (hc : chain c)
    {t₁ t₂ : P.M α} (h₁ : c t₁) (h₂ : c t₂) (hb₁ : t₁ ≠ M.bot P) (hb₂ : t₂ ≠ M.bot P)
    {a : P.A} {hf₁ hf₂ : P.B a ⟹ (α ::: P.M α)}
    (hd₁ : M.dest P t₁ = ⟨a, hf₁⟩) (hd₂ : M.dest P t₂ = ⟨a, hf₂⟩) :
    dropFun hf₁ = dropFun hf₂ ∧
      ∀ o, M.le P (lastFun hf₁ o) (lastFun hf₂ o) ∨ M.le P (lastFun hf₂ o) (lastFun hf₁ o) := by
  rcases hc t₁ t₂ h₁ h₂ with h | h
  · obtain ⟨hd, hk⟩ := M.content_children_of_le P h hb₁ hd₁ hd₂
    exact ⟨hd, fun o => Or.inl (hk o)⟩
  · obtain ⟨hd, hk⟩ := M.content_children_of_le P h hb₂ hd₂ hd₁
    exact ⟨hd.symm, fun o => Or.inr (hk o)⟩
/-! ## Suprema of chains -/

@[simp]
theorem M.rel_eq_le [HasBot P α] (x y : P.M α) : (x ⊑ y) = M.le P x y := rfl

/-- The non-recursive content of `x`, i.e. the `α`-labelled positions at its root. -/
def M.contents (x : P.M α) : (P.B (M.dest P x).1).drop ⟹ α :=
  dropFun (M.dest P x).2

/-- The chain of `o`-th children of those non-`⊥` elements of `c` that have shape `a`.

The shape `a` is fixed and the decomposition `hf` is existentially quantified *at that
shape*, which is what keeps this definition — and every proof about it — transport-free. -/
def M.subchain [HasBot P α] (c : P.M α → Prop) (a : P.A)
    (o : (P.B a).last) : P.M α → Prop :=
  fun c' => ∃ (t : P.M α) (hf : P.B a ⟹ (α ::: P.M α)),
    c t ∧ t ≠ M.bot P ∧ M.dest P t = ⟨a, hf⟩ ∧ c' = lastFun hf o

open Classical in
/-- The supremum of a chain `c`.

If `c` has a non-`⊥` element, the shape and non-recursive content of the supremum are read
off an arbitrary such element — `M.chain_shape_eq` and `M.chain_content_eq` say the choice
does not matter — and each child is the supremum of the corresponding `M.subchain`.
Otherwise every element of `c` is `⊥`, and so is the supremum. -/
noncomputable def M.csup [HasBot P α] (c : P.M α → Prop) : P.M α :=
  M.corec P (fun d : P.M α → Prop =>
    if h : ∃ t, d t ∧ t ≠ M.bot P then
      ⟨(M.dest P (choose h)).1,
        splitFun (M.contents P (choose h))
          (fun o => M.subchain P d (M.dest P (choose h)).1 o)⟩
    else
      (TypeVec.id ::: fun _ : PUnit => d) <$$> botShape) c

/-- A chain all of whose elements are `⊥` has supremum `⊥`. -/
theorem M.dest_csup_of_neg [HasBot P α] {c : P.M α → Prop}
    (h : ¬∃ t, c t ∧ t ≠ M.bot P) :
    M.dest P (M.csup P c) = (TypeVec.id ::: fun _ : PUnit => M.csup P c) <$$> botShape := by
  rw [M.csup, M.dest_corec]
  set_option backward.isDefEq.respectTransparency false in
  split
  · exact absurd ‹_› h
  · rw [← MvFunctor.comp_map, ← appendFun_comp, id_comp]
    rfl

open Classical in
/-- One step of the supremum of a chain with a non-`⊥` element, read off the chosen
witness. -/
theorem M.dest_csup_of_pos [HasBot P α] {c : P.M α → Prop}
    (hex : ∃ t, c t ∧ t ≠ M.bot P) :
    M.dest P (M.csup P c) =
      ⟨(M.dest P (choose hex)).1,
        splitFun (M.contents P (choose hex))
          (fun o => M.csup P (M.subchain P c (M.dest P (choose hex)).1 o))⟩ := by
  rw [M.csup, M.dest_corec]
  set_option backward.isDefEq.respectTransparency false in
  split
  · simp only [MvPFunctor.map_eq, appendFun_comp_splitFun, id_comp, Function.comp_def]
    rfl
  · exact absurd hex ‹_›

theorem M.csup_eq_bot [HasBot P α] {c : P.M α → Prop}
    (h : ¬∃ t, c t ∧ t ≠ M.bot P) : M.csup P c = M.bot P := by
  apply M.bisim
  apply IsBisim.coinduct P
    (fun u v => ∃ d : P.M α → Prop, (¬∃ t, d t ∧ t ≠ M.bot P) ∧ u = M.csup P d ∧ v = M.bot P)
    _ _ _ ⟨c, h, rfl, rfl⟩
  rintro u v ⟨d, hd, rfl, rfl⟩
  obtain ⟨a, f, g, hbs⟩ := exists_botShape_eq P (α := α)
  refine ⟨a, f, (fun _ => M.csup P d), (fun _ => M.bot P), ?_, ?_, fun _ => ⟨d, hd, rfl, rfl⟩⟩
  · erw [M.dest_csup_of_neg P hd, hbs, appendFun_map_splitFun, id_comp]; rfl
  · erw [M.dest_bot, hbs, appendFun_map_splitFun, id_comp]; rfl

open Classical in
/-- One step of the supremum of a chain, read off *any* non-`⊥` element `t` of the chain. -/
theorem M.dest_csup [HasBot P α] {c : P.M α → Prop} (hc : chain c)
    {t : P.M α} (ht : c t) (hb : t ≠ M.bot P)
    {a : P.A} {hf : P.B a ⟹ (α ::: P.M α)} (hd : M.dest P t = ⟨a, hf⟩) :
    M.dest P (M.csup P c) =
      ⟨a, splitFun (dropFun hf) (fun o => M.csup P (M.subchain P c a o))⟩ := by
  have hex : ∃ t, c t ∧ t ≠ M.bot P := ⟨t, ht, hb⟩
  rw [M.dest_csup_of_pos P hex]
  obtain ⟨hct, hcb⟩ := choose_spec hex
  simp only [M.contents]
  rcases hch : M.dest P (choose hex) with ⟨a₀, hf₀⟩
  obtain rfl : a₀ = a := M.chain_shape_eq P hc hct ht hcb hb hch hd
  have hcon : dropFun hf₀ = dropFun hf := (M.chain_content_eq P hc hct ht hcb hb hch hd).1
  dsimp only
  rw [hcon]

/-- Sub-chains of a chain are chains. -/
theorem M.chain_subchain [HasBot P α] {c : P.M α → Prop} (hc : chain c)
    (a : P.A) (o : (P.B a).last) : chain (M.subchain P c a o) := by
  rintro x y ⟨t₁, hf₁, ht₁, hb₁, hd₁, rfl⟩ ⟨t₂, hf₂, ht₂, hb₂, hd₂, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simpa using (M.chain_content_eq P hc ht₁ ht₂ hb₁ hb₂ hd₁ hd₂).2 o

/-- The supremum is an upper bound. -/
theorem M.le_csup [HasBot P α] {c : P.M α → Prop} (hc : chain c)
    {t : P.M α} (ht : c t) : M.le P t (M.csup P c) := by
  apply M.le.coinduct P (fun u v => ∃ d : P.M α → Prop, d u ∧ chain d ∧ v = M.csup P d)
    _ _ _ ⟨c, ht, hc, rfl⟩
  rintro u v ⟨d, hdu, hdc, rfl⟩
  by_cases hb : u = M.bot P
  · exact Or.inl hb
  rcases hu : M.dest P u with ⟨a, hf⟩
  refine Or.inr ⟨a, dropFun hf, lastFun hf, (fun o => M.csup P (M.subchain P d a o)),
    by rw [split_dropFun_lastFun], M.dest_csup P hdc hdu hb hu, fun o => ?_⟩
  exact ⟨M.subchain P d a o, ⟨u, hf, hdu, hb, hu, rfl⟩, M.chain_subchain P hdc a o, rfl⟩

/-- The supremum is the *least* upper bound. -/
theorem M.csup_le [HasBot P α] {c : P.M α → Prop} (hc : chain c)
    {x : P.M α} (hub : ∀ y, c y → M.le P y x) : M.le P (M.csup P c) x := by
  apply M.le.coinduct P
    (fun u v => ∃ d : P.M α → Prop, chain d ∧ u = M.csup P d ∧ ∀ y, d y → M.le P y v)
    _ _ _ ⟨c, hc, rfl, hub⟩
  rintro u v ⟨d, hdc, rfl, hdub⟩
  by_cases hex : ∃ t, d t ∧ t ≠ M.bot P
  · obtain ⟨t, hdt, hb⟩ := hex
    rcases ht : M.dest P t with ⟨a, hf⟩
    rcases hv : M.dest P v with ⟨b, hfv⟩
    obtain rfl : a = b := M.shape_eq_of_le P (hdub t hdt) hb ht hv
    obtain ⟨hcon, hchild⟩ := M.content_children_of_le P (hdub t hdt) hb ht hv
    refine Or.inr ⟨a, dropFun hf, (fun o => M.csup P (M.subchain P d a o)), lastFun hfv,
      M.dest_csup P hdc hdt hb ht, ?_, fun o => ?_⟩
    · rw [hcon, split_dropFun_lastFun]
    · refine ⟨M.subchain P d a o, M.chain_subchain P hdc a o, rfl, ?_⟩
      rintro y ⟨t', hf', hdt', hb', ht', rfl⟩
      exact (M.content_children_of_le P (hdub t' hdt') hb' ht' hv).2 o
  · exact Or.inl (M.csup_eq_bot P hex)

/-- `M.csup` really is the supremum of a chain. -/
theorem M.csup_spec [HasBot P α] {c : P.M α → Prop} (hc : chain c) :
    is_sup c (M.csup P c) := by
  intro x
  refine ⟨fun h y hy => PartialOrder.rel_trans (M.le_csup P hc hy) h, fun h => ?_⟩
  exact M.csup_le P hc h

/-- `P.M α` is a chain-complete partial order, which is what lets Lean's
`partial_fixpoint` target it. -/
instance (priority := default + 100) M.instCCPO
    [HasBot P α] : CCPO (P.M α) where
  has_csup {c} hc := ⟨M.csup P c, M.csup_spec P hc⟩

end MvPFunctor

end QPFTypes
