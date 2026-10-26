module

public import QPFTypes.Theory.QPF.Basic

/-!
# IsPolynomial Typeclass

This file defines an `IsPolynomial` typeclass to identify QPFs which are, in
particular, just (isomorphic to) polynomial functors.
-/
@[expose] public section

namespace QPFTypes.QPF
open MvFunctor

universe u v v'
variable {n : Nat}



/--
`IsPolynomial F` holds when `F` is isomorphic to a polynomial functor.
Which is to say, when `F` is a QPF with a trivial quotient,
meaning that `QPF.repr` and `QPF.abs` are isomorphisms.

Note that this notion of being "polynomial" is syntactically wider than
`PFunctor`, since `PFunctors` have to be defined in a particular shape.
The literature occasionally calls this notion "semantic polynomial functors".
-/
class IsPolynomial (F : TypeVec.{u} n → Type v) [q : QPF F] where
  repr_abs : ∀ {β : TypeVec (n)} (p : P F β), repr (abs p) = p

attribute [simp, grind =] IsPolynomial.repr_abs

/-- For polynomial functors, `LiftP (PredLast α p) x` holds iff `p` holds for each value that
`QPF.repr x` contains in the last position. -/
theorem IsPolynomial.liftPLast_iff {F : TypeVec.{u} (n + 1) → Type v} [QPF F]
    [IsPolynomial F] {α : TypeVec n} {β : Type u} (p : β → Prop) (x : F (α ::: β)) :
    LiftPLast p x ↔ ∀ j, p ((repr x).2 0 j) := by
  rw [LiftPLast, liftP_iff]
  constructor
  · rintro ⟨a, f, hx, hf⟩
    have hr : repr x = ⟨a, f⟩ := by rw [hx]; exact IsPolynomial.repr_abs _
    rw [hr]
    exact hf 0
  · refine fun h => ⟨_, _, (abs_repr x).symm, fun i => ?_⟩
    cases i using Fin.cases
    · exact h
    · exact fun _ => trivial

/-- For polynomial functors, `QPF.repr` commutes with `map`. -/
theorem IsPolynomial.repr_map {F : TypeVec.{u} n → Type v} [QPF F] [IsPolynomial F]
    {β γ : TypeVec n} (g : β ⟹ γ) (y : F β) :
    repr (g <$$> y) = g <$$> repr y := by
  conv => lhs; rw [← abs_repr y, ← abs_map, IsPolynomial.repr_abs]

/-! ## Attaching proofs to the last position -/

section Attach
open TypeVec
variable {F : TypeVec.{u} (n + 1) → Type v} [QPF F] [IsPolynomial F]
  {α : TypeVec.{u} n} {β : Type u} {p : β → Prop}

/-- Pairs every value in the last position of `x` with a proof of `p`, given that `p` holds on
every value in that position, i.e., `LiftP (α.PredLast p) x`. -/
def attach (x : F (α ::: β)) (h : LiftP (α.PredLast p) x) : F (α ::: Subtype p) :=
  abs ⟨(repr x).1, splitFun (dropFun (repr x).2 : _ ⟹ α)
    fun j => ⟨lastFun (repr x).2 j, (IsPolynomial.liftPLast_iff p x).1 h j⟩⟩

/-- Forgetting the proofs attached by `attach` gives back `x`. -/
@[simp, grind =]
theorem val_attach (x : F (α ::: β)) (h : LiftP (α.PredLast p) x) :
    (TypeVec.id ::: Subtype.val) <$$> attach x h = x := by
  rw [attach]; erw [← abs_map]
  conv => rhs; rw [← abs_repr x]
  congr 1
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i j
  rcases i with _ | i <;> rfl

end Attach

/-! ## ofEquiv -/

/-- Any typefunction isomorphic to a polynomial QPF is itself polynomial. -/
theorem IsPolynomial.ofEquiv {F : TypeVec.{u} n → Type v} {F' : TypeVec.{u} n → Type v'}
    [QPF F'] [IsPolynomial F'] [MvFunctor F]
    (toF : ∀ {α}, F α → F' α)
    (invF : ∀ {α}, F' α → F α)
    (left_inv : ∀ {α} (x : F α), invF (toF x) = x)
    (right_inv : ∀ {α} (x : F' α), toF (invF x) = x)
    (map_eq : ∀ {α β} (f : α ⟹ β) (a : F α), f <$$> a = invF (f <$$> toF a) := by intros; rfl) :
    IsPolynomial F (q := .ofEquiv toF invF left_inv right_inv map_eq) :=
  letI : QPF F := QPF.ofEquiv toF invF left_inv right_inv map_eq
  { repr_abs := fun p => by
      show repr (toF (invF (abs p))) = p
      rw [right_inv, IsPolynomial.repr_abs] }

/-! ## ofCurriedCurry -/

private theorem IsPolynomial.cast {F F' : TypeVec.{u} n → Type v} [q : QPF F] [IsPolynomial F]
    (h : F = F') (hq : QPF F = QPF F') : @IsPolynomial n F' (_root_.cast hq q) := by
  subst h; assumption

/--
Round-tripping a type function through `TypeFun.curry`/`TypeFun.ofCurried`
preserves polynomiality, for the `QPF` instance `QPF.instOfCurriedCurry`.
-/
instance IsPolynomial.instOfCurriedCurry {n : Nat} {F : TypeFun.{u, u} n} [QPF F]
    [IsPolynomial F] :
    @IsPolynomial n (TypeFun.ofCurried (TypeFun.curry F)) QPF.instOfCurriedCurry :=
  IsPolynomial.cast (TypeFun.ofCurried_curry F).symm (by simp)

end QPF

/-- Every multivariate PFunctor is indeed polynomial. -/
instance MvPFunctor.instIsPolynomial (P : MvPFunctor.{u} n) : QPF.IsPolynomial P.Obj where
  repr_abs _ := rfl

end QPFTypes
