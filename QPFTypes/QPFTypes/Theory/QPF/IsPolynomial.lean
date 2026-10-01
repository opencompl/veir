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

universe u
variable {n : Nat}



/--
`IsPolynomial F` holds when `F` is isomorphic to a polynomial functor.
Which is to say, when `F` is a QPF with a trivial quotient,
meaning that `QPF.repr` and `QPF.abs` are isomorphisms.

Note that this notion of being "polynomial" is syntactically wider than
`PFunctor`, since `PFunctors` have to be defined in a particular shape.
The literature occasionally cals this notion "semantic polynomial functors".
-/
class IsPolynomial (F : TypeVec.{u} n → Type u) [q : QPF F] where
  repr_abs : ∀ {β : TypeVec (n)} (p : P F β), repr (abs p) = p

attribute [simp, grind =] IsPolynomial.repr_abs

/-! ## ofEquiv -/

/-- Any typefunction isomorphic to a polynomial QPF is itself polynomial. -/
theorem IsPolynomial.ofEquiv {F F' : TypeVec.{u} n → Type u} [QPF F'] [IsPolynomial F'] [MvFunctor F]
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

private theorem IsPolynomial.cast {F F' : TypeVec.{u} n → Type u} [q : QPF F] [IsPolynomial F]
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
