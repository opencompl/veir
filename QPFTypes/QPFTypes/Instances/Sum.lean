module

public import QPFTypes.Theory.PFunctor.Multivariate.Basic
public import QPFTypes.Theory.QPF.Basic
public import QPFTypes.Theory.QPF.IsPolynomial

/-!
# QPF instances for `Sum`

This file adds `QPF` and `IsPolynomial` instances to the existing, upstream,
binary sum type `Sum` (i.e., `α ⊕ β`), as the binary type function
`TypeFun.ofCurried Sum`.
-/

@[expose] public section

universe u

namespace QPFTypes.Sum
open MvFunctor TypeVec

/-! ## Binary Sums -/

instance instMvFunctor : MvFunctor (TypeFun.ofCurried (n := 2) Sum.{u, u}) where
  map f
    | .inl a => .inl (f 1 a)
    | .inr b => .inr (f 0 b)

/-- The polynomial functor underlying `Sum`: an `inl` has a single child at index `1`
(the left type), an `inr` has a single child at index `0` (the right type). -/
def P : MvPFunctor.{u} 2 where
  A := ULift.{u} Bool
  B
    | ⟨true⟩ => #t[PUnit, PEmpty]
    | ⟨false⟩ => #t[PEmpty, PUnit]

instance instQPF : QPF (TypeFun.ofCurried (n := 2) Sum.{u, u}) where
  P := P
  abs
    | ⟨⟨true⟩, f⟩ => .inl (f 1 ⟨⟩)
    | ⟨⟨false⟩, f⟩ => .inr (f 0 ⟨⟩)
  repr
    | .inl a => ⟨⟨true⟩, splitFun (splitFun nilFun fun _ => a) PEmpty.elim⟩
    | .inr b => ⟨⟨false⟩, splitFun (splitFun nilFun PEmpty.elim) fun _ => b⟩
  abs_repr := by rintro α (_ | _) <;> rfl
  abs_map := by rintro α β f ⟨⟨_ | _⟩, g⟩ <;> rfl

instance instIsPolynomial : QPF.IsPolynomial (TypeFun.ofCurried (n := 2) Sum.{u, u}) where
  repr_abs := by
    rintro β ⟨⟨_ | _⟩, f⟩ <;> refine congrArg _ (funext fun i => funext fun x => ?_) <;>
      match i with
      | 0 | 1 => cases x <;> rfl

end QPFTypes.Sum
