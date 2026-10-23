module

public import QPFTypes.Theory.PFunctor.Multivariate.Basic
public import QPFTypes.Theory.QPF.Basic
public import QPFTypes.Theory.QPF.IsPolynomial

/-!
# QPF instances for `Option`

This file adds `QPF` and `IsPolynomial` instances to the existing, upstream,
type `Option`, as the unary type function `TypeFun.ofCurried Option`.
-/

@[expose] public section

universe u

namespace QPFTypes.Option
open MvFunctor TypeVec

instance instMvFunctor : MvFunctor (TypeFun.ofCurried (n := 1) Option.{u}) where
  map f
    | none => none
    | some a => some (f 0 a)

/-- The polynomial functor underlying `Option`: `none` has no children, `some` has a single
child. -/
def P : MvPFunctor.{u} 1 where
  A := ULift.{u} Bool
  B
    | ⟨false⟩ => #t[PEmpty]
    | ⟨true⟩ => #t[PUnit]

instance instQPF : QPF (TypeFun.ofCurried (n := 1) Option.{u}) where
  P := P
  abs
    | ⟨⟨false⟩, _⟩ => none
    | ⟨⟨true⟩, f⟩ => some (f 0 ⟨⟩)
  repr
    | none => ⟨⟨false⟩, splitFun nilFun PEmpty.elim⟩
    | some a => ⟨⟨true⟩, splitFun nilFun fun _ => a⟩
  abs_repr := by rintro α (_ | _) <;> rfl
  abs_map := by rintro α β f ⟨⟨_ | _⟩, g⟩ <;> rfl

instance instIsPolynomial : QPF.IsPolynomial (TypeFun.ofCurried (n := 1) Option.{u}) where
  repr_abs := by
    rintro β ⟨⟨_ | _⟩, f⟩ <;> refine congrArg _ (funext fun i => funext fun x => ?_) <;>
      match i with
      | 0 => cases x <;> rfl

end QPFTypes.Option
