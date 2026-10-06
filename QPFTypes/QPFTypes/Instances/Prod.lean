module

public import QPFTypes.Theory.PFunctor.Multivariate.Basic
public import QPFTypes.Theory.QPF.Basic
public import QPFTypes.Theory.QPF.IsPolynomial

/-!
# QPF instances for `Prod`

This file adds `QPF` and `IsPolynomial` instances to the existing, upstream,
binary product type `Prod` (i.e., `α × β`), as the binary type function
`TypeFun.ofCurried Prod`.
-/

@[expose] public section

universe u

namespace QPFTypes.Prod
open MvFunctor

/-! ## Binary Products -/

instance instMvFunctor : MvFunctor (TypeFun.ofCurried (n := 2) Prod.{u, u}) where
  map := fun f (a, b) => (f 1 a, f 0 b)

instance instQPF : QPF (TypeFun.ofCurried (n := 2) Prod.{u, u}) where
  P := { A := PUnit, B _ _ := PUnit.{u + 1} }
  abs := fun ⟨_, f⟩ => (f 1 ⟨⟩, f 0 ⟨⟩)
  repr := fun (a, b) => ⟨⟨⟩, fun | 0, _ => b | 1, _ => a⟩
  abs_repr := by rintro α ⟨a, b⟩; rfl
  abs_map := by rintro α β f ⟨_, g⟩; rfl

instance instIsPolynomial : QPF.IsPolynomial (TypeFun.ofCurried (n := 2) Prod.{u, u}) where
  repr_abs := by
    rintro β ⟨⟨⟩, f⟩
    simp only [QPF.repr, QPF.abs]
    congr 1
    funext i ⟨⟩
    match i with
    | 0 | 1 => rfl

end QPFTypes.Prod
