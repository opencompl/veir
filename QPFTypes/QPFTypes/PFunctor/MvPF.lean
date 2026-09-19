import QPFTypes.TypeVec
import QPFTypes.TypeFun
import QPFTypes.PFunctor.Multivariate.Basic

/-!
# Multivariate Semantic Polynomial Functor

-/
namespace QPFTypes
open TypeFun (uncurry)

class MvPF {α} (n : outParam Nat) (F : α) extends TypeFun n α where
  P : MvPFunctor n
  box : ∀ {βs}, (uncurry F) βs → P βs
  unbox : ∀ {βs}, P βs → (uncurry F) βs
  box_unbox : ∀ {βs} (x : P βs), box (unbox x) = x
  unbox_box : ∀ {βs} (x : (uncurry F) βs), unbox (box x) = x


namespace MvPF

/-

With the `TypeFun` trickery, and the below signature of `Fix`,
we can write `Fix Sum` for the original, _curried_ `Sum`.

However, `Fix Sum` itself would still be an uncurried function.

-/

def Fix (F : α) [MvPF (n + 1) F] (αs : TypeVec n) : Type :=
  _
