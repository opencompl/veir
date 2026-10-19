import Veir.Passes.ArithCanonicalize.NestedBitwiseSupport

/-! Pinned nested andi absorption, all four operand orderings. -/
namespace Veir.ArithCanonicalize.F056

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.NestedBitwiseSupport

def pattern (innerSwap outerSwap : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let inner ← MatchProg.operation (.arith .andi)
        (if innerSwap then #[y, x] else #[x, y]) #[ty]
      let _ ← MatchProg.root (.arith .andi)
        (if outerSwap then #[inner.res[0]!, x] else #[x, inner.res[0]!]) #[ty]
      return inner.res[0]!)
    pure
    (fun result => result)

theorem valid (innerSwap outerSwap : Bool) :
    Pattern.Valid (pattern innerSwap outerSwap) := by
  cases innerSwap <;> cases outerSwap <;>
    simp only [pattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    simp only [RuntimeValue.Conforms.integerType,
      forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ x y p0 inner hInner p1 result hOuter
    obtain rfl := (andi_iff _ _ _ _).mp hInner
    obtain rfl := (andi_iff _ _ _ _).mp hOuter
  · exact and_absorb w x y
  · exact and_absorb_outer_swap w x y
  · exact and_absorb_inner_swap w x y
  · exact and_absorb_both_swap w x y

end Veir.ArithCanonicalize.F056
