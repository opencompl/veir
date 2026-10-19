import Veir.Passes.ArithCanonicalize.NestedBitwiseSupport

/-! Pinned `xori(a,xori(x,a)) → x`, both nested operand orders. -/
namespace Veir.ArithCanonicalize.F067

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.NestedBitwiseSupport

def pattern (swapped : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let a ← MatchProg.value ty
      let inner ← MatchProg.operation (.arith .xori)
        (if swapped then #[a, x] else #[x, a]) #[ty]
      let _ ← MatchProg.root (.arith .xori) #[a, inner.res[0]!] #[ty]
      return x)
    pure
    (fun result => result)

theorem valid (swapped : Bool) : Pattern.Valid (pattern swapped) := by
  cases swapped <;> simp only [pattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    simp only [RuntimeValue.Conforms.integerType,
      forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ x a p0 inner hInner p1 result hOuter
    obtain rfl := (xori_iff _ _ _ _).mp hInner
    obtain rfl := (xori_iff _ _ _ _).mp hOuter
  · exact xor_cancel_right w x a
  · exact xor_cancel_right_swapped w x a

end Veir.ArithCanonicalize.F067
