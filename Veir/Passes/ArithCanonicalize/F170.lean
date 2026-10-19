import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Upstream `select(false, x, y) -> y`. -/
namespace Veir.ArithCanonicalize.F170

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let c ← matchConstant condTy 0
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .select) #[c, x, y] #[ty]
      return y)
    pure
    (fun y => y)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ ⟨cw, s⟩ condTy hType hWidth cProps cVal hCst hInterpConst x y rootProps result hResult
  cases hType
  cases condTy with
  | mk n sign =>
    dsimp at hWidth
    subst n
    obtain rfl := (constant_iff _ _ _).mp hInterpConst
    obtain rfl := (select_iff _ _ _ _ _).mp hResult
    simpa [hCst] using false_arm x y

end Veir.ArithCanonicalize.F170
