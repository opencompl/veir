import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Upstream `select(cond, x, x) -> x`, including poison conditions. -/
namespace Veir.ArithCanonicalize.F168

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let c ← MatchProg.value condTy
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .select) #[c, x, x] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ ⟨cw, s⟩ hWidth hType hCond cond hConforms x props
  cases hType
  obtain ⟨c, rfl⟩ := RuntimeValue.Conforms.integerType.mp hConforms
  cases hWidth with
  | mk n sign =>
    dsimp at hCond
    subst n
    intro result hinterp
    obtain rfl := (select_iff _ _ _ _ _).mp hinterp
    exact same_arms c x

end Veir.ArithCanonicalize.F168
