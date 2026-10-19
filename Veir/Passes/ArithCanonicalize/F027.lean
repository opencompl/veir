import Veir.Passes.ArithCanonicalize.F027Support

/-! Upstream `(a*b)/b -> a` for `arith.divui` when the multiply is `nuw`. -/
namespace Veir.ArithCanonicalize.F027

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
  Veir.ArithCanonicalize.F027Support

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let product ← MatchProg.operation (.arith .muli) #[x, y] #[ty]
        (fun p => p.attr.nuw)
      let _ ← MatchProg.root (.arith .divui) #[product.res[0]!, y] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x y mulProp product hFlag hMul divProp result hDiv
  obtain rfl := (muli_iff _ _ _ _ _).mp hMul
  obtain ⟨_, rfl⟩ := (divui_iff _ _ _ _ _).mp hDiv
  simpa [hFlag] using div_mul_nuw x y mulProp.attr.nsw divProp.exact

def pattern_swapped : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let product ← MatchProg.operation (.arith .muli) #[y, x] #[ty]
        (fun p => p.attr.nuw)
      let _ ← MatchProg.root (.arith .divui) #[product.res[0]!, y] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid_swapped : Pattern.Valid pattern_swapped := by
  simp only [pattern_swapped]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x y mulProp product hFlag hMul divProp result hDiv
  obtain rfl := (muli_iff _ _ _ _ _).mp hMul
  obtain ⟨_, rfl⟩ := (divui_iff _ _ _ _ _).mp hDiv
  simpa [hFlag, mul_comm] using div_mul_nuw x y mulProp.attr.nsw divProp.exact

end Veir.ArithCanonicalize.F027
