import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Pinned `RedundantSelectFalse`: `select(c, a, select(c,b,d))`. -/
namespace Veir.ArithCanonicalize.TD027

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let c ← MatchProg.value condTy
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let d ← MatchProg.value ty
      let inner ← MatchProg.operation (.arith .select) #[c, b, d] #[ty]
      let _ ← MatchProg.root (.arith .select) #[c, a, inner.res[0]!] #[ty]
      return (ty, c, a, d))
    (fun (ty, c, a, d) => do
      let props ← CreateProg.property (.arith .select) ()
      CreateProg.operation (.arith .select) #[c, a, d] #[ty] props)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ ⟨cw, s⟩ condTy hType hWidth c hConforms a b d innerProp innerVal hInner rootProp
  cases hType
  obtain ⟨cond, rfl⟩ := RuntimeValue.Conforms.integerType.mp hConforms
  cases condTy with
  | mk n sign =>
    dsimp at hWidth
    subst n
    obtain rfl := (select_iff _ _ _ _ _).mp hInner
    intro result hResult
    obtain rfl := (select_iff _ _ _ _ _).mp hResult
    refine ⟨.int w (LLVM.Int.select cond a d), ?_, ?_⟩
    · exact (select_iff _ _ _ _ _).mpr rfl
    · exact select_nested_false cond a b d

end Veir.ArithCanonicalize.TD027
