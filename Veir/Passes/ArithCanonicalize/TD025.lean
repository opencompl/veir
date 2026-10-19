import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Pinned `SelectNotCond`: selecting on an i1 bitwise complement swaps arms. -/
namespace Veir.ArithCanonicalize.TD025

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let c ← MatchProg.value condTy
      let one ← matchConstant condTy 1
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let complement ← MatchProg.operation (.arith .xori) #[c, one] #[condTy]
      let _ ← MatchProg.root (.arith .select) #[complement.res[0]!, x, y] #[ty]
      return (ty, condTy, c, x, y))
    (fun (ty, _condTy, c, x, y) =>
      do
        let props ← CreateProg.property (.arith .select) ()
        CreateProg.operation (.arith .select) #[c, y, x] #[ty] props)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ ⟨cw, s⟩ condTy hType hWidth c hConforms oneProp oneVal hOne hOneInterp x y xorProp xorVal hXor rootProp
  cases hType
  obtain ⟨cond, rfl⟩ := RuntimeValue.Conforms.integerType.mp hConforms
  cases condTy with
  | mk n sign =>
    dsimp at hWidth
    subst n
    obtain rfl := (constant_iff _ _ _).mp hOneInterp
    obtain rfl := (xori_iff _ _ _ _).mp hXor
    intro result hResult
    obtain rfl := (select_iff _ _ _ _ _).mp hResult
    refine ⟨.int w (LLVM.Int.select cond y x), ?_, ?_⟩
    · exact (select_iff _ _ _ _ _).mpr rfl
    · simpa [hOne] using select_not_swap cond x y

end Veir.ArithCanonicalize.TD025
