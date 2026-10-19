import Veir.Passes.ArithCanonicalize.CastIntermediateSupport

/-! Pinned `trunci(extui(x)) -> extui(x)` when result remains wider than x. -/
namespace Veir.ArithCanonicalize.TD056

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.CastSupport
  Veir.ArithCanonicalize.CastIntermediateSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sourceTy ← MatchProg.type (Attr := IntegerType)
      let resultTy ← MatchProg.type (Attr := IntegerType)
      let extTy ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.matchNative (sourceTy, resultTy, extTy)
        (fun (sourceTy, resultTy, extTy) =>
          match sourceTy.cast? IntegerType, resultTy.cast? IntegerType,
              extTy.cast? IntegerType with
          | some a, some b, some c =>
              a.bitwidth < b.bitwidth && b.bitwidth < c.bitwidth
          | _, _, _ => false)
      let x ← MatchProg.value sourceTy
      let inner ← MatchProg.operation (.arith .extui) #[x] #[extTy]
      let _ ← MatchProg.root (.arith .trunci) #[inner.res[0]!] #[resultTy]
      return (resultTy, x, inner.properties))
    (fun (resultTy, x, innerProps) =>
      CreateProg.operation (.arith .extui) #[x] #[resultTy] innerProps)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨a, sa⟩ ⟨b, sb⟩ ⟨c, sc⟩ x innerProp innerVal hInner rootProp result hResult hWidths
  simp only [IsTypeAttr.cast?_of, Bool.and_eq_true, decide_eq_true_eq] at hWidths
  obtain ⟨hab, hbc⟩ := hWidths
  have hac : a < c := Nat.lt_trans hab hbc
  obtain rfl := (extui_iff a c hac innerProp x innerVal).mp hInner
  obtain rfl := (trunci_iff b c hbc rootProp
    (LLVM.Int.zext x c innerProp.nneg hac) result).mp hResult
  refine ⟨.int b (LLVM.Int.zext x b innerProp.nneg hab), ?_, ?_⟩
  · exact (extui_iff a b hab innerProp x _).mpr rfl
  · exact trunci_extui_middle x hab hbc innerProp.nneg rootProp.attr.nsw rootProp.attr.nuw

end Veir.ArithCanonicalize.TD056
