import Veir.Passes.ArithCanonicalize.CastNarrowSupport

/-! `trunci(extsi(x)) -> trunci(x)` when the destination is narrower than x. -/
namespace Veir.ArithCanonicalize.F147b

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.CastSupport
  Veir.ArithCanonicalize.CastNarrowSupport

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
              b.bitwidth < a.bitwidth && a.bitwidth < c.bitwidth
          | _, _, _ => false)
      let x ← MatchProg.value sourceTy
      let inner ← MatchProg.operation (.arith .extsi) #[x] #[extTy]
      let root ← MatchProg.root (.arith .trunci) #[inner.res[0]!] #[resultTy]
      return (resultTy, x, root.properties))
    (fun (resultTy, x, overflow) =>
      CreateProg.operation (.arith .trunci) #[x] #[resultTy] overflow)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨a, sa⟩ ⟨b, sb⟩ ⟨c, sc⟩ x innerProp innerVal hInner rootProp result hResult hWidths
  simp only [IsTypeAttr.cast?_of, Bool.and_eq_true, decide_eq_true_eq] at hWidths
  obtain ⟨hba, hac⟩ := hWidths
  obtain rfl := (extsi_iff a c hac x innerVal).mp hInner
  obtain rfl := (trunci_iff b c (by omega) rootProp
    (LLVM.Int.sext x c hac) result).mp hResult
  refine ⟨.int b (LLVM.Int.trunc x b rootProp.attr.nsw rootProp.attr.nuw (by omega)), ?_, ?_⟩
  · exact (trunci_iff b a hba rootProp x _).mpr rfl
  · exact trunci_extsi_narrow x hba hac rootProp.attr.nsw rootProp.attr.nuw

end Veir.ArithCanonicalize.F147b
