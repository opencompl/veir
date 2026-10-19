import Veir.Passes.ArithCanonicalize.CastIntermediateSupport

/-! Pinned `trunci(extsi(x)) -> extsi(x)` when result remains wider than x. -/
namespace Veir.ArithCanonicalize.TD055

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
      let inner ← MatchProg.operation (.arith .extsi) #[x] #[extTy]
      let _ ← MatchProg.root (.arith .trunci) #[inner.res[0]!] #[resultTy]
      return (resultTy, x))
    (fun (resultTy, x) => do
      let props ← CreateProg.property (.arith .extsi) ()
      CreateProg.operation (.arith .extsi) #[x] #[resultTy] props)
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
  obtain rfl := (extsi_iff a c hac x innerVal).mp hInner
  obtain rfl := (trunci_iff b c hbc rootProp
    (LLVM.Int.sext x c hac) result).mp hResult
  refine ⟨.int b (LLVM.Int.sext x b hab), ?_, ?_⟩
  · exact (extsi_iff a b hab x _).mpr rfl
  · exact trunci_extsi_middle x hab hbc rootProp.attr.nsw rootProp.attr.nuw

end Veir.ArithCanonicalize.TD055
