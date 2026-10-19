import Veir.Passes.ArithCanonicalize.CastSupport

/-! Pinned fold bypassing an inner zero extension. -/
namespace Veir.ArithCanonicalize.F140

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.CastSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sourceTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let resultTy ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.matchNative (sourceTy, middleTy, resultTy)
        (fun (sourceTy, middleTy, resultTy) =>
          match sourceTy.cast? IntegerType, middleTy.cast? IntegerType,
              resultTy.cast? IntegerType with
          | some a, some b, some c =>
              a.bitwidth < b.bitwidth && b.bitwidth < c.bitwidth
          | _, _, _ => false)
      let x ← MatchProg.value sourceTy
      let inner ← MatchProg.operation (.arith .extui) #[x] #[middleTy]
      let _ ← MatchProg.root (.arith .extui) #[inner.res[0]!] #[resultTy]
      return (sourceTy, resultTy, x, inner.properties))
    (fun (_sourceTy, resultTy, x, innerProps) =>
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
  obtain rfl := (extui_iff a b hab innerProp x innerVal).mp hInner
  obtain rfl := (extui_iff b c hbc rootProp
    (LLVM.Int.zext x b innerProp.nneg hab) result).mp hResult
  have hac : a < c := Nat.lt_trans hab hbc
  refine ⟨.int c (LLVM.Int.zext x c innerProp.nneg hac), ?_, ?_⟩
  · exact (extui_iff a c hac innerProp x _).mpr rfl
  · exact extui_nested x hab hbc innerProp.nneg rootProp.nneg

end Veir.ArithCanonicalize.F140
