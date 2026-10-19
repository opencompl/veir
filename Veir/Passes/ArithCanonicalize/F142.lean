import Veir.Passes.ArithCanonicalize.CastSupport

/-! Pinned fold bypassing an inner sign extension. -/
namespace Veir.ArithCanonicalize.F142

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
      let inner ← MatchProg.operation (.arith .extsi) #[x] #[middleTy]
      let _ ← MatchProg.root (.arith .extsi) #[inner.res[0]!] #[resultTy]
      return (sourceTy, resultTy, x))
    (fun (_sourceTy, resultTy, x) => do
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
  obtain rfl := (extsi_iff a b hab x innerVal).mp hInner
  obtain rfl := (extsi_iff b c hbc (LLVM.Int.sext x b hab) result).mp hResult
  have hac : a < c := Nat.lt_trans hab hbc
  refine ⟨.int c (LLVM.Int.sext x c hac), ?_, ?_⟩
  · exact (extsi_iff a c hac x _).mpr rfl
  · exact extsi_nested x hab hbc

end Veir.ArithCanonicalize.F142
