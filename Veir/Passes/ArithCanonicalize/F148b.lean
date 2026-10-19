import Veir.Passes.ArithCanonicalize.CastSupport

/-! Pinned fold `trunci(extsi(x)) -> x` when trunc result is source type. -/
namespace Veir.ArithCanonicalize.F148b

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.CastSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sourceTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.matchNative (sourceTy, middleTy)
        (fun (sourceTy, middleTy) =>
          match sourceTy.cast? IntegerType, middleTy.cast? IntegerType with
          | some a, some b => a.bitwidth < b.bitwidth
          | _, _ => false)
      let x ← MatchProg.value sourceTy
      let inner ← MatchProg.operation (.arith .extsi) #[x] #[middleTy]
      let _ ← MatchProg.root (.arith .trunci) #[inner.res[0]!] #[sourceTy]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨a, sa⟩ ⟨b, sb⟩ x innerProp innerVal hInner rootProp result hResult hWidths
  simp only [IsTypeAttr.cast?_of, decide_eq_true_eq] at hWidths
  have hab : a < b := hWidths
  obtain rfl := (extsi_iff a b hab x innerVal).mp hInner
  obtain rfl := (trunci_iff a b hab rootProp
    (LLVM.Int.sext x b hab) result).mp hResult
  exact trunci_extsi_cancel x hab rootProp.attr.nsw rootProp.attr.nuw

end Veir.ArithCanonicalize.F148b
