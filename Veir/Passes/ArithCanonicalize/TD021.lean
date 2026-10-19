import Veir.Passes.ArithCanonicalize.BitwiseExtensionSupport

/-! Pinned `xori(extui(x), extui(y)) -> extui(xori(x,y))`. -/
namespace Veir.ArithCanonicalize.TD021

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
  Veir.ArithCanonicalize.CastSupport
  Veir.ArithCanonicalize.BitwiseExtensionSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sourceTy ← MatchProg.type (Attr := IntegerType)
      let resultTy ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.matchNative (sourceTy, resultTy)
        (fun (sourceTy, resultTy) =>
          match sourceTy.cast? IntegerType, resultTy.cast? IntegerType with
          | some a, some b => a.bitwidth < b.bitwidth
          | _, _ => false)
      let x ← MatchProg.value sourceTy
      let y ← MatchProg.value sourceTy
      let extX ← MatchProg.operation (.arith .extui) #[x] #[resultTy]
      let extY ← MatchProg.operation (.arith .extui) #[y] #[resultTy]
      let _ ← MatchProg.root (.arith .xori)
        #[extX.res[0]!, extY.res[0]!] #[resultTy]
      return (sourceTy, resultTy, x, y, extX.properties, extY.properties))
    (fun (sourceTy, resultTy, x, y, px, py) => do
      let xorProps ← CreateProg.property (.arith .xori) ()
      let smallXor ← CreateProg.operation (.arith .xori) #[x, y] #[sourceTy] xorProps
      let extProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.arith .extui))) (px, py)
        (fun (px, py) => some { nneg := px.nneg && py.nneg })
      CreateProg.operation (.arith .extui) #[smallXor.res[0]!] #[resultTy] extProps)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨a, sa⟩ ⟨b, sb⟩ x y pX vX hX pY vY hY rootProps result hResult hWidths
  simp only [IsTypeAttr.cast?_of, decide_eq_true_eq] at hWidths
  obtain rfl := (extui_iff a b hWidths pX x vX).mp hX
  obtain rfl := (extui_iff a b hWidths pY y vY).mp hY
  obtain rfl := (xori_iff b _ _ _).mp hResult
  refine ⟨.int a (LLVM.Int.xor x y), ?_, .int b (LLVM.Int.zext (LLVM.Int.xor x y) b (pX.nneg && pY.nneg) hWidths), ?_, ?_⟩
  · exact (xori_iff a x y _).mpr rfl
  · exact (extui_iff a b hWidths { nneg := pX.nneg && pY.nneg } (LLVM.Int.xor x y) _).mpr rfl
  · exact zext_xor x y hWidths pX.nneg pY.nneg

end Veir.ArithCanonicalize.TD021
