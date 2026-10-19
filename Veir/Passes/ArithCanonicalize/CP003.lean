import Veir.Passes.ArithCanonicalize.NarrowExtremumSupport

/-! Pinned C++ `NarrowExtremum<TruncI, extui, maxui>`. -/
namespace Veir.ArithCanonicalize.CP003

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.CastSupport
  Veir.ArithCanonicalize.NarrowExtremumSupport
  Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let narrowTy ← MatchProg.type (Attr := IntegerType)
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.matchNative (narrowTy, wideTy)
        (fun (narrowTy, wideTy) =>
          match narrowTy.cast? IntegerType, wideTy.cast? IntegerType with
          | some a, some b => a.bitwidth < b.bitwidth
          | _, _ => false)
      let x ← MatchProg.value narrowTy
      let y ← MatchProg.value narrowTy
      let extX ← MatchProg.operation (.arith .extui) #[x] #[wideTy]
      let extY ← MatchProg.operation (.arith .extui) #[y] #[wideTy]
      let wideMax ← MatchProg.operation (.arith .maxui)
        #[extX.res[0]!, extY.res[0]!] #[wideTy]
      let () ← MatchProg.inspectOperation (Outputs := Unit) wideMax.op (fun ctx op => do
        let some use := (op.getResult 0).getFirstUse! ctx | none
        guard ((use.getNextUse! ctx).isNone)
        some ())
      let _ ← MatchProg.root (.arith .trunci) #[wideMax.res[0]!] #[narrowTy]
      return (narrowTy, x, y))
    (fun (narrowTy, x, y) => do
      let props ← CreateProg.property (.arith .maxui) ()
      CreateProg.operation (.arith .maxui) #[x, y] #[narrowTy] props)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨a, sa⟩ ⟨b, sb⟩ x y pX vX hX pY vY hY
    maxProps maxVal hMax rootProps result hResult hWidths
  simp only [IsTypeAttr.cast?_of, decide_eq_true_eq] at hWidths
  obtain rfl := (extui_iff a b hWidths pX x vX).mp hX
  obtain rfl := (extui_iff a b hWidths pY y vY).mp hY
  obtain rfl := (maxui_iff b _ _ _).mp hMax
  obtain rfl := (trunci_iff a b hWidths rootProps _ result).mp hResult
  intro _
  refine ⟨.int a (LLVM.Int.umax x y), ?_, ?_⟩
  · exact (maxui_iff a x y _).mpr rfl
  · exact narrow_umax x y hWidths pX.nneg pY.nneg
      rootProps.attr.nsw rootProps.attr.nuw

end Veir.ArithCanonicalize.CP003
