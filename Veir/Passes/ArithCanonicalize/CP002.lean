import Veir.Passes.ArithCanonicalize.NarrowExtremumSupport

/-! Pinned C++ `NarrowExtremum<TruncI, extsi, minsi>`. -/
namespace Veir.ArithCanonicalize.CP002

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
      let extX ← MatchProg.operation (.arith .extsi) #[x] #[wideTy]
      let extY ← MatchProg.operation (.arith .extsi) #[y] #[wideTy]
      let wideMax ← MatchProg.operation (.arith .minsi)
        #[extX.res[0]!, extY.res[0]!] #[wideTy]
      let () ← MatchProg.inspectOperation (Outputs := Unit) wideMax.op (fun ctx op => do
        let some use := (op.getResult 0).getFirstUse! ctx | none
        guard ((use.getNextUse! ctx).isNone)
        some ())
      let _ ← MatchProg.root (.arith .trunci) #[wideMax.res[0]!] #[narrowTy]
      return (narrowTy, x, y))
    (fun (narrowTy, x, y) => do
      let props ← CreateProg.property (.arith .minsi) ()
      CreateProg.operation (.arith .minsi) #[x, y] #[narrowTy] props)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨a, sa⟩ ⟨b, sb⟩ x y pX vX hX pY vY hY
    maxProps maxVal hMax rootProps result hResult hWidths
  simp only [IsTypeAttr.cast?_of, decide_eq_true_eq] at hWidths
  obtain rfl := (extsi_iff a b hWidths x vX).mp hX
  obtain rfl := (extsi_iff a b hWidths y vY).mp hY
  obtain rfl := (minsi_iff b _ _ _).mp hMax
  obtain rfl := (trunci_iff a b hWidths rootProps _ result).mp hResult
  intro _
  refine ⟨.int a (LLVM.Int.smin x y), ?_, ?_⟩
  · exact (minsi_iff a x y _).mpr rfl
  · rw [sext_smin x y hWidths]
    exact trunci_extsi_cancel (LLVM.Int.smin x y) hWidths
      rootProps.attr.nsw rootProps.attr.nuw

end Veir.ArithCanonicalize.CP002
