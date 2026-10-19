import Veir.Passes.ArithCanonicalize.CPSelectSupport

/-! Pinned C++ `SelectToExtUI1`: `select(c, 1, 0) -> extui(c)`. -/
namespace Veir.ArithCanonicalize.CP012

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
  Veir.ArithCanonicalize.CastSupport Veir.ArithCanonicalize.SelectSupport
  Veir.ArithCanonicalize.CPSelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let resultTy ← MatchProg.type (Attr := IntegerType) (fun t => 1 < t.bitwidth)
      let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let c ← MatchProg.value condTy
      let one ← matchConstant resultTy 1
      let zero ← matchConstant resultTy 0
      let _ ← MatchProg.root (.arith .select) #[c, one, zero] #[resultTy]
      return (resultTy, c))
    (fun (resultTy, c) => do
      let props ← CreateProg.property (.arith .extui) { nneg := false }
      CreateProg.operation (.arith .extui) #[c] #[resultTy] props)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  rintro resultTy ⟨w, s⟩ rfl hw condTy ⟨cw, cs⟩ rfl hcw
    c hc oneProp oneVal hOne hOneInterp zeroProp zeroVal hZero hZeroInterp
    rootProps result hResult
  dsimp at hw hcw
  subst cw
  obtain ⟨cond, rfl⟩ := RuntimeValue.Conforms.integerType.mp hc
  obtain rfl := (constant_iff _ _ _).mp hOneInterp
  obtain rfl := (constant_iff _ _ _).mp hZeroInterp
  obtain rfl := (select_iff _ _ _ _ _).mp hResult
  refine ⟨.int w (LLVM.Int.zext cond w false hw), ?_, ?_⟩
  · exact (extui_iff 1 w hw { nneg := false } cond _).mpr rfl
  · simpa [hOne, hZero] using select_one_zero_extui cond hw

end Veir.ArithCanonicalize.CP012
