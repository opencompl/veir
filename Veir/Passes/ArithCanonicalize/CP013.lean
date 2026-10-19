import Veir.Passes.ArithCanonicalize.CPSelectSupport
import Veir.Passes.ArithCanonicalize.ConstSupport

/-! Pinned C++ `SelectToExtUI2`: `select(c, 0, 1) -> extui(xori(c, 1))`. -/
namespace Veir.ArithCanonicalize.CP013

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
  Veir.ArithCanonicalize.CastSupport Veir.ArithCanonicalize.SelectSupport
  Veir.ArithCanonicalize.CPSelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let resultTy ← MatchProg.type (Attr := IntegerType) (fun t => 1 < t.bitwidth)
      let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let c ← MatchProg.value condTy
      let zero ← matchConstant resultTy 0
      let one ← matchConstant resultTy 1
      let _ ← MatchProg.root (.arith .select) #[c, zero, one] #[resultTy]
      return (resultTy, condTy, c))
    (fun (resultTy, condTy, c) => do
      let one ← createConstant condTy 1
      let xorProps ← CreateProg.property (.arith .xori) ()
      let inv ← CreateProg.operation (.arith .xori) #[c, one] #[condTy] xorProps
      let extProps ← CreateProg.property (.arith .extui) { nneg := false }
      CreateProg.operation (.arith .extui) #[inv.res[0]!] #[resultTy] extProps)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  unfold pattern matchConstant createConstant
  provePuddleValid
  rintro resultTy ⟨w, s⟩ rfl hw condTy ⟨cw, cs⟩ rfl hcw
    c hc zeroProp zeroVal hZero hZeroInterp oneProp oneVal hOne hOneInterp
    rootProps result hResult
  dsimp at hw hcw
  subst cw
  obtain ⟨cond, rfl⟩ := RuntimeValue.Conforms.integerType.mp hc
  obtain rfl := (constant_iff _ _ _).mp hZeroInterp
  obtain rfl := (constant_iff _ _ _).mp hOneInterp
  obtain rfl := (select_iff _ _ _ _ _).mp hResult
  have hcast : (TypeAttr.of IntegerType (IntegerType.mk 1 cs)).cast? IntegerType =
      some (IntegerType.mk 1 cs) := by rfl
  simp only [hcast]
  let createdOne := BitVec.ofInt 1 (IntegerAttr.ofInt 1 (IntegerType.mk 1 cs)).value
  refine ⟨.int 1 (.val createdOne), ?_,
    .int 1 (LLVM.Int.xor cond (.val createdOne)), ?_,
    .int w (LLVM.Int.zext (LLVM.Int.xor cond (.val createdOne)) w false hw), ?_, ?_⟩
  · exact (constant_iff _ _ _).mpr rfl
  · exact (xori_iff _ _ _ _).mpr rfl
  · exact (extui_iff 1 w hw { nneg := false } _ _).mpr rfl
  · have hv : createdOne = 1#1 := by
      simpa [createdOne] using ofInt_ofInt (IntegerType.mk 1 cs) 1
    simpa [hZero, hOne, hv] using select_zero_one_extui_not cond hw

end Veir.ArithCanonicalize.CP013
