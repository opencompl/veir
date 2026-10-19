import Veir.Passes.ArithCanonicalize.CastSupport
import Veir.Passes.ArithCanonicalize.ConstSupport

/-! Pinned scalar integer constant fold of `arith.extui`. -/
namespace Veir.ArithCanonicalize.F141

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
  Veir.ArithCanonicalize.CastSupport Veir.ArithCanonicalize

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sourceTy ← MatchProg.type (Attr := IntegerType)
      let resultTy ← MatchProg.type (Attr := IntegerType)
      let c ← MatchProg.operation (.arith .constant) #[] #[sourceTy]
      MatchProg.matchNative (sourceTy, resultTy, c.properties)
        (fun (sourceTy, resultTy, props) =>
          match sourceTy.cast? IntegerType, resultTy.cast? IntegerType with
          | some a, some b =>
              (props.value.type : TypeAttr) == sourceTy && a.bitwidth < b.bitwidth
          | _, _ => false)
      let _ ← MatchProg.root (.arith .extui) #[c.res[0]!] #[resultTy]
      return (sourceTy, resultTy, c.properties))
    (fun (sourceTy, resultTy, c) => do
      let props ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.arith .constant))) (sourceTy, resultTy, c)
        (fun (sourceTy, resultTy, c) => do
          let some a := sourceTy.cast? IntegerType | none
          let some b := resultTy.cast? IntegerType | none
          let bits := (BitVec.ofInt a.bitwidth c.value.value).zeroExtend b.bitwidth
          some { value := IntegerAttr.ofInt bits.toInt b })
      let result ← CreateProg.operation (.arith .constant) #[] #[resultTy] props
      return result.res[0]!)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  rintro ⟨a, sa⟩ ⟨b, sb⟩ c vc hc rootProps result hResult hMatch
  simp only [IsTypeAttr.cast?_of, Bool.and_eq_true, decide_eq_true_eq] at hMatch
  obtain ⟨hType, hab⟩ := hMatch
  obtain rfl := (constant_iff _ _ _).mp hc
  have hty : c.value.type = IntegerType.mk a sa := by grind
  obtain rfl := (extui_iff a b hab rootProps _ result).mp hResult
  simp only [IsTypeAttr.cast?_of]
  let bits := (BitVec.ofInt a c.value.value).zeroExtend b
  let folded := IntegerAttr.ofInt bits.toInt (IntegerType.mk b sb)
  refine ⟨.int b (.val (BitVec.ofInt b folded.value)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    rfl
  · have hb : BitVec.ofInt b folded.value = bits := by
      calc
        BitVec.ofInt b folded.value = BitVec.ofInt b bits.toInt :=
          ofInt_ofInt (IntegerType.mk b sb) bits.toInt
        _ = bits := BitVec.ofInt_toInt
    rw [hb]
    by_cases hv : (BitVec.ofInt a c.value.value).msb = true <;>
      cases rootProps.nneg <;>
      simp [LLVM.Int.zext, bits, hv,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

end Veir.ArithCanonicalize.F141
