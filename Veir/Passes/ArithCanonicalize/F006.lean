import Veir.Passes.ArithCanonicalize.ExtendedSupport
import Veir.Passes.ArithCanonicalize.ConstSupport

/-! Constant folding of both results of `arith.addui_extended`. -/
namespace Veir.ArithCanonicalize.F006

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle Veir.ArithCanonicalize
  Veir.ArithCanonicalize.ExtendedSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let carryTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t = IntegerType.signless 1)
      let c0 ← MatchProg.operation (.arith .constant) #[] #[ty]
      let c1 ← MatchProg.operation (.arith .constant) #[] #[ty]
      MatchProg.matchNative (ty, c0.properties, c1.properties)
        (fun (ty, a, b) => (a.value.type : TypeAttr) == ty &&
          (b.value.type : TypeAttr) == ty)
      let _ ← MatchProg.root (.arith .addui_extended)
        #[c0.res[0]!, c1.res[0]!] #[ty, carryTy]
      return (ty, carryTy, c0.properties, c1.properties))
    (fun (ty, carryTy, c0, c1) => do
      let lowProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.arith .constant))) (ty, c0, c1)
          (fun (ty, c0, c1) => do
            let some intTy := ty.cast? IntegerType | none
            let a := BitVec.ofInt intTy.bitwidth c0.value.value
            let b := BitVec.ofInt intTy.bitwidth c1.value.value
            some { value := IntegerAttr.ofInt (a + b).toInt intTy })
      let highProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.arith .constant))) (ty, c0, c1)
          (fun (ty, c0, c1) => do
            let some intTy := ty.cast? IntegerType | none
            let a := BitVec.ofInt intTy.bitwidth c0.value.value
            let b := BitVec.ofInt intTy.bitwidth c1.value.value
            let bit := BitVec.ofBool (BitVec.uaddOverflow a b)
            some { value := IntegerAttr.ofInt bit.toInt (IntegerType.signless 1) })
      let low ← CreateProg.operation (.arith .constant) #[] #[ty] lowProps
      let high ← CreateProg.operation (.arith .constant) #[] #[carryTy] highProps
      return (low.res[0]!, high.res[0]!))
    (fun (low, high) => #[low, high])

theorem valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  rintro ⟨w, s⟩ carryTy ⟨cw, cs⟩ rfl hCarry c0 v0 h0 c1 v1 h1
    _ r0 r1 hResult _ _
  cases hCarry
  obtain rfl := (constant_iff _ _ _).mp h0
  obtain rfl := (constant_iff _ _ _).mp h1
  obtain ⟨rfl, rfl⟩ := (addui_extended_iff _ _ _ _ _).mp hResult
  simp only [IsTypeAttr.cast?_of]
  let a := BitVec.ofInt w c0.value.value
  let b := BitVec.ofInt w c1.value.value
  let bit := BitVec.ofBool (BitVec.uaddOverflow a b)
  let lo := IntegerAttr.ofInt (a + b).toInt (IntegerType.mk w s)
  let hi := IntegerAttr.ofInt bit.toInt (IntegerType.signless 1)
  refine ⟨.int w (.val (BitVec.ofInt w lo.value)), ?_,
    .int 1 (.val (BitVec.ofInt 1 hi.value)), ?_, ?_⟩
  · exact (constant_iff _ _ _).mpr rfl
  · exact (constant_iff _ _ _).mpr rfl
  · have hlo : BitVec.ofInt w lo.value = a + b := by
      calc
        _ = BitVec.ofInt w (a + b).toInt := ofInt_ofInt _ _
        _ = _ := BitVec.ofInt_toInt
    have hhi : BitVec.ofInt 1 hi.value = bit := by
      calc
        _ = BitVec.ofInt 1 bit.toInt := ofInt_ofInt _ _
        _ = _ := BitVec.ofInt_toInt
    simp [LLVM.Int.add, LLVM.Int.uaddOverflowFlag, hlo, hhi, a, b, bit,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.F006
