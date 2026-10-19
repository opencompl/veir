import Veir.Passes.ArithCanonicalize.ShiftSupport
import Veir.Passes.ArithCanonicalize.BitwiseSupport

/-! Scalar `arith.shrsi` constant evaluation. -/

namespace Veir.ArithCanonicalize.F080

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.BitwiseSupport
open Veir.ArithCanonicalize

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let c0 ← MatchProg.operation (.arith .constant) #[] #[ty]
      let c1 ← MatchProg.operation (.arith .constant) #[] #[ty]
      MatchProg.matchNative (ty, c0.properties, c1.properties)
        (fun (ty, a, b) => (a.value.type : TypeAttr) == ty &&
          (b.value.type : TypeAttr) == ty &&
          decide ((BitVec.ofInt b.value.type.bitwidth b.value.value).toNat <
            b.value.type.bitwidth))
      let _ ← MatchProg.root (.arith .shrsi) #[c0.res[0]!, c1.res[0]!] #[ty]
      return (ty, c0.properties, c1.properties))
    (fun (ty, c0, c1) => do
      let props ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.arith .constant))) (ty, c0, c1)
          (fun (ty, c0, c1) => do
            let some intTy := ty.cast? IntegerType | none
            let a := BitVec.ofInt intTy.bitwidth c0.value.value
            let b := BitVec.ofInt intTy.bitwidth c1.value.value
            some { value := IntegerAttr.ofInt (Int.ofNat (a.sshiftRight' b).toNat) intTy })
      let result ← CreateProg.operation (.arith .constant) #[] #[ty] props
      return result.res[0]!)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  rintro ⟨w, signedness⟩ c0 v0 h0 c1 v1 h1 opProp v2 h2 hty0 hty1 hbound
  obtain rfl := (constant_iff _ _ _).mp h0
  obtain rfl := (constant_iff _ _ _).mp h1
  obtain rfl := (shrsi_iff _ _ _ _ _).mp h2
  have hcast : (TypeAttr.of IntegerType (IntegerType.mk w signedness)).cast? IntegerType =
      some (IntegerType.mk w signedness) := by rfl
  simp only [hcast]
  have htype : c1.value.type = IntegerType.mk w signedness := by grind
  rw [htype] at hbound
  let a : BitVec w := BitVec.ofInt w c0.value.value
  let b : BitVec w := BitVec.ofInt w c1.value.value
  let folded := IntegerAttr.ofInt (Int.ofNat (a.sshiftRight' b).toNat)
    (IntegerType.mk w signedness)
  refine ⟨.int w (.val (BitVec.ofInt w folded.value)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    rfl
  · have hb : BitVec.ofInt w folded.value = a.sshiftRight' b := folded_bits _ _
    rw [hb]
    exact ashr_const_refines w a b opProp.exact (by simpa [b] using hbound)

end Veir.ArithCanonicalize.F080
