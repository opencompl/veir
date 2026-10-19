import Veir.Passes.ArithCanonicalize.BitwiseSupport

namespace Veir.ArithCanonicalize.TD052

open Veir Veir.Puddle Veir.Data
open Veir.ArithPuddle

/-- Scalar instance of upstream `OrIOrIConstant`, retaining the integer-attribute
    result-type guards and the width of its APInt operation. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c0 ← MatchProg.operation (.arith .constant) #[] #[ty]
      let c1 ← MatchProg.operation (.arith .constant) #[] #[ty]
      MatchProg.matchNative (ty, c0.properties, c1.properties)
        (fun (ty, a, b) => (a.value.type : TypeAttr) == ty &&
          (b.value.type : TypeAttr) == ty)
      let inner ← MatchProg.operation (.arith .ori) #[x, c0.res[0]!] #[ty]
      let _ ← MatchProg.root (.arith .ori) #[inner.res[0]!, c1.res[0]!] #[ty]
      return (ty, x, c0.properties, c1.properties))
    (fun (ty, x, c0, c1) => do
      let newConst ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.arith .constant))) (ty, c0, c1)
        (fun (ty, c0, c1) => do
          let some intTy := ty.cast? IntegerType | none
          let bits := (BitVec.ofInt intTy.bitwidth c0.value.value) |||
            (BitVec.ofInt intTy.bitwidth c1.value.value)
          some { value := IntegerAttr.ofInt (Int.ofNat bits.toNat) intTy })
      let c ← CreateProg.operation (.arith .constant) #[] #[ty] newConst
      let props ← CreateProg.property (.arith .ori) default
      let replacement ← CreateProg.operation (.arith .ori) #[x, c.res[0]!] #[ty] props
      return replacement)
    (fun result => result)

open Veir.ArithCanonicalize.BitwiseSupport

theorem pattern_valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x c0 v0 h0 c1 v1 h1 p2 v2 h2 p3 v3 h3 _ _
  obtain rfl := (constant_iff _ _ _).mp h0
  obtain rfl := (constant_iff _ _ _).mp h1
  obtain rfl := (ori_iff _ _ _ _ _).mp h2
  obtain rfl := (ori_iff _ _ _ _ _).mp h3
  have hcast : (TypeAttr.of IntegerType (IntegerType.mk w signedness)).cast? IntegerType =
      some (IntegerType.mk w signedness) := by rfl
  simp only [hcast]
  let ca : BitVec w := BitVec.ofInt w c0.value.value
  let cb : BitVec w := BitVec.ofInt w c1.value.value
  let folded := IntegerAttr.ofInt (Int.ofNat (ca ||| cb).toNat)
    (IntegerType.mk w signedness)
  refine ⟨.int w (.val (BitVec.ofInt w folded.value)), ?_,
    .int w (LLVM.Int.or x (.val (BitVec.ofInt w folded.value)) false), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    rfl
  · apply (ori_iff _ _ _ _ _).mpr
    rfl
  · have hb : BitVec.ofInt w folded.value = ca ||| cb := folded_bits _ _
    rw [hb]
    exact or_assoc_refines w x ca cb p2.disjoint p3.disjoint
end Veir.ArithCanonicalize.TD052
