import Veir.Passes.ArithCanonicalize.IntegerSupport

namespace Veir.ArithCanonicalize.TD009

open Veir Veir.Puddle Veir.Data
open Veir.ArithPuddle

/-- Scalar `subi(addi(x,c0),c1) → addi(x,c0-c1)`. The source retains
    arbitrary overflow flags and the replacement uses upstream's default flags. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c0 ← MatchProg.operation (.arith .constant) #[] #[ty]
      let c1 ← MatchProg.operation (.arith .constant) #[] #[ty]
      let inner ← MatchProg.operation (.arith .addi) #[x, c0.res[0]!] #[ty]
      let _ ← MatchProg.root (.arith .subi) #[inner.res[0]!, c1.res[0]!] #[ty]
      return (ty, x, c0.properties, c1.properties))
    (fun (ty, x, c0, c1) => do
      let newConst ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.arith .constant))) (ty, c0, c1)
        (fun (ty, c0, c1) => do
          let some intTy := ty.cast? IntegerType | none
          some { value := IntegerAttr.ofInt (c0.value.value - c1.value.value) intTy })
      let c ← CreateProg.operation (.arith .constant) #[] #[ty] newConst
      let props ← CreateProg.property (.arith .addi) default
      let replacement ← CreateProg.operation (.arith .addi) #[x, c.res[0]!] #[ty] props
      return replacement)
    (fun result => result)

open Veir.ArithCanonicalize.IntegerSupport

theorem pattern_valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x c0 v0 h0 c1 v1 h1 p2 v2 h2 p3 v3 h3
  obtain rfl := (constant_iff _ _ _).mp h0
  obtain rfl := (constant_iff _ _ _).mp h1
  obtain rfl := (addi_iff _ _ _ _ _).mp h2
  obtain rfl := (subi_iff _ _ _ _ _).mp h3
  have hcast : (TypeAttr.of IntegerType (IntegerType.mk w signedness)).cast? IntegerType =
      some (IntegerType.mk w signedness) := by rfl
  simp only [hcast]
  let folded := IntegerAttr.ofInt (c0.value.value - c1.value.value)
    (IntegerType.mk w signedness)
  refine ⟨.int w (.val (BitVec.ofInt w folded.value)), ?_,
    .int w (LLVM.Int.add x (.val (BitVec.ofInt w folded.value))), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    rfl
  · apply (addi_iff _ _ _ _ _).mpr
    rfl
  · have hb : BitVec.ofInt w folded.value =
        BitVec.ofInt w c0.value.value - BitVec.ofInt w c1.value.value := by
      dsimp [folded]
      calc
        _ = BitVec.ofInt w (c0.value.value - c1.value.value) :=
          normalize_bits (IntegerType.mk w signedness) _
        _ = _ := by simp [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
          BitVec.sub_eq_add_neg]
    rw [hb]
    exact sub_add_refines w x _ _ p2.attr.nsw p2.attr.nuw p3.attr.nsw p3.attr.nuw
end Veir.ArithCanonicalize.TD009
