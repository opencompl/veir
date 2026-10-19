import Veir.Passes.ArithCanonicalize.FoldBitwiseSupport

/-! `arith.andi(arith.xori(x, all_ones), x) -> 0`. -/

namespace Veir.ArithCanonicalize.F055

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let ones ← MatchProg.operation (.arith .constant) #[] #[ty]
      MatchProg.matchNative (ty, ones.properties) (fun (ty, props) =>
        (props.value.type : TypeAttr) == ty &&
        (BitVec.ofInt props.value.type.bitwidth props.value.value) ==
          (BitVec.ofInt props.value.type.bitwidth (-1)))
      let complement ← MatchProg.operation (.arith .xori) #[x, ones.res[0]!] #[ty]
      let _ ← MatchProg.root (.arith .andi) #[complement.res[0]!, x] #[ty]
      return ty)
    (fun ty => createConstant ty 0)
    (fun zero => zero)

theorem valid : Pattern.Valid pattern := by
  unfold pattern createConstant
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x c vc hc _ vx hx _ va ha hty hbits
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (xori_iff _ _ _ _).mp hx
  obtain rfl := (andi_iff _ _ _ _).mp ha
  have htype : c.value.type = IntegerType.mk w signedness := by grind
  rw [htype] at hbits
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int w (.val 0), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  · rw [hbits]
    exact and_complement_comm_refines w x

end Veir.ArithCanonicalize.F055
