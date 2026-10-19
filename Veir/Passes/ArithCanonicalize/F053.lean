import Veir.Passes.ArithCanonicalize.FoldBitwiseSupport

/-! `arith.andi(x, all_ones) -> x`. -/

namespace Veir.ArithCanonicalize.F053

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
      let _ ← MatchProg.root (.arith .andi) #[x, ones.res[0]!] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x c vc hc _ result hresult hty hbits
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (andi_iff _ _ _ _).mp hresult
  have htype : c.value.type = IntegerType.mk w signedness := by grind
  rw [htype] at hbits
  rw [hbits]
  exact and_ones_refines w x

end Veir.ArithCanonicalize.F053
