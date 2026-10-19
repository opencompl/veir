import Veir.Passes.ArithCanonicalize.FoldBitwiseSupport

/-! `arith.ori(x, arith.xori(x, all_ones)) -> 0`. -/

namespace Veir.ArithCanonicalize.F060

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
      let _ ← MatchProg.root (.arith .ori) #[x, complement.res[0]!] #[ty]
      return ones.res[0]!)
    pure
    (fun ones => ones)

theorem valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x c vc hc _ vx hx _ va ha hty hbits
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (xori_iff _ _ _ _).mp hx
  obtain rfl := (ori_iff _ _ _ _ _).mp ha
  have htype : c.value.type = IntegerType.mk w signedness := by grind
  rw [htype] at hbits
  rw [hbits]
  exact or_complement_refines w x _

end Veir.ArithCanonicalize.F060
