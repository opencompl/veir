import Veir.Passes.ArithCanonicalize.ShiftSupport

/-! `arith.shrsi(all_ones, x) -> x`. -/

namespace Veir.ArithCanonicalize.F079

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let ones ← MatchProg.operation (.arith .constant) #[] #[ty]
      MatchProg.matchNative (ty, ones.properties) (fun (ty, props) =>
        (props.value.type : TypeAttr) == ty &&
        (BitVec.ofInt props.value.type.bitwidth props.value.value) ==
          (BitVec.ofInt props.value.type.bitwidth (-1)))
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .shrsi) #[ones.res[0]!, x] #[ty]
      return ones.res[0]!)
    pure
    (fun ones => ones)

theorem valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ c vc hc x opProp result hresult hty hbits
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (shrsi_iff _ _ _ _ _).mp hresult
  have htype : c.value.type = IntegerType.mk w signedness := by grind
  rw [htype] at hbits
  rw [hbits]
  exact ashr_allones_refines w x opProp.exact

end Veir.ArithCanonicalize.F079
