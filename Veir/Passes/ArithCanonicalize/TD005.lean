import Veir.Passes.ArithCanonicalize.MulNegSupport

namespace Veir.ArithCanonicalize.TD005

open Veir Veir.Puddle Veir.Data
open Veir.ArithPuddle

/-- Scalar instance of upstream `AddIMulNegativeOneLhs`. Both source operations retain arbitrary
    overflow flags; the replacement has upstream's default flags. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let minusOne ← MatchProg.operation (.arith .constant) #[] #[ty]
      MatchProg.matchNative (ty, minusOne.properties) (fun (ty, props) =>
        (props.value.type : TypeAttr) == ty &&
        (BitVec.ofInt props.value.type.bitwidth props.value.value) ==
          (BitVec.ofInt props.value.type.bitwidth (-1)))
      let mul ← MatchProg.operation (.arith .muli) #[x, minusOne.res[0]!] #[ty]
      let _ ← MatchProg.root (.arith .addi) #[mul.res[0]!, y] #[ty]
      return (ty, x, y))
    (fun (ty, x, y) => do
      let props ← CreateProg.property (.arith .subi) default
      let replacement ← CreateProg.operation (.arith .subi) #[y, x] #[ty] props
      return replacement)
    (fun result => result)

open Veir.ArithCanonicalize

theorem pattern_valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x y c vc hc pm vm hm pa va ha hty hbits
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (muli_iff _ _ _ _ _).mp hm
  obtain rfl := (addi_iff _ _ _ _ _).mp ha
  have htype : c.value.type = IntegerType.mk w signedness := by grind
  rw [htype] at hbits
  refine ⟨.int w (LLVM.Int.sub y x), ?_, ?_⟩
  · apply (subi_iff _ _ _ _ _).mpr
    rfl
  · rw [hbits]
    exact add_mul_neg_one_comm_refines w y x pm.attr.nsw pm.attr.nuw
      pa.attr.nsw pa.attr.nuw
end Veir.ArithCanonicalize.TD005
