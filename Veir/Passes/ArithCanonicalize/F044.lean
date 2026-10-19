import Veir.Passes.ArithCanonicalize.SignedDivisionIdentitySupport

/-! `arith.floordivsi(x, x) -> 1`; zero divisor is undefined. -/

namespace Veir.ArithCanonicalize.F044

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .floordivsi) #[x, x] #[ty]
      return ty)
    (fun ty => createConstant ty 1)
    (fun one => one)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, createConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x divProp divVal hinterpDiv
  obtain ⟨hUB, rfl⟩ := (Veir.ArithCanonicalize.floordivsi_iff _ _ _ _).mp hinterpDiv
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int w (.val (BitVec.ofInt w 1)), ?_,
    Veir.ArithCanonicalize.sfloor_self_refines _ _ hUB⟩
  apply (constant_iff _ _ _).mpr
  simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  split
  · apply BitVec.eq_of_toNat_eq
    change (1 % Int.ofNat (2 ^ w)).toNat =
      ((1 % Int.ofNat (2 ^ w)) % Int.ofNat (2 ^ w)).toNat
    rw [Int.emod_emod]
  · simp

end Veir.ArithCanonicalize.F044
