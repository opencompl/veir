import Veir.Passes.ArithCanonicalize.SignedDivisionIdentitySupport

/-! `arith.floordivsi(x, 1) -> x`. -/

namespace Veir.ArithCanonicalize.F042

open Veir
open Veir.Puddle
open Veir.Data
open Veir.ArithPuddle

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let one ← matchConstant ty 1
      let _ ← MatchProg.root (.arith .floordivsi) #[x, one] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val propone hinterpCst
  obtain rfl := (constant_iff _ _ _).mp hinterpCst
  intro divProp divVal hinterpDiv
  obtain ⟨hdiv, rfl⟩ := (Veir.ArithCanonicalize.floordivsi_iff _ _ _ _).mp hinterpDiv
  simpa [propone] using Veir.ArithCanonicalize.sfloor_one_refines w x
    (by simpa [propone] using hdiv)

end Veir.ArithCanonicalize.F042
