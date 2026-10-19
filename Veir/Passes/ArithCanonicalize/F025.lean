import Veir.Dialects.Arith.Puddle

/-! `arith.divui(0, x) -> 0`; division by zero is undefined. -/

namespace Veir.ArithCanonicalize.F025

open Veir
open Veir.Puddle
open Veir.Data
open Veir.ArithPuddle

private theorem zero_div_refines (w : Nat) (x : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.udiv (.val 0) x exact) ⊒
      .int w (.val 0) := by
  cases x <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.udiv, isRefinedBy, Id.run, pure]
  grind

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let zero ← matchConstant ty 0
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .divui) #[zero, x] #[ty]
      return zero)
    pure
    (fun zero => zero)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ cstProp cstVal propzero hinterpCst x
  obtain rfl := (constant_iff _ _ _).mp hinterpCst
  intro divProp divVal hinterpDiv
  obtain ⟨_, rfl⟩ := (divui_iff _ _ _ _ _).mp hinterpDiv
  simpa [propzero] using zero_div_refines w x divProp.exact

end Veir.ArithCanonicalize.F025
