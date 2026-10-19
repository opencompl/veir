import Veir.Passes.ArithCanonicalize.FoldBitwiseSupport

/-! Scalar instances of Arith's generic idempotent trait fold. -/

namespace Veir.ArithCanonicalize.G002

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize

def andPattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .andi) #[x, x] #[ty]
      return x)
    pure
    (fun x => x)

theorem andValid : Pattern.Valid andPattern := by
  unfold andPattern
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x _ result hinterp
  obtain rfl := (andi_iff _ _ _ _).mp hinterp
  exact and_self_refines w x

def orPattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .ori) #[x, x] #[ty]
      return x)
    pure
    (fun x => x)

theorem orValid : Pattern.Valid orPattern := by
  unfold orPattern
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x prop result hinterp
  obtain rfl := (ori_iff _ _ _ _ _).mp hinterp
  exact or_self_refines w x prop.disjoint

end Veir.ArithCanonicalize.G002
