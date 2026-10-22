import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Shared-operand nesting for all four min/max operations and both operand commutations. -/
def IS6760 (kind : MinMaxKind) (si so : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let inner ← MatchProg.operation (.llvm kind.op) (match si with | true => #[y,x] | false => #[x,y]) #[ty]
    let _ ← MatchProg.root (.llvm kind.op) (match so with | true => #[x,inner.res[0]!] | false => #[inner.res[0]!,x]) #[ty]
    return inner.res[0]!)
  pure (fun x => x)
theorem IS6760_valid (kind : MinMaxKind) (si so : Bool) : Pattern.Valid (IS6760 kind si so) := by
  cases kind <;> cases si <;> cases so
  all_goals
    simp only [IS6760, MinMaxKind.op, MinMaxKind.inverse]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y
    rintro ip iv ii
    first
    | obtain rfl := (smax_iff _ _ _ _ _).mp ii
    | obtain rfl := (smin_iff _ _ _ _ _).mp ii
    | obtain rfl := (umax_iff _ _ _ _ _).mp ii
    | obtain rfl := (umin_iff _ _ _ _ _).mp ii
    rintro rp rv ri
    first
    | obtain rfl := (smax_iff _ _ _ _ _).mp ri
    | obtain rfl := (smin_iff _ _ _ _ _).mp ri
    | obtain rfl := (umax_iff _ _ _ _ _).mp ri
    | obtain rfl := (umin_iff _ _ _ _ _).mp ri
    cases x <;> cases y
    all_goals
      simp only [LLVM.Int.smax, LLVM.Int.smin, LLVM.Int.umax, LLVM.Int.umin, Id.run, pure]
      repeat' split
      all_goals simp_all [RuntimeValue.isRefinedBy, isRefinedBy, BitVec.sle, BitVec.ule]
      all_goals
        first
        | apply BitVec.eq_of_toInt_eq; omega
        | apply BitVec.eq_of_toNat_eq; omega
        | omega
end Veir.InstSimplify
