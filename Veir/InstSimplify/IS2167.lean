import Veir.InstSimplify.CmpSelectSupport
import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2167
def pattern (commute : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let c ← matchBitConstant ty 0
    let sel ← MatchProg.operation (.llvm .select) #[a,b,c] #[ty]
    let _ ← MatchProg.root (.llvm .and) (cond commute #[sel.res[0]!,a] #[a,sel.res[0]!]) #[ty]
    MatchProg.matchNative ty (fun ty => match ty.val with | .integerType t => t.bitwidth == 1 | _ => false)
    return sel.res[0]!) pure (fun x => x)

theorem semantic (a b : LLVM.Int 1) (d : Bool) :
    RuntimeValue.int 1 (LLVM.Int.and a (LLVM.Int.select a b (.val 0))) ⊒
      .int 1 (LLVM.Int.select a b (.val 0)) := by
  rcases int1_cases a with rfl | rfl | rfl <;>
    rcases int1_cases b with rfl | rfl | rfl <;> cases d <;>
    simp [LLVM.Int.select,LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure]

theorem valid (commute : Bool) : Pattern.Valid (pattern commute) := by
  cases commute
  all_goals
    simp only [pattern,matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ a b cp cv hci sp sv hsi rp rv hri hc hw
    have hw : w = 1 := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hw
    subst w
    obtain rfl := matched_bit_constant_eq _ _ 0 _ hci hc
    obtain rfl := (select_iff _ _ _ _ _ _).mp hsi
    obtain rfl := (and_iff _ _ _ _ _).mp hri
    simpa [logic_and_comm,logic_or_comm] using semantic a b false
end Veir.InstSimplify.IS2167
