import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Pinned upstream i1 select rule IS5202, including commuted bitwise and short circuit select forms. -/
def IS5202 (swapn2 logicaln2 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let n2 ← (match logicaln2 with
      | true => do
        let z ← matchIntConstant ty 0
        let op ← MatchProg.operation (.llvm .select) #[(match swapn2 with | true => y | false => x),(match swapn2 with | true => x | false => y),z] #[ty]
        pure op.res[0]!
      | false => do
        let op ← MatchProg.operation (.llvm .and) (match swapn2 with | true => #[y,x] | false => #[x,y]) #[ty]
        pure op.res[0]!)
    let c1 ← matchIntConstant ty 1
    let _ ← MatchProg.root (.llvm .select) #[n2,c1,x] #[ty]
    return x)
  pure (fun x => x)

theorem IS5202_valid (swapn2 logicaln2 : Bool) : Pattern.Valid (IS5202 swapn2 logicaln2) := by
  cases swapn2 <;> cases logicaln2
  all_goals
    simp only [IS5202, matchIntConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hw
    have : w = 1 := by simpa using hw
    subst w
    try simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    try simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro y
    first
    | rintro n2p n2v n2i
      obtain rfl := (and_iff _ _ _ _ _).mp n2i
    | rintro n2cp n2cv n2ch n2ci
      obtain rfl := (matched_constant_iff _ _ _ n2ch _).mp n2ci
      rintro n2p n2v n2i
      obtain rfl := (select_iff _ _ _ _ _ _).mp n2i
    rintro c1p c1v c1h c1i
    obtain rfl := (matched_constant_iff _ _ _ c1h _).mp c1i
    rintro rp rv ri
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    rcases int1_cases x with rfl | rfl | rfl <;>
    rcases int1_cases y with rfl | rfl | rfl <;>
      all_goals simp [LLVM.Int.select, LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
