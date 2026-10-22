import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Pinned upstream i1 select rule IS5179, including commuted bitwise and short circuit select forms. -/
def IS5179 (swapn2 logicaln2 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let y ← MatchProg.value ty
    let x ← MatchProg.value ty
    let n2 ← (match logicaln2 with
      | true => do
        let z ← matchIntConstant ty 1
        let op ← MatchProg.operation (.llvm .select) #[(match swapn2 with | true => y | false => x),z,(match swapn2 with | true => x | false => y)] #[ty]
        pure op.res[0]!
      | false => do
        let op ← MatchProg.operation (.llvm .or) (match swapn2 with | true => #[y,x] | false => #[x,y]) #[ty]
        pure op.res[0]!)
    let c0 ← matchIntConstant ty 0
    let _ ← MatchProg.root (.llvm .select) #[y,n2,c0] #[ty]
    return y)
  pure (fun x => x)

theorem IS5179_valid (swapn2 logicaln2 : Bool) : Pattern.Valid (IS5179 swapn2 logicaln2) := by
  cases swapn2 <;> cases logicaln2
  all_goals
    simp only [IS5179, matchIntConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hw
    have : w = 1 := by simpa using hw
    subst w
    try simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro y
    try simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    first
    | rintro n2p n2v n2i
      obtain rfl := (or_iff _ _ _ _ _).mp n2i
    | rintro n2cp n2cv n2ch n2ci
      obtain rfl := (matched_constant_iff _ _ _ n2ch _).mp n2ci
      rintro n2p n2v n2i
      obtain rfl := (select_iff _ _ _ _ _ _).mp n2i
    rintro c0p c0v c0h c0i
    obtain rfl := (matched_constant_iff _ _ _ c0h _).mp c0i
    rintro rp rv ri
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    rcases int1_cases y with rfl | rfl | rfl <;>
    rcases int1_cases x with rfl | rfl | rfl <;>
      all_goals (try cases n2p.disjoint) <;> simp [LLVM.Int.select, LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
