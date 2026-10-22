import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Pinned upstream i1 select rule IS5198, including commuted bitwise and short circuit select forms. -/
def IS5198 (swapn3 logicaln3 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let c1 ← matchIntConstant ty 1
    let y ← MatchProg.value ty
    let n3 ← (match logicaln3 with
      | true => do
        let z ← matchIntConstant ty 0
        let op ← MatchProg.operation (.llvm .select) #[(match swapn3 with | true => y | false => x),(match swapn3 with | true => x | false => y),z] #[ty]
        pure op.res[0]!
      | false => do
        let op ← MatchProg.operation (.llvm .and) (match swapn3 with | true => #[y,x] | false => #[x,y]) #[ty]
        pure op.res[0]!)
    let n4op ← MatchProg.operation (.llvm .xor) #[n3,c1] #[ty]
    let n4 := n4op.res[0]!
    let _ ← MatchProg.root (.llvm .select) #[x,c1,n4] #[ty]
    return c1)
  pure (fun x => x)

theorem IS5198_valid (swapn3 logicaln3 : Bool) : Pattern.Valid (IS5198 swapn3 logicaln3) := by
  cases swapn3 <;> cases logicaln3
  all_goals
    simp only [IS5198, matchIntConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hw
    have : w = 1 := by simpa using hw
    subst w
    try simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro c1p c1v c1h c1i
    obtain rfl := (matched_constant_iff _ _ _ c1h _).mp c1i
    try simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro y
    first
    | rintro n3p n3v n3i
      obtain rfl := (and_iff _ _ _ _ _).mp n3i
    | rintro n3cp n3cv n3ch n3ci
      obtain rfl := (matched_constant_iff _ _ _ n3ch _).mp n3ci
      rintro n3p n3v n3i
      obtain rfl := (select_iff _ _ _ _ _ _).mp n3i
    rintro n4p n4v n4i
    obtain rfl := (xor_iff _ _ _ _ _).mp n4i
    rintro rp rv ri
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    rcases int1_cases x with rfl | rfl | rfl <;>
    rcases int1_cases y with rfl | rfl | rfl <;>
      all_goals simp [LLVM.Int.select, LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
