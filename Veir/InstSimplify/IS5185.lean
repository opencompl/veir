import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Pinned upstream i1 select rule IS5185, including commuted bitwise and short circuit select forms. -/
def IS5185 (swapn4 logicaln4 swapn5 logicaln5 : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let c1 ← matchIntConstant ty 1
    let n3op ← MatchProg.operation (.llvm .xor) #[y,c1] #[ty]
    let n3 := n3op.res[0]!
    let n4 ← (match logicaln4 with
      | true => do
        let z ← matchIntConstant ty 1
        let op ← MatchProg.operation (.llvm .select) #[(match swapn4 with | true => n3 | false => x),z,(match swapn4 with | true => x | false => n3)] #[ty]
        pure op.res[0]!
      | false => do
        let op ← MatchProg.operation (.llvm .or) (match swapn4 with | true => #[n3,x] | false => #[x,n3]) #[ty]
        pure op.res[0]!)
    let n5 ← (match logicaln5 with
      | true => do
        let z ← matchIntConstant ty 1
        let op ← MatchProg.operation (.llvm .select) #[(match swapn5 with | true => y | false => x),z,(match swapn5 with | true => x | false => y)] #[ty]
        pure op.res[0]!
      | false => do
        let op ← MatchProg.operation (.llvm .or) (match swapn5 with | true => #[y,x] | false => #[x,y]) #[ty]
        pure op.res[0]!)
    let c0 ← matchIntConstant ty 0
    let _ ← MatchProg.root (.llvm .select) #[n4,n5,c0] #[ty]
    return x)
  pure (fun x => x)

theorem IS5185_valid (swapn4 logicaln4 swapn5 logicaln5 : Bool) : Pattern.Valid (IS5185 swapn4 logicaln4 swapn5 logicaln5) := by
  cases swapn4 <;> cases logicaln4 <;> cases swapn5 <;> cases logicaln5
  all_goals
    simp only [IS5185, matchIntConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hw
    have : w = 1 := by simpa using hw
    subst w
    try simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    try simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro y
    rintro c1p c1v c1h c1i
    obtain rfl := (matched_constant_iff _ _ _ c1h _).mp c1i
    rintro n3p n3v n3i
    obtain rfl := (xor_iff _ _ _ _ _).mp n3i
    first
    | rintro n4p n4v n4i
      obtain rfl := (or_iff _ _ _ _ _).mp n4i
    | rintro n4cp n4cv n4ch n4ci
      obtain rfl := (matched_constant_iff _ _ _ n4ch _).mp n4ci
      rintro n4p n4v n4i
      obtain rfl := (select_iff _ _ _ _ _ _).mp n4i
    first
    | rintro n5p n5v n5i
      obtain rfl := (or_iff _ _ _ _ _).mp n5i
    | rintro n5cp n5cv n5ch n5ci
      obtain rfl := (matched_constant_iff _ _ _ n5ch _).mp n5ci
      rintro n5p n5v n5i
      obtain rfl := (select_iff _ _ _ _ _ _).mp n5i
    rintro c0p c0v c0h c0i
    obtain rfl := (matched_constant_iff _ _ _ c0h _).mp c0i
    rintro rp rv ri
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    rcases int1_cases x with rfl | rfl | rfl <;>
    rcases int1_cases y with rfl | rfl | rfl <;>
      all_goals (try cases n4p.disjoint) <;> (try cases n5p.disjoint) <;> simp [LLVM.Int.select, LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
