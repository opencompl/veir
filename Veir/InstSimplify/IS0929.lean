import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0929
set_option backward.isDefEq.respectTransparency false
/-- mul nsw i1 X,Y → 0. Every signedness, both operand orders, arbitrary nuw. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .mul) #[x,y] #[ty] (fun p => p.nsw)
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => it.bitwidth == 1
        | _ => false)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

private theorem mul_i1_nsw (x y : LLVM.Int 1) (nu : Bool) :
    RuntimeValue.int 1 (LLVM.Int.mul x y true nu) ⊒ .int 1 (.val 0) := by
  cases x <;> cases y <;>
    simp [LLVM.Int.mul, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  rename_i a b
  rcases BitVec.eq_zero_or_eq_one a with rfl | rfl <;>
    rcases BitVec.eq_zero_or_eq_one b with rfl | rfl <;> simp +decide

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y p v hp hi hw
  have hw' : w = 1 := by
    change (w == 1) = true at hw
    simpa using hw
  subst w
  obtain rfl := (mul_iff 1 p x y v).mp hi
  exists (.int 1 (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hp]
    exact mul_i1_nsw _ _ _
end Veir.InstSimplify.IS0929
