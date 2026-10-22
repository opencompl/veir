import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Min/max intrinsics sharing an operand; all common operand positions and comparison sides. -/
def IS3793 (maxCommute minCommute reverse : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let z ← MatchProg.value ty
    let hi ← MatchProg.operation (.llvm .intr__smax)
      (match maxCommute with | true => #[y,x] | false => #[x,y]) #[ty]
    let lo ← MatchProg.operation (.llvm .intr__smin)
      (match minCommute with | true => #[z,x] | false => #[x,z]) #[ty]
    let _ ← MatchProg.root (.llvm .icmp)
      (match reverse with | true => #[lo.res[0]!,hi.res[0]!] | false => #[hi.res[0]!,lo.res[0]!]) #[cty]
      (fun p => p.predicate == (match reverse with | true => swapCmpPred .sge | false => .sge))
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3793_valid (maxCommute minCommute reverse : Bool) : Pattern.Valid (IS3793 maxCommute minCommute reverse) := by
  cases maxCommute <;> cases minCommute <;> cases reverse
  all_goals
    simp only [IS3793]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hw x y z hp hv hi lp lv li ip iv ih ii
    have : cw = 1 := by simpa using hw
    subst cw
    obtain rfl := (smax_iff _ _ _ _ _).mp hi
    obtain rfl := (smin_iff _ _ _ _ _).mp li
    obtain rfl := (icmp_iff _ _ _ _ _).mp ii
    refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
    have hc := ih
    try simp only [beq_iff_eq] at hc
    cases x <;> cases y <;> cases z <;>
      simp [LLVM.Int.smax, LLVM.Int.smin, LLVM.Int.umax, LLVM.Int.umin,
        LLVM.Int.icmp, LLVM.IntPred.eval, swapCmpPred, hc,
        Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals (try split) <;> try simp_all [BitVec.sle, BitVec.slt, BitVec.ule, BitVec.ult]
    all_goals (try split) <;> try simp_all [BitVec.sle, BitVec.slt, BitVec.ule, BitVec.ult]
    all_goals omega
end Veir.InstSimplify
