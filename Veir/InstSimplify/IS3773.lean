import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Scalar min/max versus one of its operands; both sides and both intrinsic operand orders. -/
def IS3773 (isMin commute onRhs : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let mm ← MatchProg.operation (.llvm (minmaxKind false isMin).op)
      (match commute with | true => #[y,x] | false => #[x,y]) #[ty]
    let _ ← MatchProg.root (.llvm .icmp)
      (match onRhs with | true => #[x,mm.res[0]!] | false => #[mm.res[0]!,x]) #[cty]
      (fun p => p.predicate == (match isMin != onRhs with | true => swapCmpPred .uge | false => .uge))
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3773_valid (isMin commute onRhs : Bool) : Pattern.Valid (IS3773 isMin commute onRhs) := by
  cases commute <;> cases onRhs
  all_goals
    simp only [IS3773]
    unfoldPuddleBuilder
    constructor
    · cases isMin <;> simp only [minmaxKind, MinMaxKind.op] <;> provePuddleSupported
    · cbv
    · open scoped PuddleCbv in cbv
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hw x y mp mv mi ip iv ih ii
    have : cw = 1 := by simpa using hw
    subst cw
    obtain rfl := (minmax_iff (minmaxKind false isMin) _ _ _ _ _).mp mi
    obtain rfl := (icmp_iff _ _ _ _ _).mp ii
    refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
    have hp := ih
    try simp only [beq_iff_eq] at hp
    cases x <;> cases y <;> cases isMin <;>
      simp [minmaxKind, MinMaxKind.eval, LLVM.Int.smax, LLVM.Int.smin, LLVM.Int.umax, LLVM.Int.umin,
        LLVM.Int.icmp, LLVM.IntPred.eval, swapCmpPred, hp,
        Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals split <;> simp_all [BitVec.sle, BitVec.slt, BitVec.ule, BitVec.ult]
    all_goals omega
end Veir.InstSimplify
