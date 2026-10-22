import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 6000000
/-- Compare unsigned saturation to wrapping arithmetic, with every ordinary-operation overflow flag. -/
def IS3848 (commute reverse : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let sat ← MatchProg.operation (.llvm .intr__uadd__sat) #[x,y] #[ty]
    let raw ← MatchProg.operation (.llvm .add) (match commute with | true => #[y,x] | false => #[x,y]) #[ty]
    let _ ← MatchProg.root (.llvm .icmp)
      (match reverse with | true => #[raw.res[0]!,sat.res[0]!] | false => #[sat.res[0]!,raw.res[0]!]) #[cty]
      (fun p => p.predicate == (match reverse with | true => swapCmpPred .ult | false => .ult))
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3848_valid (commute reverse : Bool) : Pattern.Valid (IS3848 commute reverse) := by
  cases commute <;> cases reverse
  all_goals
    simp only [IS3848]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hw x y sp sv si ap av ai ip iv ih ii
    have : cw = 1 := by simpa using hw
    subst cw
    obtain rfl := (uaddSat_iff _ _ _ _ _).mp si
    obtain rfl := (add_iff _ _ _ _ _).mp ai
    obtain rfl := (icmp_iff _ _ _ _ _).mp ii
    refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
    have hp := ih
    try simp only [beq_iff_eq] at hp
    cases x <;> cases y <;>
      try simp [LLVM.Int.uaddSat, LLVM.Int.add, LLVM.Int.icmp, Id.run, pure,
        RuntimeValue.isRefinedBy, isRefinedBy]
    rename_i x y
    have hadd : y + x = x + y := BitVec.add_comm y x
    have hucomm : BitVec.uaddOverflow y x = BitVec.uaddOverflow x y := by simp [BitVec.uaddOverflow, Nat.add_comm]
    have hscomm : BitVec.saddOverflow y x = BitVec.saddOverflow x y := by simp [BitVec.saddOverflow, Int.add_comm]
    cases hu : BitVec.uaddOverflow x y <;> cases hs : BitVec.saddOverflow x y <;>
      cases hnsw : ap.nsw <;> cases hnuw : ap.nuw <;>
      simp [LLVM.Int.uaddSat, LLVM.Int.add, LLVM.Int.icmp, LLVM.IntPred.eval,
        hp, swapCmpPred, hu, hs, hnsw, hnuw, hadd, hucomm, hscomm, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
