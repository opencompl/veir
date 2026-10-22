import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Exact scalar empty/full ICmp region, exhaustively by predicate and integer extremum. -/
def IS3146 (pred : LLVM.IntPred) (constant : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
      (fun t => 0 < t.bitwidth && icmpEmptyGuard pred t.bitwidth constant)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let c ← matchIntConstant ty constant
    let _ ← MatchProg.root (.llvm .icmp) #[x,c] #[cty] (fun p => p.predicate == pred)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3146_valid (pred : LLVM.IntPred) (constant : Int) :
    Pattern.Valid (IS3146 pred constant) := by
  simp only [IS3146, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hw hb _ ⟨cw,cs⟩ rfl hc
  have : cw = 1 := by simpa using hc
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x cp cv ch ci
  obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
  intro ip iv ih ii
  obtain rfl := (icmp_iff _ _ _ _ _).mp ii
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  have hp : ip.predicate = pred := by simpa using ih
  cases x with
  | poison => simp [LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val x =>
    have hn := x.isLt
    have hmin := BitVec.toInt_intMin_le x
    have hmax := BitVec.toInt_le (x := x)
    cases pred <;> simp only [icmpEmptyGuard, Bool.false_eq_true] at hb
    all_goals simp only [beq_iff_eq] at hb
    all_goals simp only [LLVM.Int.icmp, Id.run, LLVM.IntPred.eval, hp, hb,
      RuntimeValue.isRefinedBy, isRefinedBy, boolBit_eq_true, boolBit_eq_false]
    all_goals simp only [BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle,
      BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.zero_mod,
      BitVec.toInt_intMax, BitVec.toInt_intMin_of_pos (v := w) (by exact hw)] at hmin ⊢
    all_goals try simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    all_goals try simp
    all_goals omega
end Veir.InstSimplify
