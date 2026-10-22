import Veir.InstSimplify.CmpCastSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Scalar negated zero extension against a nonnegative signed constant. -/
def IS3489 (constant : Int) : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType)
    let dst ← MatchProg.type (Attr := IntegerType) (fun t => decide (0 ≤ (BitVec.ofInt t.bitwidth constant).toInt))
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value src
    let zero ← matchIntConstant dst 0
    let c ← matchIntConstant dst constant
    let z ← MatchProg.operation (.llvm .zext) #[x] #[dst]
    let neg ← MatchProg.operation (.llvm .sub) #[zero,z.res[0]!] #[dst]
    let _ ← MatchProg.root (.llvm .icmp) #[neg.res[0]!,c] #[cty] (fun p => p.predicate == .sgt)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3489_valid (constant : Int) : Pattern.Valid (IS3489 constant) := by
  simp only [IS3489, matchIntConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ _ ⟨v,ds⟩ rfl hc _ ⟨cw,cs⟩ rfl hcw
  have : cw = 1 := by simpa using hcw
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x zp zv zh zi
  obtain rfl := (matched_constant_iff _ _ _ zh _).mp zi
  intro cp cv ch ci
  obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
  intro ep ev ei
  have hw := logic_zext_width_lt ⟨w,s⟩ ⟨v,ds⟩ _ _ _ ei
  change w < v at hw
  obtain rfl := (logic_zext_iff ⟨w,s⟩ ⟨v,ds⟩ _ _ _ hw).mp ei
  intro np nv ni
  obtain rfl := (sub_iff _ _ _ _ _).mp ni
  intro ip iv ih ii
  obtain rfl := (icmp_iff _ _ _ _ _).mp ii
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  have hconst : 0 ≤ (BitVec.ofInt v constant).toInt := hc
  cases x with
  | poison => simp [LLVM.Int.zext, LLVM.Int.sub, LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val x =>
    rcases logic_zext_outcomes x v ep.nneg hw with hz | hz
    · simp [hz, LLVM.Int.sub, LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    · rw [hz]
      rcases sub_outcomes (BitVec.ofInt v 0) (x.zeroExtend v) np.nsw np.nuw with hn | hn
      · rw [hn]
        simp [LLVM.Int.icmp, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
      · rw [hn]
        have hb := neg_zext_nonpos (v := v) x hw
        have hp : ip.predicate = .sgt := by simpa using ih
        all_goals simp [LLVM.Int.icmp, LLVM.IntPred.eval, hp, BitVec.slt, BitVec.sle,
          bne, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
        all_goals
          simp only [BitVec.zeroExtend] at hb
          simp only [BitVec.toInt_ofInt] at hconst
          omega
end Veir.InstSimplify
