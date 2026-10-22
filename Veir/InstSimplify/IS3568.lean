import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Arbitrary-width constant-mask subset comparison; both AND/OR and operand canonicalizations. -/
def IS3568 (small large : Int) (useOr reverse : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => (BitVec.ofInt t.bitwidth small &&& BitVec.ofInt t.bitwidth large == BitVec.ofInt t.bitwidth small) && ((BitVec.ofInt t.bitwidth small).msb == (BitVec.ofInt t.bitwidth large).msb))
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let a ← matchIntConstant ty small
    let b ← matchIntConstant ty large
    let lhs ← MatchProg.operation (.llvm (match useOr with | true => .or | false => .and)) #[x,a] #[ty]
    let rhs ← MatchProg.operation (.llvm (match useOr with | true => .or | false => .and)) #[x,b] #[ty]
    let _ ← MatchProg.root (.llvm .icmp)
      (match reverse with | true => #[rhs.res[0]!,lhs.res[0]!] | false => #[lhs.res[0]!,rhs.res[0]!]) #[cty]
      (fun p => p.predicate == (match reverse with | true => swapCmpPred .sle | false => .sle))
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3568_valid (small large : Int) (useOr reverse : Bool) :
    Pattern.Valid (IS3568 small large useOr reverse) := by
  cases useOr <;> cases reverse
  all_goals
    simp only [IS3568]
    simp only [matchIntConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hsub hsign _ ⟨cw,cs⟩ rfl hw
    have : cw = 1 := by simpa using hw
    subst cw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x ap av ah ai
    obtain rfl := (matched_constant_iff _ _ _ ah _).mp ai
    intro bp bv bh bi
    obtain rfl := (matched_constant_iff _ _ _ bh _).mp bi
    intro lp lv li
    first | obtain rfl := (and_iff _ _ _ _ _).mp li
          | obtain rfl := (or_iff _ _ _ _ _).mp li
    intro rp rv ri
    first | obtain rfl := (and_iff _ _ _ _ _).mp ri
          | obtain rfl := (or_iff _ _ _ _ _).mp ri
    intro ip iv ih ii
    obtain rfl := (icmp_iff _ _ _ _ _).mp ii
    refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
    have hp := ih
    try simp only [beq_iff_eq] at hp
    cases x with
    | poison => simp [LLVM.Int.and, LLVM.Int.or, LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    | val x =>
      have ha := subset_toNat_le _ _ (and_mask_subset x (BitVec.ofInt w small) (BitVec.ofInt w large) hsub)
      have ho := subset_toNat_le _ _ (or_mask_subset x (BitVec.ofInt w small) (BitVec.ofInt w large) hsub)
      have hau : (x &&& BitVec.ofInt w small).ule (x &&& BitVec.ofInt w large) = true := by simpa [BitVec.ule] using ha
      have hou : (x ||| BitVec.ofInt w small).ule (x ||| BitVec.ofInt w large) = true := by simpa [BitVec.ule] using ho
      have hag : (x &&& BitVec.ofInt w large).ult (x &&& BitVec.ofInt w small) = false := by simp only [BitVec.ult, decide_eq_false_iff_not]; omega
      have hog : (x ||| BitVec.ofInt w large).ult (x ||| BitVec.ofInt w small) = false := by simp only [BitVec.ult, decide_eq_false_iff_not]; omega
      have has : (x &&& BitVec.ofInt w small).sle (x &&& BitVec.ofInt w large) = true := by
        rw [BitVec.sle_eq_ule_of_msb_eq (by simp [hsign])]; exact hau
      have hos : (x ||| BitVec.ofInt w small).sle (x ||| BitVec.ofInt w large) = true := by
        rw [BitVec.sle_eq_ule_of_msb_eq (by simp [hsign])]; exact hou
      have hasg : (x &&& BitVec.ofInt w large).slt (x &&& BitVec.ofInt w small) = false := by
        rw [BitVec.slt_eq_ult_of_msb_eq (by simp [hsign])]; exact hag
      have hosg : (x ||| BitVec.ofInt w large).slt (x ||| BitVec.ofInt w small) = false := by
        rw [BitVec.slt_eq_ult_of_msb_eq (by simp [hsign])]; exact hog
      first
      | solve | simp [LLVM.Int.and, LLVM.Int.icmp, LLVM.IntPred.eval, swapCmpPred, hp, Id.run,
          RuntimeValue.isRefinedBy, isRefinedBy, hau, hag, has, hasg]
      | cases hlf : lp.disjoint <;> cases hrf : rp.disjoint <;>
          by_cases hlz : x &&& BitVec.ofInt w small = 0#w <;>
          by_cases hrz : x &&& BitVec.ofInt w large = 0#w <;>
          simp [LLVM.Int.or, LLVM.Int.icmp, LLVM.IntPred.eval, swapCmpPred, hp, hlf, hrf,
            hlz, hrz, hou, hog, hos, hosg, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
