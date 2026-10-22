import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Arbitrary-width bit-test/clear-mask select; exact LLVM complement guard. -/
def IS4705 (mask complement : Int) (trueWhenUnset : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
      (fun t => BitVec.ofInt t.bitwidth complement == ~~~(BitVec.ofInt t.bitwidth mask))
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let m ← matchIntConstant ty mask
    let cm ← matchIntConstant ty complement
    let zero ← matchIntConstant ty 0
    let tested ← MatchProg.operation (.llvm .and) #[x,cm] #[ty]
    let masked ← MatchProg.operation (.llvm .and) #[x,m] #[ty]
    let cmp ← MatchProg.operation (.llvm .icmp) #[tested.res[0]!,zero] #[cty]
      (fun p => p.predicate == (match trueWhenUnset with | true => .eq | false => .ne))
    let _ ← MatchProg.root (.llvm .select) #[cmp.res[0]!,masked.res[0]!,x] #[ty]
    return (match trueWhenUnset with | true => x | false => masked.res[0]!))
  pure (fun x => x)

theorem IS4705_valid (mask complement : Int) (trueWhenUnset : Bool) :
    Pattern.Valid (IS4705 mask complement trueWhenUnset) := by
  cases trueWhenUnset
  all_goals
    simp only [IS4705, matchIntConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hm _ ⟨cw,cs⟩ rfl hw
    have he : BitVec.ofInt w complement = ~~~(BitVec.ofInt w mask) := by simpa using hm
    have : cw = 1 := by simpa using hw
    subst cw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x mp mv mh mi
    obtain rfl := (matched_constant_iff _ _ _ mh _).mp mi
    intro cp cv ch ci
    obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
    intro zp zv zh zi
    obtain rfl := (matched_constant_iff _ _ _ zh _).mp zi
    intro tp tv ti
    obtain rfl := (and_iff _ _ _ _ _).mp ti
    intro ap av ai
    obtain rfl := (and_iff _ _ _ _ _).mp ai
    intro ip iv ih ii
    obtain rfl := (icmp_iff _ _ _ _ _).mp ii
    intro rp rv ri
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    have hp := ih
    try simp only [beq_iff_eq] at hp
    cases x with
    | poison => simp [LLVM.Int.and, LLVM.Int.icmp, LLVM.Int.select, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    | val x =>
      by_cases hz : x &&& ~~~(BitVec.ofInt w mask) = 0
      · have heq := clear_mask_eq x (BitVec.ofInt w mask) hz
        simp [LLVM.Int.and, LLVM.Int.icmp, LLVM.Int.select, LLVM.IntPred.eval, BitVec.ofNat_eq_ofNat,
          hp, he, beq_iff_eq, bne_iff_ne, hz, heq, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      · have hz' : (x &&& ~~~(BitVec.ofInt w mask) == 0#w) = false := by
          exact beq_eq_false_iff_ne.mpr hz
        simp [LLVM.Int.and, LLVM.Int.icmp, LLVM.Int.select, LLVM.IntPred.eval, BitVec.ofNat_eq_ofNat,
          hp, he, hz', bne, hz, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
