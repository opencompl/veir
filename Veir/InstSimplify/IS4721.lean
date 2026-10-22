import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Power-of-two bit-test/set-mask select. `bit` witnesses the exact upstream power-of-two guard. -/
def IS4721 (mask : Int) (bit : Nat) (trueWhenUnset : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
      (fun t => bit < t.bitwidth && BitVec.ofInt t.bitwidth mask == BitVec.twoPow t.bitwidth bit)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let m ← matchIntConstant ty mask
    let zero ← matchIntConstant ty 0
    let tested ← MatchProg.operation (.llvm .and) #[x,m] #[ty]
    let masked ← MatchProg.operation (.llvm .or) #[x,m] #[ty] (fun p => !trueWhenUnset || !p.disjoint)
    let cmp ← MatchProg.operation (.llvm .icmp) #[tested.res[0]!,zero] #[cty]
      (fun p => p.predicate == (match trueWhenUnset with | true => .eq | false => .ne))
    let _ ← MatchProg.root (.llvm .select) #[cmp.res[0]!,masked.res[0]!,x] #[ty]
    return (match trueWhenUnset with | true => masked.res[0]! | false => x))
  pure (fun x => x)

theorem IS4721_valid (mask : Int) (bit : Nat) (trueWhenUnset : Bool) :
    Pattern.Valid (IS4721 mask bit trueWhenUnset) := by
  cases trueWhenUnset
  all_goals
    simp only [IS4721, matchIntConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hbit he _ ⟨cw,cs⟩ rfl hw
    have : cw = 1 := by simpa using hw
    subst cw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x mp mv mh mi
    obtain rfl := (matched_constant_iff _ _ _ mh _).mp mi
    intro zp zv zh zi
    obtain rfl := (matched_constant_iff _ _ _ zh _).mp zi
    intro tp tv ti
    obtain rfl := (and_iff _ _ _ _ _).mp ti
    intro ap av ah ai
    obtain rfl := (or_iff _ _ _ _ _).mp ai
    intro ip iv ih ii
    obtain rfl := (icmp_iff _ _ _ _ _).mp ii
    intro rp rv ri
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    have hp := ih
    try simp only [beq_iff_eq] at hp
    cases x with
    | poison => simp [LLVM.Int.and, LLVM.Int.or, LLVM.Int.icmp, LLVM.Int.select, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    | val x =>
      by_cases hz : x &&& BitVec.twoPow w bit = 0
      · cases hd : ap.disjoint <;> (try simp [hd] at ah) <;>
          simp [hd,LLVM.Int.and, LLVM.Int.or, LLVM.Int.icmp, LLVM.Int.select, LLVM.IntPred.eval, BitVec.ofNat_eq_ofNat,
            hp, he, beq_iff_eq, bne_iff_ne, hz, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      · have hz0 : x &&& BitVec.twoPow w bit ≠ 0#w := hz
        have heq := set_mask_eq x bit hz
        have hz' : (x &&& BitVec.twoPow w bit == 0#w) = false := by
          exact beq_eq_false_iff_ne.mpr hz
        cases hd : ap.disjoint <;> (try simp [hd] at ah) <;>
          simp [hd,LLVM.Int.and, LLVM.Int.or, LLVM.Int.icmp, LLVM.Int.select, LLVM.IntPred.eval, BitVec.ofNat_eq_ofNat,
            hp, he, hz', bne, hz0, hz, heq, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
