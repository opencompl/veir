import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Upstream guards require a nonzero APInt C, including constants whose signed interpretation is negative. -/
def IS1717 (c : Int) (sw0 sw1 swroot : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let pop ← MatchProg.operation (.llvm .intr__ctpop) #[x] #[ty]
    let cval ← matchBitConstant ty c
    let zero ← matchBitConstant ty 0
    MatchProg.matchNative ty (fun t => match t.val with | .integerType t => !(BitVec.ofInt t.bitwidth c == 0) | _ => false)
    let cmp0 ← MatchProg.operation (.llvm .icmp) (match sw0 with | true => #[cval,pop.res[0]!] | false => #[pop.res[0]!,cval]) #[bt] (fun p => p.predicate == .eq)
    let cmp1 ← MatchProg.operation (.llvm .icmp) (match sw1 with | true => #[zero,x] | false => #[x,zero]) #[bt] (fun p => p.predicate == .ne)
    let _ ← MatchProg.root (.llvm .or) (match swroot with | true => #[cmp1.res[0]!,cmp0.res[0]!] | false => #[cmp0.res[0]!,cmp1.res[0]!]) #[bt]
    return cmp1.res[0]!)
  pure (fun x => x)
theorem IS1717_valid (c : Int) (sw0 sw1 swroot : Bool) : Pattern.Valid (IS1717 c sw0 sw1 swroot) := by
  cases sw0 <;> cases sw1 <;> cases swroot
  all_goals
    simp only [IS1717, matchBitConstant]
    provePuddleValid
    rintro ⟨w,s⟩ _ ⟨bw,bs⟩ rfl hb
    have : bw = 1 := by simpa using hb
    subst bw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro pp pv pi cp cv ci zp zv zi c0p c0v c0h c0i c1p c1v c1h c1i rp rv ri hc hz hn
    have hc0 : c0p.predicate = .eq := by simpa using c0h
    have hc1 : c1p.predicate = .ne := by simpa using c1h
    obtain rfl := (ctpop_iff _ _ _ _).mp pi
    obtain rfl := matched_bit_constant_eq _ _ _ _ ci hc
    obtain rfl := matched_bit_constant_eq _ _ _ _ zi hz
    have hn : BitVec.ofInt w c ≠ 0 := by simpa [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hn
    have hcb : (BitVec.ofInt w c == 0) = false := beq_eq_false_iff_ne.mpr hn
    have hbc : (0 == BitVec.ofInt w c) = false := beq_eq_false_iff_ne.mpr (Ne.symm hn)
    obtain rfl := (icmp_iff _ _ _ _ _).mp c0i
    obtain rfl := (icmp_iff _ _ _ _ _).mp c1i
    obtain rfl := (or_iff _ _ _ _ _).mp ri
    cases x with
    | poison => simp [LLVM.Int.ctpop, LLVM.Int.icmp, LLVM.IntPred.eval, LLVM.Int.and, LLVM.Int.or, hc0,hc1, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
    | val x =>
      by_cases hx : x = 0
      · subst x
        simp only [LLVM.Int.ctpop, LLVM.Int.icmp, hc0,hc1, LLVM.IntPred.eval, Id.run, pure]
        simp only [BitVec.cpop_zero, bne, hcb,hbc, BEq.rfl]
        simp [LLVM.Int.and, LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
        first | exact hn | exact Ne.symm hn | grind
      · have hxb : (x == 0) = false := beq_eq_false_iff_ne.mpr hx
        have hbx : (0 == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hx)
        simp only [LLVM.Int.ctpop, LLVM.Int.icmp, hc0,hc1, LLVM.IntPred.eval, Id.run, pure]
        simp only [bne, hxb,hbx]
        simp [LLVM.Int.and, LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
        repeat' split
        all_goals
          simp_all [RuntimeValue.isRefinedBy, isRefinedBy]
          try grind
end Veir.InstSimplify
