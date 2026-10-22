import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Both abs occurrences retain independent INT_MIN flags; negation retains arbitrary no-wrap flags. -/
def IS4938 (swapcmp : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => 0 < t.bitwidth)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let zero ← matchBitConstant ty 0
    let cmp ← MatchProg.operation (.llvm .icmp) (match swapcmp with | true => #[zero,x] | false => #[x,zero]) #[bt] (fun p => p.predicate == .eq)
    let absa ← MatchProg.operation (.llvm .intr__abs) #[x] #[ty]
    let absb ← MatchProg.operation (.llvm .intr__abs) #[x] #[ty]
    let nz ← matchBitConstant ty 0
    let neg ← MatchProg.operation (.llvm .sub) #[nz,absa.res[0]!] #[ty]
    let _ ← MatchProg.root (.llvm .select) #[cmp.res[0]!,neg.res[0]!,absb.res[0]!] #[ty]
    return absb.res[0]!)
  pure (fun x => x)
theorem IS4938_valid (swapcmp : Bool) : Pattern.Valid (IS4938 swapcmp) := by
  cases swapcmp
  all_goals
    simp only [IS4938, matchBitConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hw _ ⟨bw,bs⟩ rfl hb
    have hw : 0 < w := by simpa using hw
    have : bw = 1 := by simpa using hb
    subst bw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro zp zv zi cp cv ch ci ap av ai bp bv bi nzp nzv nzi np nv ni rp rv ri hz hnz
    obtain rfl := matched_bit_constant_eq _ _ _ _ zi hz
    obtain rfl := matched_bit_constant_eq _ _ _ _ nzi hnz
    have hp : cp.predicate = .eq := by simpa using ch
    obtain rfl := (icmp_iff _ _ _ _ _).mp ci
    obtain rfl := (abs_iff _ _ _ _).mp ai
    obtain rfl := (abs_iff _ _ _ _).mp bi
    obtain rfl := (sub_iff _ _ _ _ _).mp ni
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    cases x with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.Int.abs, LLVM.Int.sub, hp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val x =>
      by_cases hx : x = 0#w
      · subst x
        have hmin : (0#w) ≠ BitVec.intMin w := by
          intro he
          have hh := BitVec.intMin_eq_zero_iff.mp he.symm
          omega
        have hcmp : LLVM.Int.icmp (.val (0#w)) (.val (0#w)) .eq = .val 1 := by rfl
        simp [LLVM.Int.icmp, LLVM.IntPred.eval, LLVM.Int.select, LLVM.Int.abs, LLVM.Int.sub,
          BitVec.ssubOverflow_eq, BitVec.usubOverflow, hp,hmin, Ne.symm hmin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
      · have hb : (x == 0#w) = false := beq_eq_false_iff_ne.mpr hx
        have hb' : (0#w == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hx)
        simp only [LLVM.Int.icmp, LLVM.IntPred.eval, hp, Id.run, pure]
        try simp only [hb,hb']
        simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
        first | rw [if_neg hx] | rw [if_neg (Ne.symm hx)]
        split <;> grind
end Veir.InstSimplify
