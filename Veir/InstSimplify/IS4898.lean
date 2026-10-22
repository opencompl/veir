import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Zero-shift select guard for both funnel directions and both equality operand orders. -/
def IS4898 (left swapcmp : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let c ← MatchProg.value ty
    let zero ← matchBitConstant ty 0
    let cmp ← MatchProg.operation (.llvm .icmp) (match swapcmp with | false => #[c,zero] | true => #[zero,c]) #[bt] (fun p => p.predicate == .eq)
    let f ← MatchProg.operation (.llvm (match left with | true => Llvm.intr__fshl | false => .intr__fshr)) (match left with | true => #[x,y,c] | false => #[y,x,c]) #[ty]
    let _ ← MatchProg.root (.llvm .select) #[cmp.res[0]!,f.res[0]!,x] #[ty]
    return x)
  pure (fun x => x)
theorem IS4898_valid (left swapcmp : Bool) : Pattern.Valid (IS4898 left swapcmp) := by
  cases left <;> cases swapcmp
  all_goals
    simp only [IS4898, matchBitConstant]
    provePuddleValid
    rintro ⟨w,s⟩ _ ⟨bw,bs⟩ rfl hb
    have : bw = 1 := by simpa using hb
    subst bw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y c
    rintro zp zv zi cp cv ch ci fp fv fi rp rv ri hz
    obtain rfl := matched_bit_constant_eq _ _ _ _ zi hz
    have hp : cp.predicate = .eq := by simpa using ch
    obtain rfl := (icmp_iff _ _ _ _ _).mp ci
    first
    | obtain rfl := (fshl_iff _ _ _ _ _ _).mp fi
    | obtain rfl := (fshr_iff _ _ _ _ _ _).mp fi
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    cases c with
    | poison => simp [LLVM.Int.icmp,LLVM.Int.select,LLVM.Int.fshl,LLVM.Int.fshr,hp,RuntimeValue.isRefinedBy,isRefinedBy,Id.run]
    | val c =>
      by_cases hc : c = 0#w
      · subst c
        cases x <;> cases y
        all_goals
          simp [LLVM.Int.icmp,LLVM.IntPred.eval,LLVM.Int.select,LLVM.Int.fshl,LLVM.Int.fshr,hp,
            BitVec.extractLsb'_append_eq_left,BitVec.setWidth_append_eq_right,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure]
      · simp only [LLVM.Int.icmp,LLVM.IntPred.eval,hp,Id.run,pure]
        simp [LLVM.Int.select,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure]
        first | rw [if_neg hc] | rw [if_neg (Ne.symm hc)]
        split <;> grind
end Veir.InstSimplify
