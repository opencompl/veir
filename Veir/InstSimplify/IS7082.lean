import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Integer min/max saturation boundary, including commuted operands and APInt spellings. -/
def IS7082 (kind : MinMaxKind) (swap : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let c ← matchMinMaxLimit ty kind
    let _ ← MatchProg.root (.llvm kind.op) (match swap with | true => #[c,x] | false => #[x,c]) #[ty]
    return c)
  pure (fun x => x)
theorem IS7082_valid (kind : MinMaxKind) (swap : Bool) : Pattern.Valid (IS7082 kind swap) := by
  cases kind <;> cases swap
  all_goals
    simp only [IS7082, MinMaxKind.op, MinMaxKind.inverse, matchMinMaxLimit]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro cp cv ci rp rv ri hc
    obtain rfl := matched_minmax_limit_eq _ _ _ _ ci hc
    first
    | obtain rfl := (smax_iff _ _ _ _ _).mp ri
    | obtain rfl := (smin_iff _ _ _ _ _).mp ri
    | obtain rfl := (umax_iff _ _ _ _ _).mp ri
    | obtain rfl := (umin_iff _ _ _ _ _).mp ri
    cases x with
    | poison => simp [LLVM.Int.smax, LLVM.Int.smin, LLVM.Int.umax, LLVM.Int.umin, MinMaxKind.saturation,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val x =>
      have hs := BitVec.toInt_le (x := x)
      have hl := BitVec.toInt_intMin_le x
      have hu := BitVec.isLt x
      simp [LLVM.Int.smax, LLVM.Int.smin, LLVM.Int.umax, LLVM.Int.umin, MinMaxKind.saturation,
        BitVec.sle, BitVec.ule, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      all_goals
        try intro h
        try have hh := of_decide_eq_true h
        try have hh := of_decide_eq_false h
        first
        | apply BitVec.eq_of_toInt_eq
          try simp only [BitVec.toInt_intMax]
          omega
        | apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_allOnes, BitVec.toNat_zero]
          omega
        | omega
end Veir.InstSimplify
