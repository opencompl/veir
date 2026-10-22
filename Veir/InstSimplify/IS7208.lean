import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
def IS7208 (swap : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let z ← matchBitConstant ty (if swap then -1 else 0)
    let _ ← MatchProg.root (.llvm Llvm.intr__usub__sat) (if swap then #[x,z] else #[z,x]) #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let op ← CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p
    pure op.res[0]!) (fun x => x)
theorem IS7208_valid (swap : Bool) : Pattern.Valid (IS7208 swap) := by
  cases swap
  all_goals
    simp only [IS7208, Bool.false_eq_true, ↓reduceIte, matchBitConstant]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro cp cv ci rp rv ri hc
    obtain rfl := matched_bit_constant_eq _ _ _ _ ci hc
    first
    | obtain rfl := (usubSat_iff _ _ _ _ _).mp ri
    refine ⟨.int w (.val 0), ?_, ?_⟩
    · exact (zero_iff ⟨w,s⟩ _ _).mpr rfl
    · cases x with
      | poison => simp [LLVM.Int.usubSat, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      | val x =>
        simp only [LLVM.Int.usubSat, const_negOne, show BitVec.ofInt w 0 = 0 from rfl, Id.run, pure,
          RuntimeValue.isRefinedBy, isRefinedBy]
        split
        · simp
        · rename_i h
          have := BitVec.isLt x
          have := Nat.two_pow_pos w
          first
          | have hx : x = 0 := by
              apply BitVec.eq_of_toNat_eq
              simp [BitVec.usubOverflow] at h ⊢
              omega
            simp [hx]
          | have hx : x = BitVec.allOnes w := by
              apply BitVec.eq_of_toNat_eq
              simp [BitVec.usubOverflow, BitVec.toNat_allOnes] at h ⊢
              omega
            simp [hx]
end Veir.InstSimplify
