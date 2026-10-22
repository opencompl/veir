import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
def IS7213 (signed : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm (if signed then Llvm.intr__ssub__sat else .intr__usub__sat)) #[x,x] #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let op ← CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p
    pure op.res[0]!) (fun x => x)
theorem IS7213_valid (signed : Bool) : Pattern.Valid (IS7213 signed) := by
  cases signed
  all_goals
    simp only [IS7213, Bool.false_eq_true, ↓reduceIte, matchBitConstant]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro rp rv ri
    first
    | obtain rfl := (ssubSat_iff _ _ _ _ _).mp ri
    | obtain rfl := (usubSat_iff _ _ _ _ _).mp ri
    refine ⟨.int w (.val 0), ?_, ?_⟩
    · exact (zero_iff ⟨w,s⟩ _ _).mpr rfl
    · cases x <;> simp [LLVM.Int.saddSat, LLVM.Int.uaddSat, LLVM.Int.ssubSat, LLVM.Int.usubSat,
      BitVec.saddOverflow_eq, BitVec.ssubOverflow_eq, BitVec.uaddOverflow, BitVec.usubOverflow, Nat.not_le.mpr (BitVec.isLt _),
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
