import Veir.InstSimplify.LowMaskSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2623
/-- The mask has k low bits set; k is unrestricted subject to the source width. -/
def pattern (k : Nat) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let mask ← matchBitConstant ty (Int.ofNat (2^k-1))
    let sub ← MatchProg.operation (.llvm .sub) #[mask,x] #[ty] (fun p => p.nuw)
    let _ ← MatchProg.root (.llvm .xor) #[sub.res[0]!,mask] #[ty]
    MatchProg.matchNative ty (fun ty => match ty.val with | .integerType t => decide (k ≤ t.bitwidth) | _ => false)
    return x) pure (fun x => x)

theorem semantic (w k : Nat) (x : LLVM.Int w) (nsw : Bool) (hk : k ≤ w) :
    RuntimeValue.int w (LLVM.Int.xor (LLVM.Int.sub (.val ((BitVec.allOnes k).zeroExtend w)) x nsw true)
      (.val ((BitVec.allOnes k).zeroExtend w))) ⊒ .int w x := by
  cases x with
  | poison => simp [LLVM.Int.sub,LLVM.Int.xor,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  | val x =>
    let m := (BitVec.allOnes k).zeroExtend w
    by_cases hle : x ≤ m
    · rcases sub_outcomes m x nsw true with hs | hs <;>
        simp [m,hs,LLVM.Int.xor,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy,
          lowmask_sub_xor x m k hk rfl hle]
    · have hu : BitVec.usubOverflow m x = true := by
        simp only [BitVec.usubOverflow,decide_eq_true_eq]
        exact Nat.lt_of_not_ge hle
      have hp : LLVM.Int.sub (.val m) (.val x) nsw true = .poison := by
        simp only [LLVM.Int.sub,Id.run,pure]
        split
        · rfl
        · rw [if_pos (show True ∧ BitVec.usubOverflow m x = true from ⟨True.intro,hu⟩)]
      change RuntimeValue.int w (LLVM.Int.xor (LLVM.Int.sub (.val m) (.val x) nsw true) (.val m)) ⊒ _
      rw [hp]
      simp [LLVM.Int.xor,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure]

theorem valid (k : Nat) : Pattern.Valid (pattern k) := by
  simp only [pattern,matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x mp mv hmi sp sv hp hsi rp rv hri hm hk
  obtain rfl := matched_bit_constant_eq _ _ (Int.ofNat (2^k-1)) _ hmi hm
  have hk : k ≤ w := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hk
  obtain rfl := (sub_iff _ _ _ _ _).mp hsi
  obtain rfl := (xor_iff _ _ _ _ _).mp hri
  have hmask : BitVec.ofInt w (Int.ofNat (2^k-1)) = (BitVec.allOnes k).zeroExtend w := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  simpa only [hmask,hp] using semantic w k x sp.nsw hk
end Veir.InstSimplify.IS2623
