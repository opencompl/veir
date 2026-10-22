import Veir.InstSimplify.LogicExtra
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2119
def pattern (amount mask : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let a ← matchBitConstant ty amount
    let m ← matchBitConstant ty mask
    let shifted ← MatchProg.operation (.llvm .lshr) #[x,a] #[ty]
    let _ ← MatchProg.root (.llvm .and) #[shifted.res[0]!,m] #[ty]
    MatchProg.matchNative ty (fun ty => match ty.val with
      | .integerType t => ((~~~(BitVec.ofInt t.bitwidth mask)) <<< (BitVec.ofInt t.bitwidth amount).toNat) == 0
      | _ => false)
    return shifted.res[0]!) pure (fun x => x)

theorem semantic (w : Nat) (x : LLVM.Int w) (a m : BitVec w) (f0 : Bool)
    (h : (~~~m) <<< a.toNat = 0) :
    RuntimeValue.int w (LLVM.Int.and (LLVM.Int.lshr x (.val a) f0) (.val m)) ⊒
      .int w (LLVM.Int.lshr x (.val a) f0) := by
  cases x with
  | poison => simp [LLVM.Int.lshr,LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure]
  | val x =>
    simp only [LLVM.Int.lshr,Id.run,pure]
    all_goals (try split at * <;> simp_all [LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure])
    all_goals (try split at * <;> simp_all [LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure])
    all_goals (try split at * <;> simp_all [LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure])
    all_goals (try split at * <;> simp_all [LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure])
    all_goals (try split at * <;> simp_all [LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure])
    all_goals (try split at * <;> simp_all [LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure])
    all_goals (try split at * <;> simp_all [LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure])
    all_goals (try split at * <;> simp_all [LLVM.Int.and,RuntimeValue.isRefinedBy,isRefinedBy,Id.run,pure])
    all_goals have hm := mask_shift_right x m a.toNat h
    all_goals grind only [LLVM.Int.val.injEq, BitVec.shiftLeft_eq',BitVec.ushiftRight_eq']

theorem valid (amount mask : Int) : Pattern.Valid (pattern amount mask) := by
  simp only [pattern,matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x ap av hai mp mv hmi sp sv hsi rp rv hri ha hm hg
  obtain rfl := matched_bit_constant_eq _ _ amount _ hai ha
  obtain rfl := matched_bit_constant_eq _ _ mask _ hmi hm
  obtain rfl := (lshr_iff _ _ _ _ _).mp hsi
  obtain rfl := (and_iff _ _ _ _ _).mp hri
  have hg : (~~~(BitVec.ofInt w mask)) <<< (BitVec.ofInt w amount).toNat = 0 := by
    simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hg
  exact semantic w x _ _ sp.exact hg
end Veir.InstSimplify.IS2119
