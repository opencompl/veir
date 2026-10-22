import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1490
private theorem ones_shift (w n : Nat) (h : n < w) : ((BitVec.allOnes w) <<< n).sshiftRight n = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, BitVec.msb_eq_getLsbD_last]
  split <;> simp_all <;> omega
private theorem ones_ashr (x : LLVM.Int w) (ex : Bool) :
    RuntimeValue.int w (LLVM.Int.ashr (.val (BitVec.ofInt w (-1))) x ex) ⊒ .int w (.val (BitVec.ofInt w (-1))) := by
  cases x <;> simp [const_negOne, LLVM.Int.ashr, Id.run, pure,
    RuntimeValue.isRefinedBy, isRefinedBy]
  grind
private theorem ones_shl_ashr (a : LLVM.Int w) (p : NswNuwProperties) (ex : Bool) :
    RuntimeValue.int w (LLVM.Int.ashr (LLVM.Int.shl (.val (BitVec.ofInt w (-1))) a p.nsw p.nuw) a ex) ⊒
      .int w (.val (BitVec.ofInt w (-1))) := by
  cases a with
  | poison => simp [LLVM.Int.shl, LLVM.Int.ashr, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val a =>
    by_cases h : BitVec.ofNat w w ≤ a
    · simp [LLVM.Int.shl, LLVM.Int.ashr, Id.run, pure, h, RuntimeValue.isRefinedBy, isRefinedBy]
    · have hw : w < 2 ^ w := Nat.lt_two_pow_self
      have hn : (BitVec.ofNat w w).toNat = w := by simp [Nat.mod_eq_of_lt hw]
      have ha : a.toNat < w := by rw [BitVec.le_def, hn] at h; omega
      simp [LLVM.Int.shl, LLVM.Int.ashr, Id.run, pure, h, RuntimeValue.isRefinedBy,
        isRefinedBy, const_negOne, BitVec.sshiftRight_eq', ones_shift w a.toNat ha]
      grind

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let c ← matchBitConstant ty (-1)
      let _ ← MatchProg.root (.llvm .ashr) #[c,a] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_valid : Pattern.Valid pattern := by
  simp only [pattern, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp (-1) cv hc hz
  obtain rfl := (ashr_iff w p _ a v).mp hi
  exact ones_ashr _ _

def pattern_nested : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let c ← matchBitConstant ty (-1)
      let sh ← MatchProg.operation (.llvm .shl) #[c,a] #[ty]
      let _ ← MatchProg.root (.llvm .ashr) #[sh.res[0]!,a] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_nested_valid : Pattern.Valid pattern_nested := by
  simp only [pattern_nested, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a cp cv hc sp sv hs p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp (-1) cv hc hz
  obtain rfl := (shl_iff w sp _ a sv).mp hs
  obtain rfl := (ashr_iff w p _ a v).mp hi
  exact ones_shl_ashr _ _ _
end Veir.InstSimplify.IS1490
