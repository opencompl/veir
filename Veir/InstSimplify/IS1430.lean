import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1430
private theorem both_shift_zero (a : BitVec w) (hw : 1 < w)
    (hu : (a <<< (w-1)) >>> (w-1) = a)
    (hs : (a <<< (w-1)).sshiftRight (w-1) = a) : a = 0 := by
  have hb := congrArg BitVec.msb hu
  have hc := congrArg BitVec.msb hs
  simp only [BitVec.msb_ushiftRight, BitVec.msb_sshiftRight, BitVec.msb_shiftLeft] at hb hc
  have ha : a.msb = false := by simpa [show 0 < w-1 by omega] using hb.symm
  have hd : a.getLsbD 0 = false := by
    rw [ha] at hc
    simpa [BitVec.getMsbD_eq_getLsbD, show w-1-(w-1)=0 by omega, show w-1<w by omega] using hc
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [← hu]
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hd]
  by_cases h : i = 0
  · subst i; simp_all
  · simp_all; omega
private theorem both_shl_refines (x : LLVM.Int w) (hw : 1 < w) :
    RuntimeValue.int w (LLVM.Int.shl x (.val (BitVec.ofNat w (w-1))) true true) ⊒ .int w (.val 0) := by
  have hn : (BitVec.ofNat w (w-1)).toNat = w-1 := by
    have := Nat.lt_two_pow_self (n := w)
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  cases x <;> simp [LLVM.Int.shl, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [both_shift_zero]

/-- Both no-wrap flags make shifting by width-1 zero, after earlier shift-zero case. -/
def pattern (n : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty n
      let _ ← MatchProg.root (.llvm .shl) #[x,c] #[ty] (fun p => p.nsw && p.nuw)
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => decide (1 < it.bitwidth) &&
            (BitVec.ofInt it.bitwidth n == BitVec.ofNat it.bitwidth (it.bitwidth-1))
        | _ => false)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem valid (n : Int) : Pattern.Valid (pattern n) := by
  simp only [pattern, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hns hnu hi hz hn
  obtain rfl := matched_bit_constant_eq _ cp n cv hc hz
  obtain rfl := (shl_iff w p x _ v).mp hi
  change (decide (1 < w) && (BitVec.ofInt w n == BitVec.ofNat w (w-1))) = true at hn
  have hnn : 1 < w ∧ BitVec.ofInt w n = BitVec.ofNat w (w-1) := by simpa using hn
  obtain ⟨hw,hk⟩ := hnn
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hns,hnu,hk]
    exact both_shl_refines _ hw
end Veir.InstSimplify.IS1430
