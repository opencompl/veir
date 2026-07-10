import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.Casting
import Veir.ForLean
import Veir.Passes.InstructionSelection.Proofs
import Veir.Passes.InstructionSelection.RISCV64Sdag
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerConst
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSdivExact

/-!
  Correctness of the *general* (non-`exact`) `sdiv x, ±2^k` lowerings, `sdivPow2` (`i64`) and
  `sdivwPow2` (`i32`), both instances of `sdivPow2GenLocal`.

  Unlike `sdiv exact x, 2^k` (see `LowerSdivExact.lean`), which is a bare arithmetic shift, the
  general case must round toward zero: a negative dividend is first biased by `2^k - 1`. The
  emitted sequence is the Hacker's-Delight one that `DAGCombiner::visitSDIVLike` builds,

      sign   = srai  x, w-1        -- all-ones iff x < 0
      corr   = srli  sign, w-k     -- 2^k - 1 iff x < 0, else 0
      biased = add   corr, x
      q      = srai  biased, k

  followed by `neg q` when the divisor is negative. `k = 0` (divisor `±1`) is excluded by the
  pattern: the correction shift `w - k` would need a full register-width immediate, which has no
  legal encoding.

  This file holds the Layer-0 data lemmas. They bridge the pattern's `matchSignedPow2Divisor`
  output (a `Nat` exponent `k` and a sign flag) and the emitted immediates (`BitVec.ofInt 6`/`5`
  of `w-1`, `w-k`, `k`) to the `Data.RISCV.sdivPow2*_refinement` lemmas in
  `InstructionSelection/Proofs.lean`, which are stated with a `BitVec` shift amount.
-/

namespace Veir

/-! ### Immediate-encoding bridges -/

/-- The correction shift `w - k`, as emitted, agrees with the `BitVec` subtraction the refinement
    lemmas use: both reduce to `w - k` modulo `2^6`. -/
theorem ofInt_6_sub (k : Nat) (hk : k ≤ 63) :
    BitVec.ofInt 6 (((64 - k : Nat)) : Int) = 64 - BitVec.ofInt 6 (k : Int) := by
  have hkn : (BitVec.ofInt 6 (k : Int)).toNat = k := by rw [BitVec.toNat_ofInt]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_sub, hkn,
    show (64 : BitVec 6).toNat = 0 from by decide]
  simp only [Nat.reducePow]
  omega

/-- `i32` analogue of `ofInt_6_sub`. -/
theorem ofInt_5_sub (k : Nat) (hk : k ≤ 31) :
    BitVec.ofInt 5 (((32 - k : Nat)) : Int) = 32 - BitVec.ofInt 5 (k : Int) := by
  have hkn : (BitVec.ofInt 5 (k : Int)).toNat = k := by rw [BitVec.toNat_ofInt]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_sub, hkn,
    show (32 : BitVec 5).toNat = 0 from by decide]
  simp only [Nat.reducePow]
  omega

/-! ### Data-level refinement lemmas -/

/-- `i64`, positive divisor: `sdiv x 2^k` (non-`exact`, `k ≠ 0`) refines the bias/shift sequence. -/
theorem sdivPow2_pos_isRefinedBy {x xt : Data.LLVM.Int 64} (c : Int) (k : Nat)
    (hm : matchSignedPow2Divisor 64 c = some (k, false)) (hk0 : k ≠ 0) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant 64 c) false
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.srai (BitVec.ofInt 6 (k : Int))
            (Data.RISCV.add
              (Data.RISCV.srli (BitVec.ofInt 6 (((64 - k : Nat)) : Int))
                (Data.RISCV.srai (BitVec.ofInt 6 ((63 : Nat) : Int)) (LLVM.Int.toReg xt)))
              (LLVM.Int.toReg xt))) 64 := by
  obtain ⟨hnat, hb⟩ := matchSignedPow2Divisor_spec hm
  have hsnn : 0 ≤ (BitVec.ofInt 64 c).toInt := by
    have hd : decide ((BitVec.ofInt 64 c).toInt < 0) = false := hb.symm
    rw [decide_eq_false_iff_not] at hd; omega
  have hub : (BitVec.ofInt 64 c).toInt < 2 ^ 63 := BitVec.toInt_lt
  have hs2k : (BitVec.ofInt 64 c).toInt = ((2 ^ k : Nat) : Int) := by
    rw [← hnat]; exact (Int.natAbs_of_nonneg hsnn).symm
  have hklt : k < 63 := by
    have h2 : (2 : Nat) ^ k < 2 ^ 63 := by have := hub; rw [hs2k] at this; exact_mod_cast this
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp h2
  have hKtoNat : (BitVec.ofInt 6 (k : Int)).toNat = k := by rw [BitVec.toNat_ofInt]; omega
  have hkbv63 : BitVec.ofInt 6 (k : Int) < 63 := by
    rw [BitVec.lt_def, hKtoNat, show (63 : BitVec 6).toNat = 63 from by decide]; omega
  have hkbv0 : 0 < BitVec.ofInt 6 (k : Int) := by
    rw [BitVec.lt_def, hKtoNat, show (0 : BitVec 6).toNat = 0 from by decide]; omega
  have h63 : BitVec.ofInt 6 ((63 : Nat) : Int) = 63 := by decide
  have hdivbv : BitVec.ofInt 64 c = (1#64) <<< (BitVec.ofInt 6 (k : Int)) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.shiftLeft_eq', ← BitVec.twoPow_eq, BitVec.toInt_twoPow, hKtoNat,
      if_neg (by omega), if_neg (by omega), hs2k]; norm_cast
  have hdiv : Data.LLVM.Int.constant 64 c
      = Data.LLVM.Int.val ((1#64) <<< (BitVec.ofInt 6 (k : Int))) := by
    rw [Data.LLVM.Int.constant, hdivbv]
  rw [hdiv, h63, ofInt_6_sub k (by omega)]
  exact isRefinedBy_trans
    (Data.LLVM.Int.sdiv_mono x _ xt _ h (isRefinedBy_refl _) false)
    (Data.RISCV.sdivPow2_pos_refinement (BitVec.ofInt 6 (k : Int)) hkbv0 hkbv63)

/-- `i64`, negative divisor: negate the biased-shift result. -/
theorem sdivPow2_neg_isRefinedBy {x xt : Data.LLVM.Int 64} (c : Int) (k : Nat)
    (hm : matchSignedPow2Divisor 64 c = some (k, true)) (hk0 : k ≠ 0) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant 64 c) false
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.neg
            (Data.RISCV.srai (BitVec.ofInt 6 (k : Int))
              (Data.RISCV.add
                (Data.RISCV.srli (BitVec.ofInt 6 (((64 - k : Nat)) : Int))
                  (Data.RISCV.srai (BitVec.ofInt 6 ((63 : Nat) : Int)) (LLVM.Int.toReg xt)))
                (LLVM.Int.toReg xt)))) 64 := by
  obtain ⟨hnat, hb⟩ := matchSignedPow2Divisor_spec hm
  have hsneg : (BitVec.ofInt 64 c).toInt < 0 := of_decide_eq_true hb.symm
  have hlb : (-(2 ^ 63) : Int) ≤ (BitVec.ofInt 64 c).toInt := BitVec.le_toInt _
  have hs2k : (BitVec.ofInt 64 c).toInt = -((2 ^ k : Nat) : Int) := by
    rcases Int.natAbs_eq (BitVec.ofInt 64 c).toInt with he | he
    · rw [hnat] at he; omega
    · rw [hnat] at he; exact he
  have hk63 : k ≤ 63 := by
    have hInt : ((2 ^ k : Nat) : Int) ≤ (2 ^ 63 : Int) := by omega
    have h2 : (2 : Nat) ^ k ≤ 2 ^ 63 := by exact_mod_cast hInt
    exact (Nat.pow_le_pow_iff_right (by omega)).mp h2
  have hKtoNat : (BitVec.ofInt 6 (k : Int)).toNat = k := by rw [BitVec.toNat_ofInt]; omega
  have hkbv0 : 0 < BitVec.ofInt 6 (k : Int) := by
    rw [BitVec.lt_def, hKtoNat, show (0 : BitVec 6).toNat = 0 from by decide]; omega
  have h63 : BitVec.ofInt 6 ((63 : Nat) : Int) = 63 := by decide
  have hdivbv : BitVec.ofInt 64 c = -((1#64) <<< (BitVec.ofInt 6 (k : Int))) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_neg_one_shl _ (by rw [hKtoNat]; omega), hKtoNat, hs2k]
  have hdiv : Data.LLVM.Int.constant 64 c
      = Data.LLVM.Int.val (-((1#64) <<< (BitVec.ofInt 6 (k : Int)))) := by
    rw [Data.LLVM.Int.constant, hdivbv]
  rw [hdiv, h63, ofInt_6_sub k hk63]
  exact isRefinedBy_trans
    (Data.LLVM.Int.sdiv_mono x _ xt _ h (isRefinedBy_refl _) false)
    (Data.RISCV.sdivPow2_neg_refinement (BitVec.ofInt 6 (k : Int)) hkbv0)

/-- `i32` analogue of `sdivPow2_pos_isRefinedBy` (`sraiw`/`srliw`/`addw`). -/
theorem sdivwPow2_pos_isRefinedBy {x xt : Data.LLVM.Int 32} (c : Int) (k : Nat)
    (hm : matchSignedPow2Divisor 32 c = some (k, false)) (hk0 : k ≠ 0) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant 32 c) false
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.sraiw (BitVec.ofInt 5 (k : Int))
            (Data.RISCV.addw
              (Data.RISCV.srliw (BitVec.ofInt 5 (((32 - k : Nat)) : Int))
                (Data.RISCV.sraiw (BitVec.ofInt 5 ((31 : Nat) : Int)) (LLVM.Int.toReg xt)))
              (LLVM.Int.toReg xt))) 32 := by
  obtain ⟨hnat, hb⟩ := matchSignedPow2Divisor_spec hm
  have hsnn : 0 ≤ (BitVec.ofInt 32 c).toInt := by
    have hd : decide ((BitVec.ofInt 32 c).toInt < 0) = false := hb.symm
    rw [decide_eq_false_iff_not] at hd; omega
  have hub : (BitVec.ofInt 32 c).toInt < 2 ^ 31 := BitVec.toInt_lt
  have hs2k : (BitVec.ofInt 32 c).toInt = ((2 ^ k : Nat) : Int) := by
    rw [← hnat]; exact (Int.natAbs_of_nonneg hsnn).symm
  have hklt : k < 31 := by
    have h2 : (2 : Nat) ^ k < 2 ^ 31 := by have := hub; rw [hs2k] at this; exact_mod_cast this
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp h2
  have hKtoNat : (BitVec.ofInt 5 (k : Int)).toNat = k := by rw [BitVec.toNat_ofInt]; omega
  have hkbv31 : BitVec.ofInt 5 (k : Int) < 31 := by
    rw [BitVec.lt_def, hKtoNat, show (31 : BitVec 5).toNat = 31 from by decide]; omega
  have hkbv0 : 0 < BitVec.ofInt 5 (k : Int) := by
    rw [BitVec.lt_def, hKtoNat, show (0 : BitVec 5).toNat = 0 from by decide]; omega
  have h31 : BitVec.ofInt 5 ((31 : Nat) : Int) = 31 := by decide
  have hdivbv : BitVec.ofInt 32 c = (1#32) <<< (BitVec.ofInt 5 (k : Int)) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.shiftLeft_eq', ← BitVec.twoPow_eq, BitVec.toInt_twoPow, hKtoNat,
      if_neg (by omega), if_neg (by omega), hs2k]; norm_cast
  have hdiv : Data.LLVM.Int.constant 32 c
      = Data.LLVM.Int.val ((1#32) <<< (BitVec.ofInt 5 (k : Int))) := by
    rw [Data.LLVM.Int.constant, hdivbv]
  rw [hdiv, h31, ofInt_5_sub k (by omega)]
  exact isRefinedBy_trans
    (Data.LLVM.Int.sdiv_mono x _ xt _ h (isRefinedBy_refl _) false)
    (Data.RISCV.sdivwPow2_pos_refinement (BitVec.ofInt 5 (k : Int)) hkbv0 hkbv31)

/-- `i32` analogue of `sdivPow2_neg_isRefinedBy` (`negw`). -/
theorem sdivwPow2_neg_isRefinedBy {x xt : Data.LLVM.Int 32} (c : Int) (k : Nat)
    (hm : matchSignedPow2Divisor 32 c = some (k, true)) (hk0 : k ≠ 0) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant 32 c) false
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.negw
            (Data.RISCV.sraiw (BitVec.ofInt 5 (k : Int))
              (Data.RISCV.addw
                (Data.RISCV.srliw (BitVec.ofInt 5 (((32 - k : Nat)) : Int))
                  (Data.RISCV.sraiw (BitVec.ofInt 5 ((31 : Nat) : Int)) (LLVM.Int.toReg xt)))
                (LLVM.Int.toReg xt)))) 32 := by
  obtain ⟨hnat, hb⟩ := matchSignedPow2Divisor_spec hm
  have hsneg : (BitVec.ofInt 32 c).toInt < 0 := of_decide_eq_true hb.symm
  have hlb : (-(2 ^ 31) : Int) ≤ (BitVec.ofInt 32 c).toInt := BitVec.le_toInt _
  have hs2k : (BitVec.ofInt 32 c).toInt = -((2 ^ k : Nat) : Int) := by
    rcases Int.natAbs_eq (BitVec.ofInt 32 c).toInt with he | he
    · rw [hnat] at he; omega
    · rw [hnat] at he; exact he
  have hk31 : k ≤ 31 := by
    have hInt : ((2 ^ k : Nat) : Int) ≤ (2 ^ 31 : Int) := by omega
    have h2 : (2 : Nat) ^ k ≤ 2 ^ 31 := by exact_mod_cast hInt
    exact (Nat.pow_le_pow_iff_right (by omega)).mp h2
  have hKtoNat : (BitVec.ofInt 5 (k : Int)).toNat = k := by rw [BitVec.toNat_ofInt]; omega
  have hkbv0 : 0 < BitVec.ofInt 5 (k : Int) := by
    rw [BitVec.lt_def, hKtoNat, show (0 : BitVec 5).toNat = 0 from by decide]; omega
  have h31 : BitVec.ofInt 5 ((31 : Nat) : Int) = 31 := by decide
  have hdivbv : BitVec.ofInt 32 c = -((1#32) <<< (BitVec.ofInt 5 (k : Int))) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_neg_one_shl _ (by rw [hKtoNat]; omega), hKtoNat, hs2k]
  have hdiv : Data.LLVM.Int.constant 32 c
      = Data.LLVM.Int.val (-((1#32) <<< (BitVec.ofInt 5 (k : Int)))) := by
    rw [Data.LLVM.Int.constant, hdivbv]
  rw [hdiv, h31, ofInt_5_sub k hk31]
  exact isRefinedBy_trans
    (Data.LLVM.Int.sdiv_mono x _ xt _ h (isRefinedBy_refl _) false)
    (Data.RISCV.sdivwPow2_neg_refinement (BitVec.ofInt 5 (k : Int)) hkbv0)

end Veir
