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

  The data lemmas are stated entirely over `BitVec`s, so they read as the
  `Data.RISCV.sdivPow2*_refinement` lemmas of `InstructionSelection/Proofs.lean` lifted from `x` to
  a refined `xt`. The bridges above them turn the pattern's `matchSignedPow2Divisor` output (an
  `Int` constant, a `Nat` exponent, a sign flag) and its `Int` immediates into the `BitVec` divisor
  and shift amount those lemmas take. `sdivPow2GenLocal_preservesSemantics` then lifts everything
  to the graph level once, for both instances.
-/

namespace Veir

/-! ### Immediate-encoding bridges

    The pattern emits `Int` immediates (`(w : Int) - 1`, `(w : Int) - k`, `k`) and gets its exponent
    as a `Nat` from `matchSignedPow2Divisor`; the refinement lemmas speak of `BitVec` shift amounts
    and a `BitVec` divisor. These lemmas translate. -/

/-- The exponent a successful `matchSignedPow2Divisor` reports is below the width: the divisor's
    `w`-bit signed magnitude is `2^k`, and that is bounded by `2^(w-1)`. -/
theorem matchSignedPow2Divisor_exponent_lt {w : Nat} {c : Int} {k : Nat} {b : Bool} (hw : 0 < w)
    (h : matchSignedPow2Divisor w c = some (k, b)) : k < w := by
  obtain ⟨hnat, -⟩ := matchSignedPow2Divisor_spec h
  have hpow : ((2 ^ (w - 1) : Nat) : Int) = 2 ^ (w - 1) := by push_cast; rfl
  have hub : (BitVec.ofInt w c).toInt < ((2 ^ (w - 1) : Nat) : Int) := by
    rw [hpow]; exact BitVec.toInt_lt
  have hlb : -((2 ^ (w - 1) : Nat) : Int) ≤ (BitVec.ofInt w c).toInt := by
    rw [hpow]; exact BitVec.le_toInt _
  have hle : (2 : Nat) ^ k ≤ 2 ^ (w - 1) := by omega
  have := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle
  omega

/-- The `Nat` exponent survives its `BitVec 6` encoding. -/
theorem bv6_toNat {c : Int} {k : Nat} {b : Bool}
    (hm : matchSignedPow2Divisor 64 c = some (k, b)) : (BitVec.ofInt 6 (k : Int)).toNat = k := by
  have hkl : k < 64 := matchSignedPow2Divisor_exponent_lt (by omega) hm
  rw [BitVec.toNat_ofInt]; omega

/-- `i32` analogue of `bv6_toNat`. -/
theorem bv5_toNat {c : Int} {k : Nat} {b : Bool}
    (hm : matchSignedPow2Divisor 32 c = some (k, b)) : (BitVec.ofInt 5 (k : Int)).toNat = k := by
  have hkl : k < 32 := matchSignedPow2Divisor_exponent_lt (by omega) hm
  rw [BitVec.toNat_ofInt]; omega

/-- The correction shift `w - k` is emitted as an `Int` subtraction (immediates are `Int`); it
    agrees with the `BitVec` subtraction the refinement lemmas use, both reducing to `w - k`
    modulo `2^6`. -/
theorem ofInt_6_sub (k : Nat) (hk : k ≤ 63) :
    BitVec.ofInt 6 (((64 : Nat) : Int) - (k : Int)) = 64 - BitVec.ofInt 6 (k : Int) := by
  rw [show (((64 : Nat) : Int) - (k : Int)) = ((64 - k : Nat) : Int) from by omega]
  have hkn : (BitVec.ofInt 6 (k : Int)).toNat = k := by rw [BitVec.toNat_ofInt]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_sub, hkn,
    show (64 : BitVec 6).toNat = 0 from by decide]
  simp only [Nat.reducePow]
  omega

/-- `i32` analogue of `ofInt_6_sub`. -/
theorem ofInt_5_sub (k : Nat) (hk : k ≤ 31) :
    BitVec.ofInt 5 (((32 : Nat) : Int) - (k : Int)) = 32 - BitVec.ofInt 5 (k : Int) := by
  rw [show (((32 : Nat) : Int) - (k : Int)) = ((32 - k : Nat) : Int) from by omega]
  have hkn : (BitVec.ofInt 5 (k : Int)).toNat = k := by rw [BitVec.toNat_ofInt]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_sub, hkn,
    show (32 : BitVec 5).toNat = 0 from by decide]
  simp only [Nat.reducePow]
  omega

/-- A successful `matchSignedPow2Divisor 64 c` with a nonnegative sign flag pins the divisor's
    64-bit encoding to `1 <<< k` and its exponent to a nonzero, in-range shift amount. -/
theorem matchSignedPow2Divisor_pos_64 {c : Int} {k : Nat}
    (hm : matchSignedPow2Divisor 64 c = some (k, false)) (hk0 : k ≠ 0) :
    BitVec.ofInt 64 c = 1#64 <<< BitVec.ofInt 6 (k : Int)
      ∧ 0 < BitVec.ofInt 6 (k : Int) ∧ BitVec.ofInt 6 (k : Int) < 63 := by
  obtain ⟨hnat, hb⟩ := matchSignedPow2Divisor_spec hm
  have hKtoNat := bv6_toNat hm
  have hsnn : 0 ≤ (BitVec.ofInt 64 c).toInt := by
    have hd : decide ((BitVec.ofInt 64 c).toInt < 0) = false := hb.symm
    rw [decide_eq_false_iff_not] at hd; omega
  have hub : (BitVec.ofInt 64 c).toInt < 2 ^ 63 := BitVec.toInt_lt
  have hs2k : (BitVec.ofInt 64 c).toInt = ((2 ^ k : Nat) : Int) := by
    rw [← hnat]; exact (Int.natAbs_of_nonneg hsnn).symm
  have hklt : k < 63 := by
    have h2 : (2 : Nat) ^ k < 2 ^ 63 := by have := hub; rw [hs2k] at this; exact_mod_cast this
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp h2
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.shiftLeft_eq', ← BitVec.twoPow_eq, BitVec.toInt_twoPow, hKtoNat,
      if_neg (by omega), if_neg (by omega), hs2k]; norm_cast
  · rw [BitVec.lt_def, hKtoNat, show (0 : BitVec 6).toNat = 0 from by decide]; omega
  · rw [BitVec.lt_def, hKtoNat, show (63 : BitVec 6).toNat = 63 from by decide]; omega

/-- Negative-divisor analogue of `matchSignedPow2Divisor_pos_64`. -/
theorem matchSignedPow2Divisor_neg_64 {c : Int} {k : Nat}
    (hm : matchSignedPow2Divisor 64 c = some (k, true)) (hk0 : k ≠ 0) :
    BitVec.ofInt 64 c = -(1#64 <<< BitVec.ofInt 6 (k : Int)) ∧ 0 < BitVec.ofInt 6 (k : Int) := by
  obtain ⟨hnat, hb⟩ := matchSignedPow2Divisor_spec hm
  have hKtoNat := bv6_toNat hm
  have hkl : k < 64 := matchSignedPow2Divisor_exponent_lt (by omega) hm
  have hsneg : (BitVec.ofInt 64 c).toInt < 0 := of_decide_eq_true hb.symm
  have hs2k : (BitVec.ofInt 64 c).toInt = -((2 ^ k : Nat) : Int) := by
    rcases Int.natAbs_eq (BitVec.ofInt 64 c).toInt with he | he
    · rw [hnat] at he; omega
    · rw [hnat] at he; exact he
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_neg_one_shl _ (by rw [hKtoNat]; omega), hKtoNat, hs2k]
  · rw [BitVec.lt_def, hKtoNat, show (0 : BitVec 6).toNat = 0 from by decide]; omega

/-- `i32` analogue of `matchSignedPow2Divisor_pos_64`. -/
theorem matchSignedPow2Divisor_pos_32 {c : Int} {k : Nat}
    (hm : matchSignedPow2Divisor 32 c = some (k, false)) (hk0 : k ≠ 0) :
    BitVec.ofInt 32 c = 1#32 <<< BitVec.ofInt 5 (k : Int)
      ∧ 0 < BitVec.ofInt 5 (k : Int) ∧ BitVec.ofInt 5 (k : Int) < 31 := by
  obtain ⟨hnat, hb⟩ := matchSignedPow2Divisor_spec hm
  have hKtoNat := bv5_toNat hm
  have hsnn : 0 ≤ (BitVec.ofInt 32 c).toInt := by
    have hd : decide ((BitVec.ofInt 32 c).toInt < 0) = false := hb.symm
    rw [decide_eq_false_iff_not] at hd; omega
  have hub : (BitVec.ofInt 32 c).toInt < 2 ^ 31 := BitVec.toInt_lt
  have hs2k : (BitVec.ofInt 32 c).toInt = ((2 ^ k : Nat) : Int) := by
    rw [← hnat]; exact (Int.natAbs_of_nonneg hsnn).symm
  have hklt : k < 31 := by
    have h2 : (2 : Nat) ^ k < 2 ^ 31 := by have := hub; rw [hs2k] at this; exact_mod_cast this
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp h2
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.shiftLeft_eq', ← BitVec.twoPow_eq, BitVec.toInt_twoPow, hKtoNat,
      if_neg (by omega), if_neg (by omega), hs2k]; norm_cast
  · rw [BitVec.lt_def, hKtoNat, show (0 : BitVec 5).toNat = 0 from by decide]; omega
  · rw [BitVec.lt_def, hKtoNat, show (31 : BitVec 5).toNat = 31 from by decide]; omega

/-- `i32` analogue of `matchSignedPow2Divisor_neg_64`. -/
theorem matchSignedPow2Divisor_neg_32 {c : Int} {k : Nat}
    (hm : matchSignedPow2Divisor 32 c = some (k, true)) (hk0 : k ≠ 0) :
    BitVec.ofInt 32 c = -(1#32 <<< BitVec.ofInt 5 (k : Int)) ∧ 0 < BitVec.ofInt 5 (k : Int) := by
  obtain ⟨hnat, hb⟩ := matchSignedPow2Divisor_spec hm
  have hKtoNat := bv5_toNat hm
  have hkl : k < 32 := matchSignedPow2Divisor_exponent_lt (by omega) hm
  have hsneg : (BitVec.ofInt 32 c).toInt < 0 := of_decide_eq_true hb.symm
  have hs2k : (BitVec.ofInt 32 c).toInt = -((2 ^ k : Nat) : Int) := by
    rcases Int.natAbs_eq (BitVec.ofInt 32 c).toInt with he | he
    · rw [hnat] at he; omega
    · rw [hnat] at he; exact he
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_neg_one_shl _ (by rw [hKtoNat]; omega), hKtoNat, hs2k]
  · rw [BitVec.lt_def, hKtoNat, show (0 : BitVec 5).toNat = 0 from by decide]; omega

/-! ### Data-level refinement lemmas

    Purely bitvector-level: the divisor and the shift amount are `BitVec`s, so these are exactly
    `Data.RISCV.sdivPow2*_refinement` lifted from `x` to a refined `xt`. The bridges above turn the
    matcher's `Int` constant and `Nat` exponent into the hypotheses they need. -/

/-- `i64`, positive divisor: `sdiv x 2^k` (non-`exact`, `0 < k < 63`) refines the bias/shift
    sequence. -/
theorem sdivPow2_pos_isRefinedBy {x xt : Data.LLVM.Int 64} (c : BitVec 64) (k : BitVec 6)
    (hc : c = 1#64 <<< k) (hk0 : 0 < k) (hk63 : k < 63) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.val c) false
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.srai k
            (Data.RISCV.add
              (Data.RISCV.srli (64 - k) (Data.RISCV.srai 63 (LLVM.Int.toReg xt)))
              (LLVM.Int.toReg xt))) 64 := by
  revert h hc
  veir_bv_decide

/-- `i64`, negative divisor: negate the biased-shift result. -/
theorem sdivPow2_neg_isRefinedBy {x xt : Data.LLVM.Int 64} (c : BitVec 64) (k : BitVec 6)
    (hc : c = -(1#64 <<< k)) (hk0 : 0 < k) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.val c) false
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.neg
            (Data.RISCV.srai k
              (Data.RISCV.add
                (Data.RISCV.srli (64 - k) (Data.RISCV.srai 63 (LLVM.Int.toReg xt)))
                (LLVM.Int.toReg xt)))) 64 := by
  revert h hc
  veir_bv_decide

/-- `i32` analogue of `sdivPow2_pos_isRefinedBy` (`sraiw`/`srliw`/`addw`). -/
theorem sdivwPow2_pos_isRefinedBy {x xt : Data.LLVM.Int 32} (c : BitVec 32) (k : BitVec 5)
    (hc : c = 1#32 <<< k) (hk0 : 0 < k) (hk31 : k < 31) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.val c) false
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.sraiw k
            (Data.RISCV.addw
              (Data.RISCV.srliw (32 - k) (Data.RISCV.sraiw 31 (LLVM.Int.toReg xt)))
              (LLVM.Int.toReg xt))) 32 := by
  revert h hc
  veir_bv_decide

/-- `i32` analogue of `sdivPow2_neg_isRefinedBy` (`negw`). -/
theorem sdivwPow2_neg_isRefinedBy {x xt : Data.LLVM.Int 32} (c : BitVec 32) (k : BitVec 5)
    (hc : c = -(1#32 <<< k)) (hk0 : 0 < k) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.val c) false
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.negw
            (Data.RISCV.sraiw k
              (Data.RISCV.addw
                (Data.RISCV.srliw (32 - k) (Data.RISCV.sraiw 31 (LLVM.Int.toReg xt)))
                (LLVM.Int.toReg xt)))) 32 := by
  revert h hc hk0
  veir_bv_decide

/-! ### Shared correctness of `sdivPow2GenLocal` -/

/-- A distinct operation's result is never among `b`'s results. Used to carry an already-computed
    register value forward across the interpretation of a later freshly created op. -/
private theorem opResult_not_mem_getResults! {ctx : IRContext OpCode} {a b : OperationPtr} {i : Nat}
    (hne : a ≠ b) : (ValuePtr.opResult (a.getResult i)) ∉ b.getResults! ctx := by
  rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx
      (ValuePtr.opResult (a.getResult i)) b with hres | ⟨j, hj, heq⟩
  · exact hres
  · exact absurd heq (by grind [OperationPtr.getResult])

/-! Field transports across a `createOp`, phrased so that a chain of them can be discharged by `rw`.

This pattern emits six (positive divisor) or eight (negative divisor) operations, and the source
`hpattern` — which `PreservesSemantics` bakes into the *types* of `state'Wf`/`state'Dom`/
`valueRefinement`, so it can never be cleared — is correspondingly large. `grind` chokes on it once
the creation chain gets this long, so every field transport below is done by explicit rewriting
instead of the `grind [getX!_WfRewriter_createOp …]` idiom used by the shorter lowerings. -/

private theorem getOpType!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getOpType! ctx'.raw = opType := by
  rw [OperationPtr.getOpType!_WfRewriter_createOp h, if_pos rfl]

private theorem getOpType!_createOp_ne {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    o.getOpType! ctx'.raw = o.getOpType! ctx.raw := by
  rw [OperationPtr.getOpType!_WfRewriter_createOp h, if_neg hne]

private theorem getOperands!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getOperands! ctx'.raw = operands := by
  rw [OperationPtr.getOperands!_WfRewriter_createOp h, if_pos rfl]

private theorem getOperands!_createOp_ne {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    o.getOperands! ctx'.raw = o.getOperands! ctx.raw := by
  rw [OperationPtr.getOperands!_WfRewriter_createOp h, if_neg hne]

private theorem getResultTypes!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getResultTypes! ctx'.raw = resultTypes := by
  rw [OperationPtr.getResultTypes!_WfRewriter_createOp h, if_pos rfl]

private theorem getResultTypes!_createOp_ne {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    o.getResultTypes! ctx'.raw = o.getResultTypes! ctx.raw := by
  rw [OperationPtr.getResultTypes!_WfRewriter_createOp h, if_neg hne]

private theorem getProperties!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getProperties! ctx'.raw opType = properties := by
  rw [OperationPtr.getProperties!_WfRewriter_createOp h, if_pos rfl]

private theorem getType!_opResult_createOp_ne {ctx ctx' : WfIRContext OpCode}
    {o newOp : OperationPtr} {i : Nat}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    (ValuePtr.opResult (o.getResult i)).getType! ctx'.raw
      = (ValuePtr.opResult (o.getResult i)).getType! ctx.raw := by
  rw [ValuePtr.getType!_WfRewriter_createOp h]
  exact dif_neg (by rintro ⟨hc, -⟩; exact hne hc)

/-- A pre-existing operation is distinct from one `createOp` freshly allocates. -/
private theorem ne_createOp_new {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hIn : o.InBounds ctx.raw) :
    o ≠ newOp :=
  fun he => WfRewriter.createOp_new_not_inBounds newOp h (he ▸ hIn)

set_option maxHeartbeats 1000000 in
theorem sdivPow2GenLocal_preservesSemantics
    {shiftDst : Riscv} {hShift : Riscv.propertiesOf shiftDst = RISCVImmediateProperties}
    {corrDst : Riscv} {hCorr : Riscv.propertiesOf corrDst = RISCVImmediateProperties}
    {addDst : Riscv} {hAdd : Riscv.propertiesOf addDst = Unit}
    {negDst : Riscv} {hNeg : Riscv.propertiesOf negDst = Unit} {width : Nat}
    {sraFn srlFn : Int → Data.RISCV.Reg → Data.RISCV.Reg}
    {addFn subFn : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    (hSemSra : ∀ (i : Int) (r : Data.RISCV.Reg)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' shiftDst
            (cast hShift.symm (RISCVImmediateProperties.mk (IntegerAttr.mk i (IntegerType.mk 64))))
            resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (sraFn i r)], mem, none)))
    (hSemSrl : ∀ (i : Int) (r : Data.RISCV.Reg)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' corrDst
            (cast hCorr.symm (RISCVImmediateProperties.mk (IntegerAttr.mk i (IntegerType.mk 64))))
            resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (srlFn i r)], mem, none)))
    (hSemAdd : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : Riscv.propertiesOf addDst)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' addDst props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (addFn r₁ r₂)], mem, none)))
    (hSemSub : ∀ (z r : Data.RISCV.Reg) (props : Riscv.propertiesOf negDst)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' negDst props resultTypes #[.reg z, .reg r] blockOperands mem
          = some (.ok (#[.reg (subFn z r)], mem, none)))
    (hRefinePos : ∀ (x xt : Data.LLVM.Int width) (c : Int) (k : Nat),
        matchSignedPow2Divisor width c = some (k, false) → k ≠ 0 → x ⊒ xt →
        Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant width c) false
          ⊒ RISCV.Reg.toInt
              (sraFn (k : Int)
                (addFn (LLVM.Int.toReg xt)
                  (srlFn ((width : Int) - (k : Int))
                    (sraFn ((width : Int) - 1) (LLVM.Int.toReg xt))))) width)
    (hRefineNeg : ∀ (x xt : Data.LLVM.Int width) (c : Int) (k : Nat),
        matchSignedPow2Divisor width c = some (k, true) → k ≠ 0 → x ⊒ xt →
        Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant width c) false
          ⊒ RISCV.Reg.toInt
              (subFn (Data.RISCV.li (BitVec.ofInt 64 0))
                (sraFn (k : Int)
                  (addFn (LLVM.Int.toReg xt)
                    (srlFn ((width : Int) - (k : Int))
                      (sraFn ((width : Int) - 1) (LLVM.Int.toReg xt)))))) width)
    {h : LocalRewritePattern.ReturnOps
      (sdivPow2GenLocal shiftDst hShift corrDst hCorr addDst hAdd negDst hNeg width)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges
      (sdivPow2GenLocal shiftDst hShift corrDst hCorr addDst hAdd negDst hNeg width)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (sdivPow2GenLocal shiftDst hShift corrDst hCorr addDst hAdd negDst hNeg width)}
    {h₄ : LocalRewritePattern.ReturnValues
      (sdivPow2GenLocal shiftDst hShift corrDst hCorr addDst hAdd negDst hNeg width)} :
    LocalRewritePattern.PreservesSemantics
      (sdivPow2GenLocal shiftDst hShift corrDst hCorr addDst hAdd negDst hNeg width) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, sdivPow2GenLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  have hMatchSome : (matchSdiv op ctx.raw).isSome := by
    cases hM : matchSdiv op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchSdiv_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_sdiv opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  have isT : Attribute.isType (Attribute.integerType intType) :=
    hResTypeVal ▸ (((op.getResult 0).get! ctx.raw).type).2
  -- Peel the `exact` guard: this pattern is the *non*-`exact` one, so it survives on `exact = false`.
  peelSplittableCondition [hExact] hpattern
  have hExactFalse : props.exact = false := by
    cases hb : props.exact
    · rfl
    · exact absurd hb hExact
  -- Resolve the `.integerType t` match on the result type, then the bitwidth guard.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  peelSplittableCondition' [hBw] hpattern
  -- Peel the constant match, the power-of-two divisor match, and the `k ≠ 0` guard.
  have hCVSome : (matchConstantIntVal rhs ctx.raw).isSome := by
    cases hCV : matchConstantIntVal rhs ctx.raw with
    | some y => rfl
    | none => rw [hCV] at hpattern; simp at hpattern
  obtain ⟨imm, hCV⟩ := Option.isSome_iff_exists.mp hCVSome
  rw [hCV] at hpattern
  simp only [] at hpattern
  have hKSome : (matchSignedPow2Divisor width imm.value).isSome := by
    cases hK : matchSignedPow2Divisor width imm.value with
    | some y => rfl
    | none => rw [hK] at hpattern; simp at hpattern
  obtain ⟨⟨k, isNeg⟩, hK⟩ := Option.isSome_iff_exists.mp hKSome
  rw [hK] at hpattern
  simp only [] at hpattern
  peelSplittableCondition [hK0] hpattern
  -- Unfold the source `sdiv` interpretation (UB-aware, as in `sdivPow2Exact`).
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sdiv)
      (srcFn := fun x y props => Data.LLVM.Int.sdiv x y props.exact)
      opInBounds hOpType hNumResults hOperands hProps
      (fun _ _ _ _ _ _ _ _ hh => by
        simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self] at hh
        repeat' split at hh
        all_goals first
          | (simp only [pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hh; exact hh.symm)
          | nomatch hh)
      hinterp hLhsType hRhsType
  subst hCf
  have hyConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf
    hCV (by rw [hOperands]; simp) hRhsType
  obtain rfl : yVal = Data.LLVM.Int.constant intType.bitwidth imm.value := by
    have h := hyVal.symm.trans hyConst; simpa using h
  have hDomCtxLhs : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have lhsNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have lhsIn : lhs.InBounds ctx.raw := by grind
  -- Peel the five shared creations; the rest branches on the divisor's sign.
  peelCastToRegLocal hpattern ctx₁ castOp hCast hDomCtxLhs hDom₁
  peelOpCreation! hpattern ctx₂ signOp hSign hDom₁ hDom₂
  peelOpCreation! hpattern ctx₃ corrOp hCorrOp hDom₂ hDom₃
  peelOpCreation! hpattern ctx₄ biasedOp hBiased hDom₃ hDom₄
  peelOpCreation! hpattern ctx₅ qOp hQ hDom₄ hDom₅
  cases isNeg with
  | false =>
    -- Positive divisor: `castToReg → srai → srli → add → srai → castBack` (6 ops).
    simp only [reduceIte] at hpattern
    peelReplaceWithRegLocal hpattern ctx₆ castBackOp hCastBack hDom₅ hDom₆
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom lhsIn hxVal
        hDomCtxLhs hDom₆ lhsNotOp
    obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
    -- In-bounds facts for every created op in every later context.
    have hCastIn₁ : castOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds castOp hCast
    have hCastIn₂ : castOp.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hSign hCastIn₁
    have hCastIn₃ : castOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hCorrOp hCastIn₂
    have hCastIn₄ : castOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hBiased hCastIn₃
    have hCastIn₅ : castOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hQ hCastIn₄
    have hCastIn₆ : castOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hCastBack hCastIn₅
    have hSignIn₂ : signOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds signOp hSign
    have hSignIn₃ : signOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hCorrOp hSignIn₂
    have hSignIn₄ : signOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hBiased hSignIn₃
    have hSignIn₅ : signOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hQ hSignIn₄
    have hSignIn₆ : signOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hCastBack hSignIn₅
    have hCorrIn₃ : corrOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds corrOp hCorrOp
    have hCorrIn₄ : corrOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation corrOp) hBiased hCorrIn₃
    have hCorrIn₅ : corrOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation corrOp) hQ hCorrIn₄
    have hCorrIn₆ : corrOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation corrOp) hCastBack hCorrIn₅
    have hBiasedIn₄ : biasedOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_new_inBounds biasedOp hBiased
    have hBiasedIn₅ : biasedOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation biasedOp) hQ hBiasedIn₄
    have hBiasedIn₆ : biasedOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation biasedOp) hCastBack hBiasedIn₅
    have hQIn₅ : qOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds qOp hQ
    have hQIn₆ : qOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation qOp) hCastBack hQIn₅
    have hCastBackIn₆ : castBackOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_new_inBounds castBackOp hCastBack
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hCast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSign hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hCorrOp hOpIn₂
    have hOpIn₄ : op.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hBiased hOpIn₃
    -- Every created op is distinct from the ones created before it.
    have neCS : castOp ≠ signOp := ne_createOp_new hSign hCastIn₁
    have neCR : castOp ≠ corrOp := ne_createOp_new hCorrOp hCastIn₂
    have neCB : castOp ≠ biasedOp := ne_createOp_new hBiased hCastIn₃
    have neCQ : castOp ≠ qOp := ne_createOp_new hQ hCastIn₄
    have neCK : castOp ≠ castBackOp := ne_createOp_new hCastBack hCastIn₅
    have neSR : signOp ≠ corrOp := ne_createOp_new hCorrOp hSignIn₂
    have neSB : signOp ≠ biasedOp := ne_createOp_new hBiased hSignIn₃
    have neSQ : signOp ≠ qOp := ne_createOp_new hQ hSignIn₄
    have neSK : signOp ≠ castBackOp := ne_createOp_new hCastBack hSignIn₅
    have neRB : corrOp ≠ biasedOp := ne_createOp_new hBiased hCorrIn₃
    have neRQ : corrOp ≠ qOp := ne_createOp_new hQ hCorrIn₄
    have neRK : corrOp ≠ castBackOp := ne_createOp_new hCastBack hCorrIn₅
    have neBQ : biasedOp ≠ qOp := ne_createOp_new hQ hBiasedIn₄
    have neBK : biasedOp ≠ castBackOp := ne_createOp_new hCastBack hBiasedIn₅
    have neQK : qOp ≠ castBackOp := ne_createOp_new hCastBack hQIn₅
    have neOpC : op ≠ castOp := ne_createOp_new hCast opInBounds
    have neOpS : op ≠ signOp := ne_createOp_new hSign hOpIn₁
    have neOpR : op ≠ corrOp := ne_createOp_new hCorrOp hOpIn₂
    have neOpB : op ≠ biasedOp := ne_createOp_new hBiased hOpIn₃
    have neOpQ : op ≠ qOp := ne_createOp_new hQ hOpIn₄
    -- Transport each op's fields from its creation context to `ctx₆`.
    have hCastType : castOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
      rw [getOpType!_createOp_ne hCastBack neCK, getOpType!_createOp_ne hQ neCQ,
        getOpType!_createOp_ne hBiased neCB, getOpType!_createOp_ne hCorrOp neCR,
        getOpType!_createOp_ne hSign neCS, getOpType!_createOp_self hCast]
    have hSignType : signOp.getOpType! ctx₆.raw = .riscv shiftDst := by
      rw [getOpType!_createOp_ne hCastBack neSK, getOpType!_createOp_ne hQ neSQ,
        getOpType!_createOp_ne hBiased neSB, getOpType!_createOp_ne hCorrOp neSR,
        getOpType!_createOp_self hSign]
    have hCorrType : corrOp.getOpType! ctx₆.raw = .riscv corrDst := by
      rw [getOpType!_createOp_ne hCastBack neRK, getOpType!_createOp_ne hQ neRQ,
        getOpType!_createOp_ne hBiased neRB, getOpType!_createOp_self hCorrOp]
    have hBiasedType : biasedOp.getOpType! ctx₆.raw = .riscv addDst := by
      rw [getOpType!_createOp_ne hCastBack neBK, getOpType!_createOp_ne hQ neBQ,
        getOpType!_createOp_self hBiased]
    have hQType : qOp.getOpType! ctx₆.raw = .riscv shiftDst := by
      rw [getOpType!_createOp_ne hCastBack neQK, getOpType!_createOp_self hQ]
    have hCastBackType : castBackOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
      rw [getOpType!_createOp_self hCastBack]
    have hCastOperands : castOp.getOperands! ctx₆.raw = #[lhs] := by
      rw [getOperands!_createOp_ne hCastBack neCK, getOperands!_createOp_ne hQ neCQ,
        getOperands!_createOp_ne hBiased neCB, getOperands!_createOp_ne hCorrOp neCR,
        getOperands!_createOp_ne hSign neCS, getOperands!_createOp_self hCast]
    have hSignOperands :
        signOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      rw [getOperands!_createOp_ne hCastBack neSK, getOperands!_createOp_ne hQ neSQ,
        getOperands!_createOp_ne hBiased neSB, getOperands!_createOp_ne hCorrOp neSR,
        getOperands!_createOp_self hSign]
    have hCorrOperands :
        corrOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (signOp.getResult 0)] := by
      rw [getOperands!_createOp_ne hCastBack neRK, getOperands!_createOp_ne hQ neRQ,
        getOperands!_createOp_ne hBiased neRB, getOperands!_createOp_self hCorrOp]
    have hBiasedOperands :
        biasedOp.getOperands! ctx₆.raw
          = #[ValuePtr.opResult (castOp.getResult 0), ValuePtr.opResult (corrOp.getResult 0)] := by
      rw [getOperands!_createOp_ne hCastBack neBK, getOperands!_createOp_ne hQ neBQ,
        getOperands!_createOp_self hBiased]
    have hQOperands :
        qOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (biasedOp.getResult 0)] := by
      rw [getOperands!_createOp_ne hCastBack neQK, getOperands!_createOp_self hQ]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (qOp.getResult 0)] := by
      rw [getOperands!_createOp_self hCastBack]
    have hSignProps : signOp.getProperties! ctx₆.raw (.riscv shiftDst)
        = cast hShift.symm
            (RISCVImmediateProperties.mk (IntegerAttr.mk ((bw : Int) - 1) (IntegerType.mk 64))) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack neSK,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hQ neSQ,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hBiased neSB,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hCorrOp neSR,
        getProperties!_createOp_self hSign]
      rfl
    have hCorrProps : corrOp.getProperties! ctx₆.raw (.riscv corrDst)
        = cast hCorr.symm
            (RISCVImmediateProperties.mk
              (IntegerAttr.mk ((bw : Int) - (k : Int)) (IntegerType.mk 64))) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack neRK,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hQ neRQ,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hBiased neRB,
        getProperties!_createOp_self hCorrOp]
      rfl
    have hQProps : qOp.getProperties! ctx₆.raw (.riscv shiftDst)
        = cast hShift.symm
            (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64))) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack neQK,
        getProperties!_createOp_self hQ]
      rfl
    have hCBType : ((op.getResult 0).get! ctx₅.raw).type
        = (⟨Attribute.integerType { bitwidth := bw }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₅.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        rw [getType!_opResult_createOp_ne hQ neOpQ, getType!_opResult_createOp_ne hBiased neOpB,
          getType!_opResult_createOp_ne hCorrOp neOpR, getType!_opResult_createOp_ne hSign neOpS,
          getType!_opResult_createOp_ne hCast neOpC]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neCK, getResultTypes!_createOp_ne hQ neCQ,
        getResultTypes!_createOp_ne hBiased neCB, getResultTypes!_createOp_ne hCorrOp neCR,
        getResultTypes!_createOp_ne hSign neCS, getResultTypes!_createOp_self hCast]
    have hSignResTypes : signOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neSK, getResultTypes!_createOp_ne hQ neSQ,
        getResultTypes!_createOp_ne hBiased neSB, getResultTypes!_createOp_ne hCorrOp neSR,
        getResultTypes!_createOp_self hSign]
    have hCorrResTypes : corrOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neRK, getResultTypes!_createOp_ne hQ neRQ,
        getResultTypes!_createOp_ne hBiased neRB, getResultTypes!_createOp_self hCorrOp]
    have hBiasedResTypes : biasedOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neBK, getResultTypes!_createOp_ne hQ neBQ,
        getResultTypes!_createOp_self hBiased]
    have hQResTypes : qOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neQK, getResultTypes!_createOp_self hQ]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.integerType { bitwidth := bw }, isT⟩] := by
      rw [getResultTypes!_createOp_self hCastBack, hCBType]
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := hCastIn₆)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hOther₂⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := hSignIn₆)
        (res := sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt))
        (props := cast hShift.symm
          (RISCVImmediateProperties.mk (IntegerAttr.mk ((bw : Int) - 1) (IntegerType.mk 64))))
        (hSemSra ((bw : Int) - 1) (LLVM.Int.toReg xt))
        hSignType hSignProps hSignOperands hSignResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hOther₃⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₂) (inBounds := hCorrIn₆)
        (res := srlFn ((bw : Int) - (k : Int)) (sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt)))
        (props := cast hCorr.symm
          (RISCVImmediateProperties.mk
            (IntegerAttr.mk ((bw : Int) - (k : Int)) (IntegerType.mk 64))))
        (hSemSrl ((bw : Int) - (k : Int)) (sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt)))
        hCorrType hCorrProps hCorrOperands hCorrResTypes hRes₂
    -- Carry the cast result forward across the `sign`/`corr` steps (each touches only its result).
    have hCastRes₃ : s₃.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hOther₃ _ (opResult_not_mem_getResults! neCR),
        hOther₂ _ (opResult_not_mem_getResults! neCS)]
      exact hRes₁
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := hBiasedIn₆)
        (f := addFn) (hSemAdd _ _) hBiasedType hBiasedOperands hBiasedResTypes hCastRes₃ hRes₃
    obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₄) (inBounds := hQIn₆)
        (res := sraFn (k : Int)
          (addFn (LLVM.Int.toReg xt)
            (srlFn ((bw : Int) - (k : Int)) (sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt)))))
        (props := cast hShift.symm
          (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64))))
        (hSemSra (k : Int) _)
        hQType hQProps hQOperands hQResTypes hRes₄
    obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
      interpretOp_castBack_forward (state := s₅) (inBounds := hCastBackIn₆)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₅
    refine ⟨s₆, ?_, ?_, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, liftM, monadLift,
        MonadLift.monadLift, Interp]
    · rw [hMem₆, hMem₅, hMem₄, hMem₃, hMem₂, hMem₁, ← memoryRefinement]; exact hMem.symm
    · refine ⟨#[RuntimeValue.int bw
          (RISCV.Reg.toInt
            (sraFn (k : Int)
              (addFn (LLVM.Int.toReg xt)
                (srlFn ((bw : Int) - (k : Int))
                  (sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt))))) bw)], ?_, ?_⟩
      · simp [hRes₆, Option.bind, Option.map]
      · rw [hExactFalse]
        exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefinePos xVal xt imm.value k hK hK0 hxtRef⟩
  | true =>
    -- Negative divisor: the same five ops, then `li 0`, `sub 0 q`, `castBack` (8 ops).
    rw [if_neg (by decide)] at hpattern
    simp only [negateRegLocal, bind, Option.bind_assoc] at hpattern
    peelOpCreation! hpattern ctx₆ zeroOp hZero hDom₅ hDom₆
    peelOpCreation! hpattern ctx₇ negOp hNegOp hDom₆ hDom₇
    simp only [Option.some.injEq, exists_eq_left'] at hpattern
    peelReplaceWithRegLocal hpattern ctx₈ castBackOp hCastBack hDom₇ hDom₈
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom lhsIn hxVal
        hDomCtxLhs hDom₈ lhsNotOp
    obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
    -- In-bounds facts for every created op in every later context.
    have hCastIn₁ : castOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds castOp hCast
    have hCastIn₂ : castOp.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hSign hCastIn₁
    have hCastIn₃ : castOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hCorrOp hCastIn₂
    have hCastIn₄ : castOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hBiased hCastIn₃
    have hCastIn₅ : castOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hQ hCastIn₄
    have hCastIn₆ : castOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hZero hCastIn₅
    have hCastIn₇ : castOp.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hNegOp hCastIn₆
    have hCastIn₈ : castOp.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation castOp) hCastBack hCastIn₇
    have hSignIn₂ : signOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds signOp hSign
    have hSignIn₃ : signOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hCorrOp hSignIn₂
    have hSignIn₄ : signOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hBiased hSignIn₃
    have hSignIn₅ : signOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hQ hSignIn₄
    have hSignIn₆ : signOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hZero hSignIn₅
    have hSignIn₇ : signOp.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hNegOp hSignIn₆
    have hSignIn₈ : signOp.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation signOp) hCastBack hSignIn₇
    have hCorrIn₃ : corrOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds corrOp hCorrOp
    have hCorrIn₄ : corrOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation corrOp) hBiased hCorrIn₃
    have hCorrIn₅ : corrOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation corrOp) hQ hCorrIn₄
    have hCorrIn₆ : corrOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation corrOp) hZero hCorrIn₅
    have hCorrIn₇ : corrOp.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation corrOp) hNegOp hCorrIn₆
    have hCorrIn₈ : corrOp.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation corrOp) hCastBack hCorrIn₇
    have hBiasedIn₄ : biasedOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_new_inBounds biasedOp hBiased
    have hBiasedIn₅ : biasedOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation biasedOp) hQ hBiasedIn₄
    have hBiasedIn₆ : biasedOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation biasedOp) hZero hBiasedIn₅
    have hBiasedIn₇ : biasedOp.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation biasedOp) hNegOp hBiasedIn₆
    have hBiasedIn₈ : biasedOp.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation biasedOp) hCastBack hBiasedIn₇
    have hQIn₅ : qOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds qOp hQ
    have hQIn₆ : qOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation qOp) hZero hQIn₅
    have hQIn₇ : qOp.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation qOp) hNegOp hQIn₆
    have hQIn₈ : qOp.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation qOp) hCastBack hQIn₇
    have hZeroIn₆ : zeroOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds zeroOp hZero
    have hZeroIn₇ : zeroOp.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation zeroOp) hNegOp hZeroIn₆
    have hZeroIn₈ : zeroOp.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation zeroOp) hCastBack hZeroIn₇
    have hNegIn₇ : negOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds negOp hNegOp
    have hNegIn₈ : negOp.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation negOp) hCastBack hNegIn₇
    have hCastBackIn₈ : castBackOp.InBounds ctx₈.raw :=
      WfRewriter.createOp_new_inBounds castBackOp hCastBack
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hCast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSign hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hCorrOp hOpIn₂
    have hOpIn₄ : op.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hBiased hOpIn₃
    have hOpIn₅ : op.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hQ hOpIn₄
    have hOpIn₆ : op.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hZero hOpIn₅
    -- Every created op is distinct from the ones created before it.
    have neCS : castOp ≠ signOp := ne_createOp_new hSign hCastIn₁
    have neCR : castOp ≠ corrOp := ne_createOp_new hCorrOp hCastIn₂
    have neCB : castOp ≠ biasedOp := ne_createOp_new hBiased hCastIn₃
    have neCQ : castOp ≠ qOp := ne_createOp_new hQ hCastIn₄
    have neCZ : castOp ≠ zeroOp := ne_createOp_new hZero hCastIn₅
    have neCN : castOp ≠ negOp := ne_createOp_new hNegOp hCastIn₆
    have neCK : castOp ≠ castBackOp := ne_createOp_new hCastBack hCastIn₇
    have neSR : signOp ≠ corrOp := ne_createOp_new hCorrOp hSignIn₂
    have neSB : signOp ≠ biasedOp := ne_createOp_new hBiased hSignIn₃
    have neSQ : signOp ≠ qOp := ne_createOp_new hQ hSignIn₄
    have neSZ : signOp ≠ zeroOp := ne_createOp_new hZero hSignIn₅
    have neSN : signOp ≠ negOp := ne_createOp_new hNegOp hSignIn₆
    have neSK : signOp ≠ castBackOp := ne_createOp_new hCastBack hSignIn₇
    have neRB : corrOp ≠ biasedOp := ne_createOp_new hBiased hCorrIn₃
    have neRQ : corrOp ≠ qOp := ne_createOp_new hQ hCorrIn₄
    have neRZ : corrOp ≠ zeroOp := ne_createOp_new hZero hCorrIn₅
    have neRN : corrOp ≠ negOp := ne_createOp_new hNegOp hCorrIn₆
    have neRK : corrOp ≠ castBackOp := ne_createOp_new hCastBack hCorrIn₇
    have neBQ : biasedOp ≠ qOp := ne_createOp_new hQ hBiasedIn₄
    have neBZ : biasedOp ≠ zeroOp := ne_createOp_new hZero hBiasedIn₅
    have neBN : biasedOp ≠ negOp := ne_createOp_new hNegOp hBiasedIn₆
    have neBK : biasedOp ≠ castBackOp := ne_createOp_new hCastBack hBiasedIn₇
    have neQZ : qOp ≠ zeroOp := ne_createOp_new hZero hQIn₅
    have neQN : qOp ≠ negOp := ne_createOp_new hNegOp hQIn₆
    have neQK : qOp ≠ castBackOp := ne_createOp_new hCastBack hQIn₇
    have neZN : zeroOp ≠ negOp := ne_createOp_new hNegOp hZeroIn₆
    have neZK : zeroOp ≠ castBackOp := ne_createOp_new hCastBack hZeroIn₇
    have neNK : negOp ≠ castBackOp := ne_createOp_new hCastBack hNegIn₇
    have neOpC : op ≠ castOp := ne_createOp_new hCast opInBounds
    have neOpS : op ≠ signOp := ne_createOp_new hSign hOpIn₁
    have neOpR : op ≠ corrOp := ne_createOp_new hCorrOp hOpIn₂
    have neOpB : op ≠ biasedOp := ne_createOp_new hBiased hOpIn₃
    have neOpQ : op ≠ qOp := ne_createOp_new hQ hOpIn₄
    have neOpZ : op ≠ zeroOp := ne_createOp_new hZero hOpIn₅
    have neOpN : op ≠ negOp := ne_createOp_new hNegOp hOpIn₆
    -- Transport each op's fields from its creation context to `ctx₈`.
    have hCastType : castOp.getOpType! ctx₈.raw = .builtin .unrealized_conversion_cast := by
      rw [getOpType!_createOp_ne hCastBack neCK, getOpType!_createOp_ne hNegOp neCN,
        getOpType!_createOp_ne hZero neCZ, getOpType!_createOp_ne hQ neCQ,
        getOpType!_createOp_ne hBiased neCB, getOpType!_createOp_ne hCorrOp neCR,
        getOpType!_createOp_ne hSign neCS, getOpType!_createOp_self hCast]
    have hSignType : signOp.getOpType! ctx₈.raw = .riscv shiftDst := by
      rw [getOpType!_createOp_ne hCastBack neSK, getOpType!_createOp_ne hNegOp neSN,
        getOpType!_createOp_ne hZero neSZ, getOpType!_createOp_ne hQ neSQ,
        getOpType!_createOp_ne hBiased neSB, getOpType!_createOp_ne hCorrOp neSR,
        getOpType!_createOp_self hSign]
    have hCorrType : corrOp.getOpType! ctx₈.raw = .riscv corrDst := by
      rw [getOpType!_createOp_ne hCastBack neRK, getOpType!_createOp_ne hNegOp neRN,
        getOpType!_createOp_ne hZero neRZ, getOpType!_createOp_ne hQ neRQ,
        getOpType!_createOp_ne hBiased neRB, getOpType!_createOp_self hCorrOp]
    have hBiasedType : biasedOp.getOpType! ctx₈.raw = .riscv addDst := by
      rw [getOpType!_createOp_ne hCastBack neBK, getOpType!_createOp_ne hNegOp neBN,
        getOpType!_createOp_ne hZero neBZ, getOpType!_createOp_ne hQ neBQ,
        getOpType!_createOp_self hBiased]
    have hQType : qOp.getOpType! ctx₈.raw = .riscv shiftDst := by
      rw [getOpType!_createOp_ne hCastBack neQK, getOpType!_createOp_ne hNegOp neQN,
        getOpType!_createOp_ne hZero neQZ, getOpType!_createOp_self hQ]
    have hZeroType : zeroOp.getOpType! ctx₈.raw = .riscv .li := by
      rw [getOpType!_createOp_ne hCastBack neZK, getOpType!_createOp_ne hNegOp neZN,
        getOpType!_createOp_self hZero]
    have hNegType : negOp.getOpType! ctx₈.raw = .riscv negDst := by
      rw [getOpType!_createOp_ne hCastBack neNK, getOpType!_createOp_self hNegOp]
    have hCastBackType : castBackOp.getOpType! ctx₈.raw = .builtin .unrealized_conversion_cast := by
      rw [getOpType!_createOp_self hCastBack]
    have hCastOperands : castOp.getOperands! ctx₈.raw = #[lhs] := by
      rw [getOperands!_createOp_ne hCastBack neCK, getOperands!_createOp_ne hNegOp neCN,
        getOperands!_createOp_ne hZero neCZ, getOperands!_createOp_ne hQ neCQ,
        getOperands!_createOp_ne hBiased neCB, getOperands!_createOp_ne hCorrOp neCR,
        getOperands!_createOp_ne hSign neCS, getOperands!_createOp_self hCast]
    have hSignOperands :
        signOp.getOperands! ctx₈.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      rw [getOperands!_createOp_ne hCastBack neSK, getOperands!_createOp_ne hNegOp neSN,
        getOperands!_createOp_ne hZero neSZ, getOperands!_createOp_ne hQ neSQ,
        getOperands!_createOp_ne hBiased neSB, getOperands!_createOp_ne hCorrOp neSR,
        getOperands!_createOp_self hSign]
    have hCorrOperands :
        corrOp.getOperands! ctx₈.raw = #[ValuePtr.opResult (signOp.getResult 0)] := by
      rw [getOperands!_createOp_ne hCastBack neRK, getOperands!_createOp_ne hNegOp neRN,
        getOperands!_createOp_ne hZero neRZ, getOperands!_createOp_ne hQ neRQ,
        getOperands!_createOp_ne hBiased neRB, getOperands!_createOp_self hCorrOp]
    have hBiasedOperands :
        biasedOp.getOperands! ctx₈.raw
          = #[ValuePtr.opResult (castOp.getResult 0), ValuePtr.opResult (corrOp.getResult 0)] := by
      rw [getOperands!_createOp_ne hCastBack neBK, getOperands!_createOp_ne hNegOp neBN,
        getOperands!_createOp_ne hZero neBZ, getOperands!_createOp_ne hQ neBQ,
        getOperands!_createOp_self hBiased]
    have hQOperands :
        qOp.getOperands! ctx₈.raw = #[ValuePtr.opResult (biasedOp.getResult 0)] := by
      rw [getOperands!_createOp_ne hCastBack neQK, getOperands!_createOp_ne hNegOp neQN,
        getOperands!_createOp_ne hZero neQZ, getOperands!_createOp_self hQ]
    have hZeroOperands : zeroOp.getOperands! ctx₈.raw = #[] := by
      rw [getOperands!_createOp_ne hCastBack neZK, getOperands!_createOp_ne hNegOp neZN,
        getOperands!_createOp_self hZero]
    have hNegOperands :
        negOp.getOperands! ctx₈.raw
          = #[ValuePtr.opResult (zeroOp.getResult 0), ValuePtr.opResult (qOp.getResult 0)] := by
      rw [getOperands!_createOp_ne hCastBack neNK, getOperands!_createOp_self hNegOp]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₈.raw = #[ValuePtr.opResult (negOp.getResult 0)] := by
      rw [getOperands!_createOp_self hCastBack]
    have hSignProps : signOp.getProperties! ctx₈.raw (.riscv shiftDst)
        = cast hShift.symm
            (RISCVImmediateProperties.mk (IntegerAttr.mk ((bw : Int) - 1) (IntegerType.mk 64))) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack neSK,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hNegOp neSN,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hZero neSZ,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hQ neSQ,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hBiased neSB,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hCorrOp neSR,
        getProperties!_createOp_self hSign]
      rfl
    have hCorrProps : corrOp.getProperties! ctx₈.raw (.riscv corrDst)
        = cast hCorr.symm
            (RISCVImmediateProperties.mk
              (IntegerAttr.mk ((bw : Int) - (k : Int)) (IntegerType.mk 64))) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack neRK,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hNegOp neRN,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hZero neRZ,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hQ neRQ,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hBiased neRB,
        getProperties!_createOp_self hCorrOp]
      rfl
    have hQProps : qOp.getProperties! ctx₈.raw (.riscv shiftDst)
        = cast hShift.symm
            (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64))) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack neQK,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hNegOp neQN,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hZero neQZ,
        getProperties!_createOp_self hQ]
      rfl
    have hZeroProps : zeroOp.getProperties! ctx₈.raw (.riscv .li)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack neZK,
        OperationPtr.getProperties!_WfRewriter_createOp_ne hNegOp neZN,
        getProperties!_createOp_self hZero]
    have hCBType : ((op.getResult 0).get! ctx₇.raw).type
        = (⟨Attribute.integerType { bitwidth := bw }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₇.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        rw [getType!_opResult_createOp_ne hNegOp neOpN, getType!_opResult_createOp_ne hZero neOpZ,
          getType!_opResult_createOp_ne hQ neOpQ, getType!_opResult_createOp_ne hBiased neOpB,
          getType!_opResult_createOp_ne hCorrOp neOpR, getType!_opResult_createOp_ne hSign neOpS,
          getType!_opResult_createOp_ne hCast neOpC]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₈.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neCK, getResultTypes!_createOp_ne hNegOp neCN,
        getResultTypes!_createOp_ne hZero neCZ, getResultTypes!_createOp_ne hQ neCQ,
        getResultTypes!_createOp_ne hBiased neCB, getResultTypes!_createOp_ne hCorrOp neCR,
        getResultTypes!_createOp_ne hSign neCS, getResultTypes!_createOp_self hCast]
    have hSignResTypes : signOp.getResultTypes! ctx₈.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neSK, getResultTypes!_createOp_ne hNegOp neSN,
        getResultTypes!_createOp_ne hZero neSZ, getResultTypes!_createOp_ne hQ neSQ,
        getResultTypes!_createOp_ne hBiased neSB, getResultTypes!_createOp_ne hCorrOp neSR,
        getResultTypes!_createOp_self hSign]
    have hCorrResTypes : corrOp.getResultTypes! ctx₈.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neRK, getResultTypes!_createOp_ne hNegOp neRN,
        getResultTypes!_createOp_ne hZero neRZ, getResultTypes!_createOp_ne hQ neRQ,
        getResultTypes!_createOp_ne hBiased neRB, getResultTypes!_createOp_self hCorrOp]
    have hBiasedResTypes : biasedOp.getResultTypes! ctx₈.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neBK, getResultTypes!_createOp_ne hNegOp neBN,
        getResultTypes!_createOp_ne hZero neBZ, getResultTypes!_createOp_ne hQ neBQ,
        getResultTypes!_createOp_self hBiased]
    have hQResTypes : qOp.getResultTypes! ctx₈.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neQK, getResultTypes!_createOp_ne hNegOp neQN,
        getResultTypes!_createOp_ne hZero neQZ, getResultTypes!_createOp_self hQ]
    have hZeroResTypes : zeroOp.getResultTypes! ctx₈.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neZK, getResultTypes!_createOp_ne hNegOp neZN,
        getResultTypes!_createOp_self hZero]
    have hNegResTypes : negOp.getResultTypes! ctx₈.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [getResultTypes!_createOp_ne hCastBack neNK, getResultTypes!_createOp_self hNegOp]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₈.raw
        = #[⟨Attribute.integerType { bitwidth := bw }, isT⟩] := by
      rw [getResultTypes!_createOp_self hCastBack, hCBType]
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := hCastIn₈)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hOther₂⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := hSignIn₈)
        (res := sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt))
        (props := cast hShift.symm
          (RISCVImmediateProperties.mk (IntegerAttr.mk ((bw : Int) - 1) (IntegerType.mk 64))))
        (hSemSra ((bw : Int) - 1) (LLVM.Int.toReg xt))
        hSignType hSignProps hSignOperands hSignResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hOther₃⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₂) (inBounds := hCorrIn₈)
        (res := srlFn ((bw : Int) - (k : Int)) (sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt)))
        (props := cast hCorr.symm
          (RISCVImmediateProperties.mk
            (IntegerAttr.mk ((bw : Int) - (k : Int)) (IntegerType.mk 64))))
        (hSemSrl ((bw : Int) - (k : Int)) (sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt)))
        hCorrType hCorrProps hCorrOperands hCorrResTypes hRes₂
    have hCastRes₃ : s₃.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hOther₃ _ (opResult_not_mem_getResults! neCR),
        hOther₂ _ (opResult_not_mem_getResults! neCS)]
      exact hRes₁
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := hBiasedIn₈)
        (f := addFn) (hSemAdd _ _) hBiasedType hBiasedOperands hBiasedResTypes hCastRes₃ hRes₃
    obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₄) (inBounds := hQIn₈)
        (res := sraFn (k : Int)
          (addFn (LLVM.Int.toReg xt)
            (srlFn ((bw : Int) - (k : Int)) (sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt)))))
        (props := cast hShift.symm
          (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64))))
        (hSemSra (k : Int) _)
        hQType hQProps hQOperands hQResTypes hRes₄
    obtain ⟨s₆, hI₆, hMem₆, hRes₆, hOther₆⟩ :=
      interpretOp_riscv_li_forward (state := s₅) (inBounds := hZeroIn₈)
        (props := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64)))
        hZeroType hZeroProps hZeroOperands hZeroResTypes
    -- Transport the shift result across the `li` step (`li` touches only its own result).
    have hQRes₆ : s₆.variables.getVar? (ValuePtr.opResult (qOp.getResult 0))
        = some (RuntimeValue.reg
            (sraFn (k : Int)
              (addFn (LLVM.Int.toReg xt)
                (srlFn ((bw : Int) - (k : Int))
                  (sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt)))))) := by
      rw [hOther₆ _ (opResult_not_mem_getResults! neQZ)]; exact hRes₅
    obtain ⟨s₇, hI₇, hMem₇, hRes₇, -⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₆) (inBounds := hNegIn₈)
        (f := subFn) (hSemSub _ _) hNegType hNegOperands hNegResTypes hRes₆ hQRes₆
    obtain ⟨s₈, hI₈, hMem₈, hRes₈, -⟩ :=
      interpretOp_castBack_forward (state := s₇) (inBounds := hCastBackIn₈)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₇
    refine ⟨s₈, ?_, ?_, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, hI₈, liftM, monadLift,
        MonadLift.monadLift, Interp]
    · rw [hMem₈, hMem₇, hMem₆, hMem₅, hMem₄, hMem₃, hMem₂, hMem₁, ← memoryRefinement]
      exact hMem.symm
    · refine ⟨#[RuntimeValue.int bw
          (RISCV.Reg.toInt
            (subFn (Data.RISCV.li (BitVec.ofInt 64 0))
              (sraFn (k : Int)
                (addFn (LLVM.Int.toReg xt)
                  (srlFn ((bw : Int) - (k : Int))
                    (sraFn ((bw : Int) - 1) (LLVM.Int.toReg xt)))))) bw)], ?_, ?_⟩
      · simp [hRes₈, Option.bind, Option.map]
      · rw [hExactFalse]
        exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefineNeg xVal xt imm.value k hK hK0 hxtRef⟩

/-- `riscv.sub _ (li 0)` is `riscv.neg` (the `li 0` immediate is `BitVec.ofInt 64 0`). -/
private theorem gen_sub_li_zero_eq_neg (r : Data.RISCV.Reg) :
    Data.RISCV.sub r (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.neg r := by
  rw [Data.RISCV.neg, show BitVec.ofInt 64 0 = 0 from by simp]

/-- `riscv.subw _ (li 0)` is `riscv.negw`. -/
private theorem gen_subw_li_zero_eq_negw (r : Data.RISCV.Reg) :
    Data.RISCV.subw r (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.negw r := by
  rw [Data.RISCV.negw, show BitVec.ofInt 64 0 = 0 from by simp]

/-! ### Instantiations

    The generic proof hands the refinement hypotheses the matcher's raw output — an `Int` constant
    and a `Nat` exponent, with the immediates as `Int` subtractions. The bridges above re-encode
    both as the `BitVec`s the data lemmas take. -/

namespace Example

/-- Correctness of the `srai`/`srli`/`add`/`sub` lowering of `llvm.sdiv x (±2^k)` on `i64`. -/
theorem sdivPow2_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics
      (sdivPow2GenLocal .srai rfl .srli rfl .add rfl .sub rfl 64) h h₂ h₃ h₄ :=
  sdivPow2GenLocal_preservesSemantics
    (sraFn := fun i r => Data.RISCV.srai (BitVec.ofInt 6 i) r)
    (srlFn := fun i r => Data.RISCV.srli (BitVec.ofInt 6 i) r)
    (addFn := fun r₁ r₂ => Data.RISCV.add r₂ r₁)
    (subFn := fun z r => Data.RISCV.sub r z)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ xt c k hm hk0 hx => by
      obtain ⟨hc, hk0', hk63⟩ := matchSignedPow2Divisor_pos_64 hm hk0
      rw [show BitVec.ofInt 6 (((64 : Nat) : Int) - 1) = 63 from by decide,
        ofInt_6_sub k (by have := matchSignedPow2Divisor_exponent_lt (show 0 < 64 by omega) hm
                          omega)]
      exact sdivPow2_pos_isRefinedBy (BitVec.ofInt 64 c) _ hc hk0' hk63 hx)
    (fun _ xt c k hm hk0 hx => by
      obtain ⟨hc, hk0'⟩ := matchSignedPow2Divisor_neg_64 hm hk0
      rw [gen_sub_li_zero_eq_neg,
        show BitVec.ofInt 6 (((64 : Nat) : Int) - 1) = 63 from by decide,
        ofInt_6_sub k (by have := matchSignedPow2Divisor_exponent_lt (show 0 < 64 by omega) hm
                          omega)]
      exact sdivPow2_neg_isRefinedBy (BitVec.ofInt 64 c) _ hc hk0' hx)

/-- Correctness of the `sraiw`/`srliw`/`addw`/`subw` lowering of `llvm.sdiv x (±2^k)` on `i32`. -/
theorem sdivwPow2_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics
      (sdivPow2GenLocal .sraiw rfl .srliw rfl .addw rfl .subw rfl 32) h h₂ h₃ h₄ :=
  sdivPow2GenLocal_preservesSemantics
    (sraFn := fun i r => Data.RISCV.sraiw (BitVec.ofInt 5 i) r)
    (srlFn := fun i r => Data.RISCV.srliw (BitVec.ofInt 5 i) r)
    (addFn := fun r₁ r₂ => Data.RISCV.addw r₂ r₁)
    (subFn := fun z r => Data.RISCV.subw r z)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ xt c k hm hk0 hx => by
      obtain ⟨hc, hk0', hk31⟩ := matchSignedPow2Divisor_pos_32 hm hk0
      rw [show BitVec.ofInt 5 (((32 : Nat) : Int) - 1) = 31 from by decide,
        ofInt_5_sub k (by have := matchSignedPow2Divisor_exponent_lt (show 0 < 32 by omega) hm
                          omega)]
      exact sdivwPow2_pos_isRefinedBy (BitVec.ofInt 32 c) _ hc hk0' hk31 hx)
    (fun _ xt c k hm hk0 hx => by
      obtain ⟨hc, hk0'⟩ := matchSignedPow2Divisor_neg_32 hm hk0
      rw [gen_subw_li_zero_eq_negw,
        show BitVec.ofInt 5 (((32 : Nat) : Int) - 1) = 31 from by decide,
        ofInt_5_sub k (by have := matchSignedPow2Divisor_exponent_lt (show 0 < 32 by omega) hm
                          omega)]
      exact sdivwPow2_neg_isRefinedBy (BitVec.ofInt 32 c) _ hc hk0' hx)

end Example

end Veir
