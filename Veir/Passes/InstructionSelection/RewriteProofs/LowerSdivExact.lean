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
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelect
-- Imported for their pre-generated match-congruence auxiliaries (see `LowerSelectSingleBit`).
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRoriw
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectSingleBit

namespace Veir

/-!
## Correctness of `sdivPow2ExactGenLocal`

`sdivPow2ExactGenLocal dst hDst negDst hNeg width` strength-reduces an *exact* `sdiv x (2^k)` to an
arithmetic shift right by `k` (`riscv.srai`/`sraiw`), negating the result for a negative divisor
(`riscv.sub`/`subw` of zero). Two branches:

* positive divisor: `castToReg x → srai (k) → castBack` (3 ops), and
* negative divisor: `castToReg x → srai (k) → li 0 → sub 0 (srai …) → castBack` (5 ops).

Instances: `sdivPow2Exact` (`srai`/`sub`, i64), `sdivwPow2Exact` (`sraiw`/`subw`, i32).

The data-level identities (an exact `sdiv` by `±2^k` is `±(x >>s k)`) are the pre-proven
`sdivPow2Exact_{pos,neg}_refinement` (and the `w` analogues) in `InstructionSelection.Proofs`; here
`matchSignedPow2Divisor_spec` bridges the matcher's `(k, isNeg)` to the `1 <<< k` divisor form and
the shift-amount range each of those lemmas requires. The source `sdiv` raises UB on a
zero/poison/overflowing divisor, so the interpretation unfold uses the UB-aware `hSemSrc` split (as
in `sdiv_local`).
-/

/-- A successful signed power-of-two divisor match pins the `w`-bit signed magnitude of the divisor
    to `2^k` and reports its sign. Reads the classification off the width-normalized signed value
    `(BitVec.ofInt w c).toInt`, matching the semantics of the constant the divisor decodes to. -/
theorem matchSignedPow2Divisor_spec {w : Nat} {c : Int} {k : Nat} {b : Bool}
    (h : matchSignedPow2Divisor w c = some (k, b)) :
    ((BitVec.ofInt w c).toInt).natAbs = 2 ^ k ∧ b = decide ((BitVec.ofInt w c).toInt < 0) := by
  unfold matchSignedPow2Divisor at h
  simp only [log2IfPow2] at h
  split at h
  · exact absurd h (by simp [Option.bind])
  · rename_i hcond
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      bne_eq_false_iff_eq] at hcond
    have h2 := Option.some.inj h
    obtain ⟨hk, hb⟩ := Prod.mk.inj h2
    exact ⟨by rw [← hk]; exact eq_two_pow_log2 _ hcond.1 hcond.2, hb.symm⟩

/-! ### Data-level refinement lemmas -/

/-- `sdiv exact x (2^k)` on `i64` (positive divisor) refines `riscv.srai x k`. -/
theorem sdiv_pos_isRefinedBy_srai {x xt : Data.LLVM.Int 64} (c : Int) (k : Nat)
    (hm : matchSignedPow2Divisor 64 c = some (k, false)) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant 64 c) true
      ⊒ RISCV.Reg.toInt (Data.RISCV.srai (BitVec.ofInt 6 (k : Int)) (LLVM.Int.toReg xt)) 64 := by
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
  have hkbv : BitVec.ofInt 6 (k : Int) < 63 := by
    rw [BitVec.lt_def, hKtoNat, show (63 : BitVec 6).toNat = 63 from by decide]; omega
  have hdivbv : BitVec.ofInt 64 c = (1#64) <<< (BitVec.ofInt 6 (k : Int)) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.shiftLeft_eq', ← BitVec.twoPow_eq, BitVec.toInt_twoPow, hKtoNat,
      if_neg (by omega), if_neg (by omega), hs2k]; norm_cast
  have hdiv : Data.LLVM.Int.constant 64 c
      = Data.LLVM.Int.val ((1#64) <<< (BitVec.ofInt 6 (k : Int))) := by
    rw [Data.LLVM.Int.constant, hdivbv]
  rw [hdiv]
  exact isRefinedBy_trans
    (Data.LLVM.Int.sdiv_mono x _ xt _ h (isRefinedBy_refl _) true)
    (Data.RISCV.sdivPow2Exact_pos_refinement (BitVec.ofInt 6 (k : Int)) hkbv)

/-- `sdiv exact x (-2^k)` on `i64` (negative divisor) refines `riscv.sub 0 (riscv.srai x k)`. -/
theorem sdiv_neg_isRefinedBy_neg_srai {x xt : Data.LLVM.Int 64} (c : Int) (k : Nat)
    (hm : matchSignedPow2Divisor 64 c = some (k, true)) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant 64 c) true
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.neg (Data.RISCV.srai (BitVec.ofInt 6 (k : Int)) (LLVM.Int.toReg xt))) 64 := by
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
  have hdivbv : BitVec.ofInt 64 c = -((1#64) <<< (BitVec.ofInt 6 (k : Int))) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_neg_one_shl _ (by rw [hKtoNat]; omega), hKtoNat, hs2k]
  have hdiv : Data.LLVM.Int.constant 64 c
      = Data.LLVM.Int.val (-((1#64) <<< (BitVec.ofInt 6 (k : Int)))) := by
    rw [Data.LLVM.Int.constant, hdivbv]
  rw [hdiv]
  exact isRefinedBy_trans
    (Data.LLVM.Int.sdiv_mono x _ xt _ h (isRefinedBy_refl _) true)
    (Data.RISCV.sdivPow2Exact_neg_refinement (BitVec.ofInt 6 (k : Int)))

/-- `i32` analogue of `sdiv_pos_isRefinedBy_srai` (`sraiw`). -/
theorem sdiv_pos_isRefinedBy_sraiw {x xt : Data.LLVM.Int 32} (c : Int) (k : Nat)
    (hm : matchSignedPow2Divisor 32 c = some (k, false)) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant 32 c) true
      ⊒ RISCV.Reg.toInt (Data.RISCV.sraiw (BitVec.ofInt 5 (k : Int)) (LLVM.Int.toReg xt)) 32 := by
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
  have hkbv : BitVec.ofInt 5 (k : Int) < 31 := by
    rw [BitVec.lt_def, hKtoNat, show (31 : BitVec 5).toNat = 31 from by decide]; omega
  have hdivbv : BitVec.ofInt 32 c = (1#32) <<< (BitVec.ofInt 5 (k : Int)) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.shiftLeft_eq', ← BitVec.twoPow_eq, BitVec.toInt_twoPow, hKtoNat,
      if_neg (by omega), if_neg (by omega), hs2k]; norm_cast
  have hdiv : Data.LLVM.Int.constant 32 c
      = Data.LLVM.Int.val ((1#32) <<< (BitVec.ofInt 5 (k : Int))) := by
    rw [Data.LLVM.Int.constant, hdivbv]
  rw [hdiv]
  exact isRefinedBy_trans
    (Data.LLVM.Int.sdiv_mono x _ xt _ h (isRefinedBy_refl _) true)
    (Data.RISCV.sdivwPow2Exact_pos_refinement (BitVec.ofInt 5 (k : Int)) hkbv)

/-- `i32` analogue of `sdiv_neg_isRefinedBy_neg_srai` (`subw`/`negw`). -/
theorem sdiv_neg_isRefinedBy_negw_sraiw {x xt : Data.LLVM.Int 32} (c : Int) (k : Nat)
    (hm : matchSignedPow2Divisor 32 c = some (k, true)) (h : x ⊒ xt) :
    Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant 32 c) true
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.negw (Data.RISCV.sraiw (BitVec.ofInt 5 (k : Int)) (LLVM.Int.toReg xt))) 32 := by
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
  have hdivbv : BitVec.ofInt 32 c = -((1#32) <<< (BitVec.ofInt 5 (k : Int))) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_neg_one_shl _ (by rw [hKtoNat]; omega), hKtoNat, hs2k]
  have hdiv : Data.LLVM.Int.constant 32 c
      = Data.LLVM.Int.val (-((1#32) <<< (BitVec.ofInt 5 (k : Int)))) := by
    rw [Data.LLVM.Int.constant, hdivbv]
  rw [hdiv]
  exact isRefinedBy_trans
    (Data.LLVM.Int.sdiv_mono x _ xt _ h (isRefinedBy_refl _) true)
    (Data.RISCV.sdivwPow2Exact_neg_refinement (BitVec.ofInt 5 (k : Int)))

/-! ### Shared correctness of `sdivPow2ExactGenLocal` -/

set_option maxHeartbeats 3200000 in
theorem sdivPow2ExactGenLocal_preservesSemantics
    {dst : Riscv} {hDst : Riscv.propertiesOf dst = RISCVImmediateProperties}
    {negDst : Riscv} {hNeg : Riscv.propertiesOf negDst = Unit} {width : Nat}
    {sraFn : Nat → Data.RISCV.Reg → Data.RISCV.Reg}
    {subFn : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    (hSemSra : ∀ (k : Nat) (r : Data.RISCV.Reg)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' dst
            (cast hDst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64))))
            resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (sraFn k r)], mem, none)))
    (hSemSub : ∀ (z r : Data.RISCV.Reg) (props : Riscv.propertiesOf negDst)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' negDst props resultTypes #[.reg z, .reg r] blockOperands mem
          = some (.ok (#[.reg (subFn z r)], mem, none)))
    (hRefinePos : ∀ (x xt : Data.LLVM.Int width) (c : Int) (k : Nat),
        matchSignedPow2Divisor width c = some (k, false) → x ⊒ xt →
        Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant width c) true
          ⊒ RISCV.Reg.toInt (sraFn k (LLVM.Int.toReg xt)) width)
    (hRefineNeg : ∀ (x xt : Data.LLVM.Int width) (c : Int) (k : Nat),
        matchSignedPow2Divisor width c = some (k, true) → x ⊒ xt →
        Data.LLVM.Int.sdiv x (Data.LLVM.Int.constant width c) true
          ⊒ RISCV.Reg.toInt
              (subFn (Data.RISCV.li (BitVec.ofInt 64 0)) (sraFn k (LLVM.Int.toReg xt))) width)
    {h : LocalRewritePattern.ReturnOps (sdivPow2ExactGenLocal dst hDst negDst hNeg width)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (sdivPow2ExactGenLocal dst hDst negDst hNeg width)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (sdivPow2ExactGenLocal dst hDst negDst hNeg width)}
    {h₄ : LocalRewritePattern.ReturnValues (sdivPow2ExactGenLocal dst hDst negDst hNeg width)} :
    LocalRewritePattern.PreservesSemantics (sdivPow2ExactGenLocal dst hDst negDst hNeg width)
      h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, sdivPow2ExactGenLocal]
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
  -- Peel the `exact` guard (bail branch discharged; surviving branch has `props.exact = true`).
  peelSplittableCondition [hExact] hpattern
  have hExactTrue : props.exact = true := by
    cases hb : props.exact
    · exact absurd hb hExact
    · rfl
  -- Resolve the `.integerType t` match on the result type, then the bitwidth guard.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  peelSplittableCondition' [hBw] hpattern
  -- Peel the constant match and the power-of-two divisor match.
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
  -- Unfold the source `sdiv` interpretation (UB-aware, as in `sdiv_local`).
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
  -- Peel the two shared creations (`castToReg lhs`, `srai/sraiw`); the rest branches on the sign.
  peelCastToRegLocal hpattern ctx₁ castOp hCast hDomCtxLhs hDom₁
  peelOpCreation! hpattern ctx₂ sraOp hSra hDom₁ hDom₂
  -- Branch on the divisor's sign.
  cases isNeg with
  | false =>
    -- Positive divisor: `castToReg → srai → castBack` (3 ops), as in `udivPow2`.
    simp only [reduceIte] at hpattern
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtxLhs hDom₃ lhsNotOp
    obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
    have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hSraType : sraOp.getOpType! ctx₃.raw = .riscv dst := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[lhs] := by grind
    have hSraOperands :
        sraOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (sraOp.getResult 0)] := by grind
    have hSraProps : sraOp.getProperties! ctx₃.raw (.riscv dst)
        = cast hDst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64)))
        := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hSra (operation := sraOp)]
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType { bitwidth := bw }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hSra
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hSra (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hSraResTypes : sraOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSra (operation := sraOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := sraOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.integerType { bitwidth := bw }, isT⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
        (res := sraFn k (LLVM.Int.toReg xt))
        (props := cast hDst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64))))
        (hSemSra k (LLVM.Int.toReg xt))
        hSraType hSraProps hSraOperands hSraResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int bw (RISCV.Reg.toInt (sraFn k (LLVM.Int.toReg xt)) bw)], ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · rw [hExactTrue]
        exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefinePos xVal xt imm.value k hK hxtRef⟩
  | true =>
    -- Negative divisor: `castToReg → srai → li 0 → sub 0 (srai …) → castBack` (5 ops).
    rw [if_neg (by decide)] at hpattern
    simp only [negateRegLocal, bind, Option.bind_assoc] at hpattern
    peelOpCreation! hpattern ctx₃ zeroOp hZero hDom₂ hDom₃
    peelOpCreation! hpattern ctx₄ negOp hNegOp hDom₃ hDom₄
    simp only [Option.some.injEq, exists_eq_left'] at hpattern
    peelReplaceWithRegLocal hpattern ctx₅ castBackOp hCastBack hDom₄ hDom₅
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtxLhs hDom₅ lhsNotOp
    obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
    have hCastType : castOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getOpType!_WfRewriter_createOp hSra (operation := castOp),
        OperationPtr.getOpType!_WfRewriter_createOp hZero (operation := castOp),
        OperationPtr.getOpType!_WfRewriter_createOp hNegOp (operation := castOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hSraType : sraOp.getOpType! ctx₅.raw = .riscv dst := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hSra (operation := sraOp),
        OperationPtr.getOpType!_WfRewriter_createOp hZero (operation := sraOp),
        OperationPtr.getOpType!_WfRewriter_createOp hNegOp (operation := sraOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := sraOp)]
    have hZeroType : zeroOp.getOpType! ctx₅.raw = .riscv .li := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hZero (operation := zeroOp),
        OperationPtr.getOpType!_WfRewriter_createOp hNegOp (operation := zeroOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := zeroOp)]
    have hNegType : negOp.getOpType! ctx₅.raw = .riscv negDst := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hNegOp (operation := negOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := negOp)]
    have hCastBackType : castBackOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := castBackOp)]
    have hCastOperands : castOp.getOperands! ctx₅.raw = #[lhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getOperands!_WfRewriter_createOp hSra (operation := castOp),
        OperationPtr.getOperands!_WfRewriter_createOp hZero (operation := castOp),
        OperationPtr.getOperands!_WfRewriter_createOp hNegOp (operation := castOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hSraOperands :
        sraOp.getOperands! ctx₅.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hSra (operation := sraOp),
        OperationPtr.getOperands!_WfRewriter_createOp hZero (operation := sraOp),
        OperationPtr.getOperands!_WfRewriter_createOp hNegOp (operation := sraOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := sraOp)]
    have hZeroOperands : zeroOp.getOperands! ctx₅.raw = #[] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hZero (operation := zeroOp),
        OperationPtr.getOperands!_WfRewriter_createOp hNegOp (operation := zeroOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := zeroOp)]
    have hNegOperands :
        negOp.getOperands! ctx₅.raw
          = #[ValuePtr.opResult (zeroOp.getResult 0), ValuePtr.opResult (sraOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hNegOp (operation := negOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := negOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₅.raw = #[ValuePtr.opResult (negOp.getResult 0)] := by grind
    have hSraProps : sraOp.getProperties! ctx₅.raw (.riscv dst)
        = cast hDst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64)))
        := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
        OperationPtr.getProperties!_WfRewriter_createOp_ne hNegOp (by grind),
        OperationPtr.getProperties!_WfRewriter_createOp_ne hZero (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hSra (operation := sraOp)]
    have hZeroProps : zeroOp.getProperties! ctx₅.raw (.riscv .li)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
        OperationPtr.getProperties!_WfRewriter_createOp_ne hNegOp (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hZero (operation := zeroOp)]
    have hCBType : ((op.getResult 0).get! ctx₄.raw).type
        = (⟨Attribute.integerType { bitwidth := bw }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₄.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hNegOp
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hZero
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hSra
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hSra (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hZero (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hNegOp (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hSraResTypes : sraOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSra (operation := sraOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hZero (operation := sraOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hNegOp (operation := sraOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := sraOp)]
    have hZeroResTypes : zeroOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hZero (operation := zeroOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hNegOp (operation := zeroOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := zeroOp)]
    have hNegResTypes : negOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hNegOp (operation := negOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := negOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.integerType { bitwidth := bw }, isT⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
        (res := sraFn k (LLVM.Int.toReg xt))
        (props := cast hDst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64))))
        (hSemSra k (LLVM.Int.toReg xt))
        hSraType hSraProps hSraOperands hSraResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hOther₃⟩ :=
      interpretOp_riscv_li_forward (state := s₂) (inBounds := by grind)
        (props := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64)))
        hZeroType hZeroProps hZeroOperands hZeroResTypes
    -- Transport the shift result across the `li` step (`li` touches only its own result).
    have hSraNotZeroRes : ValuePtr.opResult (sraOp.getResult 0) ∉ zeroOp.getResults! ctx₅.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₅.raw
          (ValuePtr.opResult (sraOp.getResult 0)) zeroOp with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (by grind [OperationPtr.getResult])
    have hSraRes₃ : s₃.variables.getVar? (ValuePtr.opResult (sraOp.getResult 0))
        = some (RuntimeValue.reg (sraFn k (LLVM.Int.toReg xt))) := by
      rw [hOther₃ _ hSraNotZeroRes]; exact hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := by grind)
        (f := subFn) (hSemSub _ _) hNegType hNegOperands hNegResTypes hRes₃ hSraRes₃
    obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
      interpretOp_castBack_forward (state := s₄) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₄
    refine ⟨s₅, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.int bw
          (RISCV.Reg.toInt (subFn (Data.RISCV.li (BitVec.ofInt 64 0)) (sraFn k (LLVM.Int.toReg xt))) bw)],
          ?_, ?_⟩
      · simp [hRes₅, Option.bind, Option.map]
      · rw [hExactTrue]
        exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefineNeg xVal xt imm.value k hK hxtRef⟩

/-- `riscv.sub _ (li 0)` is `riscv.neg` (the `li 0` immediate is `BitVec.ofInt 64 0`). -/
private theorem sub_li_zero_eq_neg (r : Data.RISCV.Reg) :
    Data.RISCV.sub r (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.neg r := by
  rw [Data.RISCV.neg, show BitVec.ofInt 64 0 = 0 from by simp]

/-- `riscv.subw _ (li 0)` is `riscv.negw`. -/
private theorem subw_li_zero_eq_negw (r : Data.RISCV.Reg) :
    Data.RISCV.subw r (Data.RISCV.li (BitVec.ofInt 64 0)) = Data.RISCV.negw r := by
  rw [Data.RISCV.negw, show BitVec.ofInt 64 0 = 0 from by simp]

/-! ### Instantiations -/

namespace Example

/-- Correctness of the `riscv.srai`/`riscv.sub` lowering of an exact `llvm.sdiv x (2^k)` on `i64`. -/
theorem sdivPow2Exact_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics (sdivPow2ExactGenLocal .srai rfl .sub rfl 64) h h₂ h₃ h₄ :=
  sdivPow2ExactGenLocal_preservesSemantics
    (sraFn := fun k r => Data.RISCV.srai (BitVec.ofInt 6 (k : Int)) r)
    (subFn := fun z r => Data.RISCV.sub r z)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ xt c k hk hx => sdiv_pos_isRefinedBy_srai c k hk hx)
    (fun _ xt c k hk hx => by rw [sub_li_zero_eq_neg]; exact sdiv_neg_isRefinedBy_neg_srai c k hk hx)

/-- Correctness of the `riscv.sraiw`/`riscv.subw` lowering of an exact `llvm.sdiv x (2^k)` on `i32`. -/
theorem sdivwPow2Exact_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics (sdivPow2ExactGenLocal .sraiw rfl .subw rfl 32) h h₂ h₃ h₄ :=
  sdivPow2ExactGenLocal_preservesSemantics
    (sraFn := fun k r => Data.RISCV.sraiw (BitVec.ofInt 5 (k : Int)) r)
    (subFn := fun z r => Data.RISCV.subw r z)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ xt c k hk hx => sdiv_pos_isRefinedBy_sraiw c k hk hx)
    (fun _ xt c k hk hx => by
      rw [subw_li_zero_eq_negw]; exact sdiv_neg_isRefinedBy_negw_sraiw c k hk hx)

end Example

end Veir
