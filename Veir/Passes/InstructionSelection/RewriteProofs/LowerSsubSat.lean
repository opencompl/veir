import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerConst
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBswap
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSaddSat
import Veir.Passes.InstructionSelection.RewriteProofs.LowerIcmp

namespace Veir

/-!
## Correctness of `ssubSat_local`

`llvm.intr.ssub.sat` on a 64-bit integer is lowered to LLVM's RV64+Zicond signed saturating-sub
sequence.  Casting both operands to registers `X = toReg xt`, `Y = toReg yt`, it emits:
`diff = sub X Y`, `cmp = slt X Y` (i.e. `X <s Y`), `diffSignBit = srli 63 diff`,
`diffSign = srai 63 diff`, `intMin = slli 63 (li -1)`, `overflow = xor cmp diffSignBit`,
`sat = xor diffSign intMin`, then the branchless select
`or (czeronez diff overflow) (czeroeqz sat overflow)` (`overflow ≠ 0 ? sat : diff`), cast back to
the integer type.

The chain is the `sub` sibling of `saddSat_local` (fourteen ops, `i64`-only, no bitwidth branch),
but the proof is written in the `LowerFshGeneral` style: every creation is peeled with the plain
`peelOpCreation` + `createOp!_none_some`, the `LowerIcmp` `CtxExtends` bundles are composed once
(`E₁…E₁₄`, suffix compositions `Fᵢ : ctxᵢ → ctx₁₄`), each op's structural facts transport by a
single `rw [Fᵢ.…]; grind`, and operand dominance transports once at the end via `Ectx.dominates` —
avoiding `LowerSaddSat`'s quadratic in-bounds/distinctness bookkeeping.
-/

/-- The first result of a freshly created op (with at least one result type) is in bounds in the
    creation's output context. Proven once here so the fourteen-creation proofs below can use it as
    a term: the equivalent inline `grind` blows its E-matching budget in their large contexts. -/
theorem opResult_getResult_inBounds_of_createOp
    {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr} {opType : OpCode}
    {resultTypes operands blockOperands regions} {properties : HasOpInfo.propertiesOf opType}
    {hoper hblock hreg hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties none
      hoper hblock hreg hins = some (ctx', newOp))
    (hsize : 0 < resultTypes.size) :
    (ValuePtr.opResult (newOp.getResult 0)).InBounds ctx'.raw := by
  grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]

/-- Correctness of the branchless signed saturating-sub chain: the round trip
    `int × int → reg × reg → li/sub/slt/srli/srai/slli/xor/xor/czeronez/czeroeqz/or → int` refines
    `ssub.sat`.  (`xt`/`yt` are the possibly-more-defined target-side values of the operands.) -/
theorem ssubSat_isRefinedBy_toInt {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.ssubSat x y ⊒
      RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.czeronez
            (Data.RISCV.xor
              (Data.RISCV.srli (BitVec.ofInt 6 63)
                (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
            (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.czeroeqz
            (Data.RISCV.xor
              (Data.RISCV.srli (BitVec.ofInt 6 63)
                (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
            (Data.RISCV.xor
              (Data.RISCV.slli (BitVec.ofInt 6 63) (Data.RISCV.li (BitVec.ofInt 64 (-1))))
              (Data.RISCV.srai (BitVec.ofInt 6 63)
                (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))))) 64 := by
  revert h₁ h₂
  veir_bv_decide

set_option maxHeartbeats 4000000 in
/-- Correctness of the `ssubSat_local` lowering: the twelve-op RV64+Zicond signed saturating-sub
    chain refines `llvm.intr.ssub.sat`. -/
theorem ssubSat_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics ssubSat_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, ssubSat_local, createRISCVUnitLocal,
    createRISCVImmLocal, signedSatSelectLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchSsubSat op ctx.raw).isSome := by
    cases hM : matchSsubSat op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSsubSat_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_intr__ssub__sat opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  -- Resolve the result-type-destructuring match on `intType`.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand values and their `ssubSat`.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold
      (srcFn := fun {_} x y _ => Data.LLVM.Int.ssubSat x y)
      (props := op.getProperties! ctx.raw (.llvm .intr__ssub__sat))
      opInBounds hOpType hNumResults hOperands rfl
      (fun bw x y props rt bo mem res h => by
        have hEq : Llvm.interpretOp' .intr__ssub__sat props rt #[.int bw x, .int bw y] bo mem
            = some (.ok (#[.int bw (Data.LLVM.Int.ssubSat x y)], mem, none)) := by
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]
        rw [hEq] at h; injection h with h; injection h with h; exact h.symm)
      hinterp hLhsType hRhsType
  subst hCf
  -- The matched operands dominate the rewrite point in the source context.
  have hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  peelSplittableCondition' [hBw] hpattern
  -- Source value: `op`'s single result is `ssubSat` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- In-bounds facts and `lhs`/`rhs` are not among `op`'s results.
  have hLhsIn : lhs.InBounds ctx.raw := by clear hpattern; grind
  have hRhsIn : rhs.InBounds ctx.raw := by clear hpattern; grind
  have hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    clear hpattern
    grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the ten creations before the select block (two casts + `li`/`sub`/`slt`/`srli`/`srai`/
  -- `slli`/`xor`/`xor`).
  peelOpCreation hpattern ctx₁ lcastOp hLCast
  simp only [castToRegLocal] at hLCast
  replace hLCast := WfRewriter.createOp!_none_some hLCast
  obtain ⟨_, _, _, hLCast⟩ := hLCast
  peelOpCreation hpattern ctx₂ rcastOp hRCast
  simp only [castToRegLocal] at hRCast
  replace hRCast := WfRewriter.createOp!_none_some hRCast
  obtain ⟨_, _, _, hRCast⟩ := hRCast
  peelOpCreation hpattern ctx₃ oneOp hOne
  replace hOne := WfRewriter.createOp!_none_some hOne
  obtain ⟨_, _, _, hOne⟩ := hOne
  peelOpCreation hpattern ctx₄ diffOp hDiff
  replace hDiff := WfRewriter.createOp!_none_some hDiff
  obtain ⟨_, _, _, hDiff⟩ := hDiff
  peelOpCreation hpattern ctx₅ cmpOp hCmp
  replace hCmp := WfRewriter.createOp!_none_some hCmp
  obtain ⟨_, _, _, hCmp⟩ := hCmp
  peelOpCreation hpattern ctx₆ dsbOp hDsb
  replace hDsb := WfRewriter.createOp!_none_some hDsb
  obtain ⟨_, _, _, hDsb⟩ := hDsb
  peelOpCreation hpattern ctx₇ dsOp hDs
  replace hDs := WfRewriter.createOp!_none_some hDs
  obtain ⟨_, _, _, hDs⟩ := hDs
  peelOpCreation hpattern ctx₈ imOp hIm
  replace hIm := WfRewriter.createOp!_none_some hIm
  obtain ⟨_, _, _, hIm⟩ := hIm
  peelOpCreation hpattern ctx₉ ovOp hOv
  replace hOv := WfRewriter.createOp!_none_some hOv
  obtain ⟨_, _, _, hOv⟩ := hOv
  peelOpCreation hpattern ctx₁₀ satOp hSat
  replace hSat := WfRewriter.createOp!_none_some hSat
  obtain ⟨_, _, _, hSat⟩ := hSat
  -- `signedSatSelectLocal` is a *nested* `do` block returning `(ctx, ops, values)`, so its four
  -- creations sit under one extra existential. Open it, peel the four inner creations, and keep
  -- `hFinal` (how the block's result feeds the pattern's return value) for the final cleanup.
  have ⟨⟨ctxSel, selOps, selVals⟩, hSelInner, hFinal⟩ := hpattern
  clear hpattern; have hpattern := hSelInner; clear hSelInner
  peelOpCreation hpattern ctx₁₁ wozOp hWoz
  replace hWoz := WfRewriter.createOp!_none_some hWoz
  obtain ⟨_, _, _, hWoz⟩ := hWoz
  peelOpCreation hpattern ctx₁₂ sozOp hSoz
  replace hSoz := WfRewriter.createOp!_none_some hSoz
  obtain ⟨_, _, _, hSoz⟩ := hSoz
  peelOpCreation hpattern ctx₁₃ selOp hSel
  replace hSel := WfRewriter.createOp!_none_some hSel
  obtain ⟨_, _, _, hSel⟩ := hSel
  peelOpCreation hpattern ctx₁₄ cbOp hCb
  simp only [replaceWithRegLocal] at hCb
  replace hCb := WfRewriter.createOp!_none_some hCb
  obtain ⟨_, _, _, hCb⟩ := hCb
  cleanupHpattern hpattern
  cleanupHpattern hFinal
  -- `op` stays in bounds through the creations (inputs to the `CtxExtends` witnesses).
  have hOpIn₁ : op.InBounds ctx₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLCast opInBounds
  have hOpIn₂ : op.InBounds ctx₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRCast hOpIn₁
  have hOpIn₃ : op.InBounds ctx₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOne hOpIn₂
  have hOpIn₄ : op.InBounds ctx₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hDiff hOpIn₃
  have hOpIn₅ : op.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hCmp hOpIn₄
  have hOpIn₆ : op.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hDsb hOpIn₅
  have hOpIn₇ : op.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hDs hOpIn₆
  have hOpIn₈ : op.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hIm hOpIn₇
  have hOpIn₉ : op.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOv hOpIn₈
  have hOpIn₁₀ : op.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSat hOpIn₉
  have hOpIn₁₁ : op.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hWoz hOpIn₁₀
  have hOpIn₁₂ : op.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSoz hOpIn₁₁
  have hOpIn₁₃ : op.InBounds ctx₁₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSel hOpIn₁₂
  -- One-step context extensions and their compositions up to the final context `ctx₁₄`.
  have E₁ := CtxExtends.of_createOp (op := op) hLCast opInBounds
  have E₂ := CtxExtends.of_createOp (op := op) hRCast hOpIn₁
  have E₃ := CtxExtends.of_createOp (op := op) hOne hOpIn₂
  have E₄ := CtxExtends.of_createOp (op := op) hDiff hOpIn₃
  have E₅ := CtxExtends.of_createOp (op := op) hCmp hOpIn₄
  have E₆ := CtxExtends.of_createOp (op := op) hDsb hOpIn₅
  have E₇ := CtxExtends.of_createOp (op := op) hDs hOpIn₆
  have E₈ := CtxExtends.of_createOp (op := op) hIm hOpIn₇
  have E₉ := CtxExtends.of_createOp (op := op) hOv hOpIn₈
  have E₁₀ := CtxExtends.of_createOp (op := op) hSat hOpIn₉
  have E₁₁ := CtxExtends.of_createOp (op := op) hWoz hOpIn₁₀
  have E₁₂ := CtxExtends.of_createOp (op := op) hSoz hOpIn₁₁
  have E₁₃ := CtxExtends.of_createOp (op := op) hSel hOpIn₁₂
  have E₁₄ := CtxExtends.of_createOp (op := op) hCb hOpIn₁₃
  have F₁₃ : CtxExtends op ctx₁₃ ctx₁₄ := E₁₄
  have F₁₂ : CtxExtends op ctx₁₂ ctx₁₄ := E₁₃.trans F₁₃
  have F₁₁ : CtxExtends op ctx₁₁ ctx₁₄ := E₁₂.trans F₁₂
  have F₁₀ : CtxExtends op ctx₁₀ ctx₁₄ := E₁₁.trans F₁₁
  have F₉ : CtxExtends op ctx₉ ctx₁₄ := E₁₀.trans F₁₀
  have F₈ : CtxExtends op ctx₈ ctx₁₄ := E₉.trans F₉
  have F₇ : CtxExtends op ctx₇ ctx₁₄ := E₈.trans F₈
  have F₆ : CtxExtends op ctx₆ ctx₁₄ := E₇.trans F₇
  have F₅ : CtxExtends op ctx₅ ctx₁₄ := E₆.trans F₆
  have F₄ : CtxExtends op ctx₄ ctx₁₄ := E₅.trans F₅
  have F₃ : CtxExtends op ctx₃ ctx₁₄ := E₄.trans F₄
  have F₂ : CtxExtends op ctx₂ ctx₁₄ := E₃.trans F₃
  have F₁ : CtxExtends op ctx₁ ctx₁₄ := E₂.trans F₂
  have Ectx : CtxExtends op ctx ctx₁₄ := E₁.trans F₁
  have G₁₃ : CtxExtends op ctx ctx₁₃ :=
    E₁.trans (E₂.trans (E₃.trans (E₄.trans (E₅.trans (E₆.trans (E₇.trans (E₈.trans (E₉.trans
      (E₁₀.trans (E₁₁.trans (E₁₂.trans E₁₃)))))))))))
  -- Read the refined values `xt`/`yt` of `lhs`/`rhs` in the target state `state'`.
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hxVal
      hDomCtxL (Ectx.dominates lhs hDomCtxL) lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRhsIn hyVal
      hDomCtxR (Ectx.dominates rhs hDomCtxR) rNotOp
  -- Normalise the bitwidth to the literal `64`.
  obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
  -- In-bounds facts for the fourteen created ops in their creation contexts.
  have hLCastIn₁ : lcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds lcastOp hLCast
  have hRCastIn₂ : rcastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds rcastOp hRCast
  have hOneIn₃ : oneOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds oneOp hOne
  have hDiffIn₄ : diffOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds diffOp hDiff
  have hCmpIn₅ : cmpOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds cmpOp hCmp
  have hDsbIn₆ : dsbOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds dsbOp hDsb
  have hDsIn₇ : dsOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds dsOp hDs
  have hImIn₈ : imOp.InBounds ctx₈.raw := WfRewriter.createOp_new_inBounds imOp hIm
  have hOvIn₉ : ovOp.InBounds ctx₉.raw := WfRewriter.createOp_new_inBounds ovOp hOv
  have hSatIn₁₀ : satOp.InBounds ctx₁₀.raw := WfRewriter.createOp_new_inBounds satOp hSat
  have hWozIn₁₁ : wozOp.InBounds ctx₁₁.raw := WfRewriter.createOp_new_inBounds wozOp hWoz
  have hSozIn₁₂ : sozOp.InBounds ctx₁₂.raw := WfRewriter.createOp_new_inBounds sozOp hSoz
  have hSelIn₁₃ : selOp.InBounds ctx₁₃.raw := WfRewriter.createOp_new_inBounds selOp hSel
  have hCbIn₁₄ : cbOp.InBounds ctx₁₄.raw := WfRewriter.createOp_new_inBounds cbOp hCb
  -- Structural facts about the fourteen created ops, in the final context.
  have hLCastType : lcastOp.getOpType! ctx₁₄.raw = .builtin .unrealized_conversion_cast := by
    rw [F₁.opType lcastOp hLCastIn₁]; grind
  have hRCastType : rcastOp.getOpType! ctx₁₄.raw = .builtin .unrealized_conversion_cast := by
    rw [F₂.opType rcastOp hRCastIn₂]; grind
  have hOneType : oneOp.getOpType! ctx₁₄.raw = .riscv .li := by
    rw [F₃.opType oneOp hOneIn₃]; grind
  have hDiffType : diffOp.getOpType! ctx₁₄.raw = .riscv .sub := by
    rw [F₄.opType diffOp hDiffIn₄]; grind
  have hCmpType : cmpOp.getOpType! ctx₁₄.raw = .riscv .slt := by
    rw [F₅.opType cmpOp hCmpIn₅]; grind
  have hDsbType : dsbOp.getOpType! ctx₁₄.raw = .riscv .srli := by
    rw [F₆.opType dsbOp hDsbIn₆]; grind
  have hDsType : dsOp.getOpType! ctx₁₄.raw = .riscv .srai := by
    rw [F₇.opType dsOp hDsIn₇]; grind
  have hImType : imOp.getOpType! ctx₁₄.raw = .riscv .slli := by
    rw [F₈.opType imOp hImIn₈]; grind
  have hOvType : ovOp.getOpType! ctx₁₄.raw = .riscv .xor := by
    rw [F₉.opType ovOp hOvIn₉]; grind
  have hSatType : satOp.getOpType! ctx₁₄.raw = .riscv .xor := by
    rw [F₁₀.opType satOp hSatIn₁₀]; grind
  have hWozType : wozOp.getOpType! ctx₁₄.raw = .riscv .czeronez := by
    rw [F₁₁.opType wozOp hWozIn₁₁]; grind
  have hSozType : sozOp.getOpType! ctx₁₄.raw = .riscv .czeroeqz := by
    rw [F₁₂.opType sozOp hSozIn₁₂]; grind
  have hSelType : selOp.getOpType! ctx₁₄.raw = .riscv .or := by
    rw [F₁₃.opType selOp hSelIn₁₃]; grind
  have hCbType : cbOp.getOpType! ctx₁₄.raw = .builtin .unrealized_conversion_cast := by grind
  have hLCastOperands : lcastOp.getOperands! ctx₁₄.raw = #[lhs] := by
    rw [F₁.operands lcastOp hLCastIn₁]; grind
  have hRCastOperands : rcastOp.getOperands! ctx₁₄.raw = #[rhs] := by
    rw [F₂.operands rcastOp hRCastIn₂]; grind
  have hOneOperands : oneOp.getOperands! ctx₁₄.raw = #[] := by
    rw [F₃.operands oneOp hOneIn₃]; grind
  have hDiffOperands : diffOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    rw [F₄.operands diffOp hDiffIn₄]; grind
  have hCmpOperands : cmpOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    rw [F₅.operands cmpOp hCmpIn₅]; grind
  have hDsbOperands : dsbOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (diffOp.getResult 0)] := by
    rw [F₆.operands dsbOp hDsbIn₆]; grind
  have hDsOperands : dsOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (diffOp.getResult 0)] := by
    rw [F₇.operands dsOp hDsIn₇]; grind
  have hImOperands : imOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (oneOp.getResult 0)] := by
    rw [F₈.operands imOp hImIn₈]; grind
  have hOvOperands : ovOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (cmpOp.getResult 0), ValuePtr.opResult (dsbOp.getResult 0)] := by
    rw [F₉.operands ovOp hOvIn₉]; grind
  have hSatOperands : satOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (dsOp.getResult 0), ValuePtr.opResult (imOp.getResult 0)] := by
    rw [F₁₀.operands satOp hSatIn₁₀]; grind
  have hWozOperands : wozOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (diffOp.getResult 0), ValuePtr.opResult (ovOp.getResult 0)] := by
    rw [F₁₁.operands wozOp hWozIn₁₁]; grind
  have hSozOperands : sozOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (satOp.getResult 0), ValuePtr.opResult (ovOp.getResult 0)] := by
    rw [F₁₂.operands sozOp hSozIn₁₂]; grind
  have hSelOperands : selOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (sozOp.getResult 0), ValuePtr.opResult (wozOp.getResult 0)] := by
    rw [F₁₃.operands selOp hSelIn₁₃]; grind
  have hCbOperands : cbOp.getOperands! ctx₁₄.raw
      = #[ValuePtr.opResult (selOp.getResult 0)] := by grind
  have hLCastResTypes : lcastOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁.resultTypes lcastOp hLCastIn₁]; grind
  have hRCastResTypes : rcastOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₂.resultTypes rcastOp hRCastIn₂]; grind
  have hOneResTypes : oneOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₃.resultTypes oneOp hOneIn₃]; grind
  have hDiffResTypes : diffOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₄.resultTypes diffOp hDiffIn₄]; grind
  have hCmpResTypes : cmpOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₅.resultTypes cmpOp hCmpIn₅]; grind
  have hDsbResTypes : dsbOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₆.resultTypes dsbOp hDsbIn₆]; grind
  have hDsResTypes : dsOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₇.resultTypes dsOp hDsIn₇]; grind
  have hImResTypes : imOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₈.resultTypes imOp hImIn₈]; grind
  have hOvResTypes : ovOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₉.resultTypes ovOp hOvIn₉]; grind
  have hSatResTypes : satOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁₀.resultTypes satOp hSatIn₁₀]; grind
  have hWozResTypes : wozOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁₁.resultTypes wozOp hWozIn₁₁]; grind
  have hSozResTypes : sozOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁₂.resultTypes sozOp hSozIn₁₂]; grind
  have hSelResTypes : selOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁₃.resultTypes selOp hSelIn₁₃]; grind
  -- The immediate properties of the `li`/`srli`/`srai`/`slli`.
  have hOneProps : oneOp.getProperties! ctx₁₄.raw (.riscv .li) = mkRISCVImm (-1) := by
    rw [F₃.properties oneOp hOneIn₃,
      OperationPtr.getProperties!_WfRewriter_createOp hOne (operation := oneOp)]
    rw [if_pos rfl]; rfl
  have hDsbProps : dsbOp.getProperties! ctx₁₄.raw (.riscv .srli) = mkRISCVImm 63 := by
    rw [F₆.properties dsbOp hDsbIn₆,
      OperationPtr.getProperties!_WfRewriter_createOp hDsb (operation := dsbOp)]
    rw [if_pos rfl]; rfl
  have hDsbImm : BitVec.ofInt 6 (dsbOp.getProperties! ctx₁₄.raw (.riscv .srli)).value.value
      = BitVec.ofInt 6 63 := by rw [hDsbProps]; simp [mkRISCVImm]
  have hDsProps : dsOp.getProperties! ctx₁₄.raw (.riscv .srai) = mkRISCVImm 63 := by
    rw [F₇.properties dsOp hDsIn₇,
      OperationPtr.getProperties!_WfRewriter_createOp hDs (operation := dsOp)]
    rw [if_pos rfl]; rfl
  have hDsImm : BitVec.ofInt 6 (dsOp.getProperties! ctx₁₄.raw (.riscv .srai)).value.value
      = BitVec.ofInt 6 63 := by rw [hDsProps]; simp [mkRISCVImm]
  have hImProps : imOp.getProperties! ctx₁₄.raw (.riscv .slli) = mkRISCVImm 63 := by
    rw [F₈.properties imOp hImIn₈,
      OperationPtr.getProperties!_WfRewriter_createOp hIm (operation := imOp)]
    rw [if_pos rfl]; rfl
  have hImImm : BitVec.ofInt 6 (imOp.getProperties! ctx₁₄.raw (.riscv .slli)).value.value
      = BitVec.ofInt 6 63 := by rw [hImProps]; simp [mkRISCVImm]
  -- The cast-back op's result type is `i64`.
  have hCBType : ((op.getResult 0).get! ctx₁₃.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw :=
      G₁₃.valueType _ hResIn
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hCbResTypes : cbOp.getResultTypes! ctx₁₄.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
  -- Freshness facts for the frame clauses.
  have hLCastFresh : ¬ lcastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds lcastOp hLCast
  have hRCastFresh : ¬ rcastOp.InBounds ctx₁.raw :=
    WfRewriter.createOp_new_not_inBounds rcastOp hRCast
  have hOneFresh : ¬ oneOp.InBounds ctx₂.raw :=
    WfRewriter.createOp_new_not_inBounds oneOp hOne
  have hDiffFresh : ¬ diffOp.InBounds ctx₃.raw :=
    WfRewriter.createOp_new_not_inBounds diffOp hDiff
  have hCmpFresh : ¬ cmpOp.InBounds ctx₄.raw :=
    WfRewriter.createOp_new_not_inBounds cmpOp hCmp
  have hDsbFresh : ¬ dsbOp.InBounds ctx₅.raw :=
    WfRewriter.createOp_new_not_inBounds dsbOp hDsb
  have hDsFresh : ¬ dsOp.InBounds ctx₆.raw :=
    WfRewriter.createOp_new_not_inBounds dsOp hDs
  have hImFresh : ¬ imOp.InBounds ctx₇.raw :=
    WfRewriter.createOp_new_not_inBounds imOp hIm
  have hOvFresh : ¬ ovOp.InBounds ctx₈.raw :=
    WfRewriter.createOp_new_not_inBounds ovOp hOv
  have hSatFresh : ¬ satOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_new_not_inBounds satOp hSat
  have hWozFresh : ¬ wozOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_new_not_inBounds wozOp hWoz
  have hSozFresh : ¬ sozOp.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_new_not_inBounds sozOp hSoz
  -- In-bounds facts for the fresh op results in the intermediate contexts they must survive to.
  have hXIn₁ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₁.raw :=
    opResult_getResult_inBounds_of_createOp hLCast (by simp)
  have hXIn₂ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₂.raw :=
    E₂.valueInBounds _ hXIn₁
  have hXIn₃ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₃.raw :=
    E₃.valueInBounds _ hXIn₂
  have hYIn₂ : (ValuePtr.opResult (rcastOp.getResult 0)).InBounds ctx₂.raw :=
    opResult_getResult_inBounds_of_createOp hRCast (by simp)
  have hYIn₃ : (ValuePtr.opResult (rcastOp.getResult 0)).InBounds ctx₃.raw :=
    E₃.valueInBounds _ hYIn₂
  have hMIn₃ : (ValuePtr.opResult (oneOp.getResult 0)).InBounds ctx₃.raw :=
    opResult_getResult_inBounds_of_createOp hOne (by simp)
  have hMIn₄ : (ValuePtr.opResult (oneOp.getResult 0)).InBounds ctx₄.raw :=
    E₄.valueInBounds _ hMIn₃
  have hMIn₅ : (ValuePtr.opResult (oneOp.getResult 0)).InBounds ctx₅.raw :=
    E₅.valueInBounds _ hMIn₄
  have hMIn₆ : (ValuePtr.opResult (oneOp.getResult 0)).InBounds ctx₆.raw :=
    E₆.valueInBounds _ hMIn₅
  have hDIFFIn₄ : (ValuePtr.opResult (diffOp.getResult 0)).InBounds ctx₄.raw :=
    opResult_getResult_inBounds_of_createOp hDiff (by simp)
  have hDIFFIn₅ : (ValuePtr.opResult (diffOp.getResult 0)).InBounds ctx₅.raw :=
    E₅.valueInBounds _ hDIFFIn₄
  have hDIFFIn₆ : (ValuePtr.opResult (diffOp.getResult 0)).InBounds ctx₆.raw :=
    E₆.valueInBounds _ hDIFFIn₅
  have hDIFFIn₇ : (ValuePtr.opResult (diffOp.getResult 0)).InBounds ctx₇.raw :=
    E₇.valueInBounds _ hDIFFIn₆
  have hDIFFIn₈ : (ValuePtr.opResult (diffOp.getResult 0)).InBounds ctx₈.raw :=
    E₈.valueInBounds _ hDIFFIn₇
  have hDIFFIn₉ : (ValuePtr.opResult (diffOp.getResult 0)).InBounds ctx₉.raw :=
    E₉.valueInBounds _ hDIFFIn₈
  have hCMPIn₅ : (ValuePtr.opResult (cmpOp.getResult 0)).InBounds ctx₅.raw :=
    opResult_getResult_inBounds_of_createOp hCmp (by simp)
  have hCMPIn₆ : (ValuePtr.opResult (cmpOp.getResult 0)).InBounds ctx₆.raw :=
    E₆.valueInBounds _ hCMPIn₅
  have hCMPIn₇ : (ValuePtr.opResult (cmpOp.getResult 0)).InBounds ctx₇.raw :=
    E₇.valueInBounds _ hCMPIn₆
  have hDSBIn₆ : (ValuePtr.opResult (dsbOp.getResult 0)).InBounds ctx₆.raw :=
    opResult_getResult_inBounds_of_createOp hDsb (by simp)
  have hDSBIn₇ : (ValuePtr.opResult (dsbOp.getResult 0)).InBounds ctx₇.raw :=
    E₇.valueInBounds _ hDSBIn₆
  have hDSIn₇ : (ValuePtr.opResult (dsOp.getResult 0)).InBounds ctx₇.raw :=
    opResult_getResult_inBounds_of_createOp hDs (by simp)
  have hDSIn₈ : (ValuePtr.opResult (dsOp.getResult 0)).InBounds ctx₈.raw :=
    E₈.valueInBounds _ hDSIn₇
  have hIMIn₈ : (ValuePtr.opResult (imOp.getResult 0)).InBounds ctx₈.raw :=
    opResult_getResult_inBounds_of_createOp hIm (by simp)
  have hOVIn₉ : (ValuePtr.opResult (ovOp.getResult 0)).InBounds ctx₉.raw :=
    opResult_getResult_inBounds_of_createOp hOv (by simp)
  have hOVIn₁₀ : (ValuePtr.opResult (ovOp.getResult 0)).InBounds ctx₁₀.raw :=
    E₁₀.valueInBounds _ hOVIn₉
  have hSATIn₁₀ : (ValuePtr.opResult (satOp.getResult 0)).InBounds ctx₁₀.raw :=
    opResult_getResult_inBounds_of_createOp hSat (by simp)
  have hWOZIn₁₁ : (ValuePtr.opResult (wozOp.getResult 0)).InBounds ctx₁₁.raw :=
    opResult_getResult_inBounds_of_createOp hWoz (by simp)
  -- Interpretation tail: execute the fourteen-op list in `state'`. The frame clauses carry earlier
  -- register bindings across later steps; `diff` in particular must survive six intervening ops to
  -- reach the `czeronez`, and `li -1` four to reach the `slli`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state')
      (inBounds := F₁.inBounds lcastOp hLCastIn₁)
      hLCastType hLCastOperands hLCastResTypes hLVal'
  have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 64 yt) := by
    rw [hFrame₁ rhs (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hRhsIn hLCastFresh)]
    exact hRVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁)
      (inBounds := F₂.inBounds rcastOp hRCastIn₂)
      hRCastType hRCastOperands hRCastResTypes hRVal₁
  have hX₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hXIn₁ hRCastFresh)]
    exact hRes₁
  -- `li -1`
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
    interpretOp_riscv_li_forward (state := s₂) (inBounds := F₃.inBounds oneOp hOneIn₃)
      hOneType hOneProps hOneOperands hOneResTypes
  have hM₃ : s₃.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := hRes₃
  have hX₃ : s₃.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hXIn₂ hOneFresh)]
    exact hX₂
  have hY₃ : s₃.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hYIn₂ hOneFresh)]
    exact hRes₂
  -- `diff = sub X Y`
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := F₄.inBounds diffOp hDiffIn₄)
      (f := fun r₁ r₂ => Data.RISCV.sub r₂ r₁) (fun _ _ _ _ => rfl) hDiffType hDiffOperands
      hDiffResTypes hX₃ hY₃
  have hX₄ : s₄.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hXIn₃ hDiffFresh)]
    exact hX₃
  have hY₄ : s₄.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hYIn₃ hDiffFresh)]
    exact hY₃
  have hM₄ : s₄.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hMIn₃ hDiffFresh)]
    exact hM₃
  -- `cmp = slt X Y`  (i.e. `X <s Y`)
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₄) (inBounds := F₅.inBounds cmpOp hCmpIn₅)
      (f := fun r₁ r₂ => Data.RISCV.slt r₂ r₁) (fun _ _ _ _ => rfl) hCmpType hCmpOperands
      hCmpResTypes hX₄ hY₄
  have hM₅ : s₅.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hMIn₄ hCmpFresh)]
    exact hM₄
  have hDIFF₅ : s₅.variables.getVar? (ValuePtr.opResult (diffOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDIFFIn₄ hCmpFresh)]
    exact hRes₄
  -- `diffSignBit = srli 63 diff`
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
    interpretOp_riscv_srli_forward (state := s₅) (inBounds := F₆.inBounds dsbOp hDsbIn₆)
      (k := BitVec.ofInt 6 63) hDsbType hDsbImm hDsbOperands hDsbResTypes hDIFF₅
  have hM₆ : s₆.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hMIn₅ hDsbFresh)]
    exact hM₅
  have hDIFF₆ : s₆.variables.getVar? (ValuePtr.opResult (diffOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDIFFIn₅ hDsbFresh)]
    exact hDIFF₅
  have hCMP₆ : s₆.variables.getVar? (ValuePtr.opResult (cmpOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCMPIn₅ hDsbFresh)]
    exact hRes₅
  -- `diffSign = srai 63 diff`
  obtain ⟨s₇, hI₇, hMem₇, hRes₇, hFrame₇⟩ :=
    interpretOp_riscv_srai_forward (state := s₆) (inBounds := F₇.inBounds dsOp hDsIn₇)
      (k := BitVec.ofInt 6 63) hDsType hDsImm hDsOperands hDsResTypes hDIFF₆
  have hM₇ : s₇.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hMIn₆ hDsFresh)]
    exact hM₆
  have hDIFF₇ : s₇.variables.getVar? (ValuePtr.opResult (diffOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDIFFIn₆ hDsFresh)]
    exact hDIFF₆
  have hCMP₇ : s₇.variables.getVar? (ValuePtr.opResult (cmpOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCMPIn₆ hDsFresh)]
    exact hCMP₆
  have hDSB₇ : s₇.variables.getVar? (ValuePtr.opResult (dsbOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srli (BitVec.ofInt 6 63)
          (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDSBIn₆ hDsFresh)]
    exact hRes₆
  -- `intMin = slli 63 (li -1)`
  obtain ⟨s₈, hI₈, hMem₈, hRes₈, hFrame₈⟩ :=
    interpretOp_riscv_slli_forward (state := s₇) (inBounds := F₈.inBounds imOp hImIn₈)
      (k := BitVec.ofInt 6 63) hImType hImImm hImOperands hImResTypes hM₇
  have hDIFF₈ : s₈.variables.getVar? (ValuePtr.opResult (diffOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₈ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDIFFIn₇ hImFresh)]
    exact hDIFF₇
  have hCMP₈ : s₈.variables.getVar? (ValuePtr.opResult (cmpOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₈ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCMPIn₇ hImFresh)]
    exact hCMP₇
  have hDSB₈ : s₈.variables.getVar? (ValuePtr.opResult (dsbOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srli (BitVec.ofInt 6 63)
          (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₈ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDSBIn₇ hImFresh)]
    exact hDSB₇
  have hDS₈ : s₈.variables.getVar? (ValuePtr.opResult (dsOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srai (BitVec.ofInt 6 63)
          (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₈ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDSIn₇ hImFresh)]
    exact hRes₇
  -- `overflow = xor cmp diffSignBit`
  obtain ⟨s₉, hI₉, hMem₉, hRes₉, hFrame₉⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₈) (inBounds := F₉.inBounds ovOp hOvIn₉)
      (f := fun r₁ r₂ => Data.RISCV.xor r₂ r₁) (fun _ _ _ _ => rfl) hOvType hOvOperands
      hOvResTypes hCMP₈ hDSB₈
  have hDIFF₉ : s₉.variables.getVar? (ValuePtr.opResult (diffOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₉ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDIFFIn₈ hOvFresh)]
    exact hDIFF₈
  have hDS₉ : s₉.variables.getVar? (ValuePtr.opResult (dsOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srai (BitVec.ofInt 6 63)
          (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₉ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDSIn₈ hOvFresh)]
    exact hDS₈
  have hIM₉ : s₉.variables.getVar? (ValuePtr.opResult (imOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.slli (BitVec.ofInt 6 63)
          (Data.RISCV.li (BitVec.ofInt 64 (-1))))) := by
    rw [hFrame₉ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hIMIn₈ hOvFresh)]
    exact hRes₈
  -- `sat = xor diffSign intMin`
  obtain ⟨s₁₀, hI₁₀, hMem₁₀, hRes₁₀, hFrame₁₀⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₉) (inBounds := F₁₀.inBounds satOp hSatIn₁₀)
      (f := fun r₁ r₂ => Data.RISCV.xor r₂ r₁) (fun _ _ _ _ => rfl) hSatType hSatOperands
      hSatResTypes hDS₉ hIM₉
  have hDIFF₁₀ : s₁₀.variables.getVar? (ValuePtr.opResult (diffOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₁₀ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hDIFFIn₉ hSatFresh)]
    exact hDIFF₉
  have hOV₁₀ : s₁₀.variables.getVar? (ValuePtr.opResult (ovOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.xor
          (Data.RISCV.srli (BitVec.ofInt 6 63)
            (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₁₀ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hOVIn₉ hSatFresh)]
    exact hRes₉
  -- `wrappedOrZero = czeronez diff overflow`
  obtain ⟨s₁₁, hI₁₁, hMem₁₁, hRes₁₁, hFrame₁₁⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₁₀) (inBounds := F₁₁.inBounds wozOp hWozIn₁₁)
      (f := fun r₁ r₂ => Data.RISCV.czeronez r₂ r₁) (fun _ _ _ _ => rfl) hWozType hWozOperands
      hWozResTypes hDIFF₁₀ hOV₁₀
  have hOV₁₁ : s₁₁.variables.getVar? (ValuePtr.opResult (ovOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.xor
          (Data.RISCV.srli (BitVec.ofInt 6 63)
            (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₁₁ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hOVIn₁₀ hWozFresh)]
    exact hOV₁₀
  have hSAT₁₁ : s₁₁.variables.getVar? (ValuePtr.opResult (satOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.xor
          (Data.RISCV.slli (BitVec.ofInt 6 63) (Data.RISCV.li (BitVec.ofInt 64 (-1))))
          (Data.RISCV.srai (BitVec.ofInt 6 63)
            (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))))) := by
    rw [hFrame₁₁ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSATIn₁₀ hWozFresh)]
    exact hRes₁₀
  -- `satOrZero = czeroeqz sat overflow`
  obtain ⟨s₁₂, hI₁₂, hMem₁₂, hRes₁₂, hFrame₁₂⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₁₁) (inBounds := F₁₂.inBounds sozOp hSozIn₁₂)
      (f := fun r₁ r₂ => Data.RISCV.czeroeqz r₂ r₁) (fun _ _ _ _ => rfl) hSozType hSozOperands
      hSozResTypes hSAT₁₁ hOV₁₁
  have hWOZ₁₂ : s₁₂.variables.getVar? (ValuePtr.opResult (wozOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.czeronez
          (Data.RISCV.xor
            (Data.RISCV.srli (BitVec.ofInt 6 63)
              (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
            (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₁₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hWOZIn₁₁ hSozFresh)]
    exact hRes₁₁
  -- `select = or satOrZero wrappedOrZero`
  obtain ⟨s₁₃, hI₁₃, hMem₁₃, hRes₁₃, hFrame₁₃⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₁₂) (inBounds := F₁₃.inBounds selOp hSelIn₁₃)
      (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl) hSelType hSelOperands
      hSelResTypes hRes₁₂ hWOZ₁₂
  obtain ⟨s₁₄, hI₁₄, hMem₁₄, hRes₁₄, -⟩ :=
    interpretOp_castBack_forward (state := s₁₃) (inBounds := hCbIn₁₄)
      hCbType hCbOperands hCbResTypes hRes₁₃
  refine ⟨s₁₄, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, hI₈, hI₉, hI₁₀, hI₁₁, hI₁₂,
      hI₁₃, hI₁₄, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.czeronez
            (Data.RISCV.xor
              (Data.RISCV.srli (BitVec.ofInt 6 63)
                (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
            (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.czeroeqz
            (Data.RISCV.xor
              (Data.RISCV.srli (BitVec.ofInt 6 63)
                (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (Data.RISCV.slt (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
            (Data.RISCV.xor
              (Data.RISCV.slli (BitVec.ofInt 6 63) (Data.RISCV.li (BitVec.ofInt 64 (-1))))
              (Data.RISCV.srai (BitVec.ofInt 6 63)
                (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))))) 64)], ?_, ?_⟩
    · simp [hRes₁₄, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using ssubSat_isRefinedBy_toInt hxtRef hytRef⟩

/--
info: 'Veir.ssubSat_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 ssubSat_isRefinedBy_toInt._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms ssubSat_local_preservesSemantics

end Veir
