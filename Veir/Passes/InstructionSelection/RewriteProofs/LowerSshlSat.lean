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
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSsubSat

namespace Veir

/-!
## Correctness of `sshlSat_local`

`llvm.intr.sshl.sat` on a 64-bit integer is lowered to LLVM's RV64+Zicond signed saturating-shl
sequence.  Casting both operands to registers `X = toReg xt`, `Y = toReg yt`, it emits:
`shifted = sll X Y`, `unshifted = sra shifted Y`, `sign = srai 63 X`,
`intMax = srli 1 (li -1)`, `overflow = xor X unshifted` (the shift is lossy iff shifting back
does not recover `X`), `sat = xor sign intMax` (`X < 0 ? INT_MIN : INT_MAX`), then the branchless
select `or (czeronez shifted overflow) (czeroeqz sat overflow)` (`overflow ≠ 0 ? sat : shifted`),
cast back to the integer type.

The chain is the `shl` sibling of `ssubSat_local` (thirteen ops, `i64`-only, no bitwidth branch),
proven in the same `CtxExtends` style — see the header of `LowerSsubSat.lean`.
-/

/-- Correctness of the branchless signed saturating-shl chain: the round trip
    `int × int → reg × reg → sll/li/sra/srai/srli/xor/xor/czeronez/czeroeqz/or → int` refines
    `sshl.sat`.  (`xt`/`yt` are the possibly-more-defined target-side values of the operands.) -/
theorem sshlSat_isRefinedBy_toInt {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.sshlSat x y ⊒
      RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.czeronez
            (Data.RISCV.xor
              (Data.RISCV.sra (LLVM.Int.toReg yt)
                (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (LLVM.Int.toReg xt))
            (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.czeroeqz
            (Data.RISCV.xor
              (Data.RISCV.sra (LLVM.Int.toReg yt)
                (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (LLVM.Int.toReg xt))
            (Data.RISCV.xor
              (Data.RISCV.srli (BitVec.ofInt 6 1) (Data.RISCV.li (BitVec.ofInt 64 (-1))))
              (Data.RISCV.srai (BitVec.ofInt 6 63) (LLVM.Int.toReg xt))))) 64 := by
  revert h₁ h₂
  veir_bv_decide

set_option maxHeartbeats 4000000 in
/-- Correctness of the `sshlSat_local` lowering: the eleven-op RV64+Zicond signed saturating-shl
    chain refines `llvm.intr.sshl.sat`. -/
theorem sshlSat_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics sshlSat_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, sshlSat_local, createRISCVUnitLocal,
    createRISCVImmLocal, signedSatSelectLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchSshlSat op ctx.raw).isSome := by
    cases hM : matchSshlSat op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSshlSat_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_intr__sshl__sat opVerif hOpType
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
  -- Unfold the interpretation of the matched op: exposes the operand values and their `sshlSat`.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold
      (srcFn := fun {_} x y _ => Data.LLVM.Int.sshlSat x y)
      (props := op.getProperties! ctx.raw (.llvm .intr__sshl__sat))
      opInBounds hOpType hNumResults hOperands rfl
      (fun bw x y props rt bo mem res h => by
        have hEq : Llvm.interpretOp' .intr__sshl__sat props rt #[.int bw x, .int bw y] bo mem
            = some (.ok (#[.int bw (Data.LLVM.Int.sshlSat x y)], mem, none)) := by
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
  -- Source value: `op`'s single result is `sshlSat` of its operands.
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
  -- Peel the nine creations before the select block (two casts + `sll`/`li`/`sra`/`srai`/`srli`/
  -- `xor`/`xor`).
  peelOpCreation hpattern ctx₁ lcastOp hLCast
  simp only [castToRegLocal] at hLCast
  replace hLCast := WfRewriter.createOp!_none_some hLCast
  obtain ⟨_, _, _, hLCast⟩ := hLCast
  peelOpCreation hpattern ctx₂ rcastOp hRCast
  simp only [castToRegLocal] at hRCast
  replace hRCast := WfRewriter.createOp!_none_some hRCast
  obtain ⟨_, _, _, hRCast⟩ := hRCast
  peelOpCreation hpattern ctx₃ shOp hSh
  replace hSh := WfRewriter.createOp!_none_some hSh
  obtain ⟨_, _, _, hSh⟩ := hSh
  peelOpCreation hpattern ctx₄ oneOp hOne
  replace hOne := WfRewriter.createOp!_none_some hOne
  obtain ⟨_, _, _, hOne⟩ := hOne
  peelOpCreation hpattern ctx₅ unshOp hUnsh
  replace hUnsh := WfRewriter.createOp!_none_some hUnsh
  obtain ⟨_, _, _, hUnsh⟩ := hUnsh
  peelOpCreation hpattern ctx₆ signOp hSign
  replace hSign := WfRewriter.createOp!_none_some hSign
  obtain ⟨_, _, _, hSign⟩ := hSign
  peelOpCreation hpattern ctx₇ imaxOp hImax
  replace hImax := WfRewriter.createOp!_none_some hImax
  obtain ⟨_, _, _, hImax⟩ := hImax
  peelOpCreation hpattern ctx₈ ovOp hOv
  replace hOv := WfRewriter.createOp!_none_some hOv
  obtain ⟨_, _, _, hOv⟩ := hOv
  peelOpCreation hpattern ctx₉ satOp hSat
  replace hSat := WfRewriter.createOp!_none_some hSat
  obtain ⟨_, _, _, hSat⟩ := hSat
  -- `signedSatSelectLocal` is a *nested* `do` block returning `(ctx, ops, values)`, so its four
  -- creations sit under one extra existential. Open it, peel the four inner creations, and keep
  -- `hFinal` (how the block's result feeds the pattern's return value) for the final cleanup.
  have ⟨⟨ctxSel, selOps, selVals⟩, hSelInner, hFinal⟩ := hpattern
  clear hpattern; have hpattern := hSelInner; clear hSelInner
  peelOpCreation hpattern ctx₁₀ wozOp hWoz
  replace hWoz := WfRewriter.createOp!_none_some hWoz
  obtain ⟨_, _, _, hWoz⟩ := hWoz
  peelOpCreation hpattern ctx₁₁ sozOp hSoz
  replace hSoz := WfRewriter.createOp!_none_some hSoz
  obtain ⟨_, _, _, hSoz⟩ := hSoz
  peelOpCreation hpattern ctx₁₂ selOp hSel
  replace hSel := WfRewriter.createOp!_none_some hSel
  obtain ⟨_, _, _, hSel⟩ := hSel
  peelOpCreation hpattern ctx₁₃ cbOp hCb
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
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSh hOpIn₂
  have hOpIn₄ : op.InBounds ctx₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOne hOpIn₃
  have hOpIn₅ : op.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hUnsh hOpIn₄
  have hOpIn₆ : op.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSign hOpIn₅
  have hOpIn₇ : op.InBounds ctx₇.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hImax hOpIn₆
  have hOpIn₈ : op.InBounds ctx₈.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOv hOpIn₇
  have hOpIn₉ : op.InBounds ctx₉.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSat hOpIn₈
  have hOpIn₁₀ : op.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hWoz hOpIn₉
  have hOpIn₁₁ : op.InBounds ctx₁₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSoz hOpIn₁₀
  have hOpIn₁₂ : op.InBounds ctx₁₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSel hOpIn₁₁
  -- One-step context extensions and their compositions up to the final context `ctx₁₃`.
  have E₁ := CtxExtends.of_createOp (op := op) hLCast opInBounds
  have E₂ := CtxExtends.of_createOp (op := op) hRCast hOpIn₁
  have E₃ := CtxExtends.of_createOp (op := op) hSh hOpIn₂
  have E₄ := CtxExtends.of_createOp (op := op) hOne hOpIn₃
  have E₅ := CtxExtends.of_createOp (op := op) hUnsh hOpIn₄
  have E₆ := CtxExtends.of_createOp (op := op) hSign hOpIn₅
  have E₇ := CtxExtends.of_createOp (op := op) hImax hOpIn₆
  have E₈ := CtxExtends.of_createOp (op := op) hOv hOpIn₇
  have E₉ := CtxExtends.of_createOp (op := op) hSat hOpIn₈
  have E₁₀ := CtxExtends.of_createOp (op := op) hWoz hOpIn₉
  have E₁₁ := CtxExtends.of_createOp (op := op) hSoz hOpIn₁₀
  have E₁₂ := CtxExtends.of_createOp (op := op) hSel hOpIn₁₁
  have E₁₃ := CtxExtends.of_createOp (op := op) hCb hOpIn₁₂
  have F₁₂ : CtxExtends op ctx₁₂ ctx₁₃ := E₁₃
  have F₁₁ : CtxExtends op ctx₁₁ ctx₁₃ := E₁₂.trans F₁₂
  have F₁₀ : CtxExtends op ctx₁₀ ctx₁₃ := E₁₁.trans F₁₁
  have F₉ : CtxExtends op ctx₉ ctx₁₃ := E₁₀.trans F₁₀
  have F₈ : CtxExtends op ctx₈ ctx₁₃ := E₉.trans F₉
  have F₇ : CtxExtends op ctx₇ ctx₁₃ := E₈.trans F₈
  have F₆ : CtxExtends op ctx₆ ctx₁₃ := E₇.trans F₇
  have F₅ : CtxExtends op ctx₅ ctx₁₃ := E₆.trans F₆
  have F₄ : CtxExtends op ctx₄ ctx₁₃ := E₅.trans F₅
  have F₃ : CtxExtends op ctx₃ ctx₁₃ := E₄.trans F₄
  have F₂ : CtxExtends op ctx₂ ctx₁₃ := E₃.trans F₃
  have F₁ : CtxExtends op ctx₁ ctx₁₃ := E₂.trans F₂
  have Ectx : CtxExtends op ctx ctx₁₃ := E₁.trans F₁
  have G₁₂ : CtxExtends op ctx ctx₁₂ :=
    E₁.trans (E₂.trans (E₃.trans (E₄.trans (E₅.trans (E₆.trans (E₇.trans (E₈.trans (E₉.trans
      (E₁₀.trans (E₁₁.trans E₁₂))))))))))
  -- Read the refined values `xt`/`yt` of `lhs`/`rhs` in the target state `state'`.
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hxVal
      hDomCtxL (Ectx.dominates lhs hDomCtxL) lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRhsIn hyVal
      hDomCtxR (Ectx.dominates rhs hDomCtxR) rNotOp
  -- Normalise the bitwidth to the literal `64`.
  obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
  -- In-bounds facts for the thirteen created ops in their creation contexts.
  have hLCastIn₁ : lcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds lcastOp hLCast
  have hRCastIn₂ : rcastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds rcastOp hRCast
  have hShIn₃ : shOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds shOp hSh
  have hOneIn₄ : oneOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds oneOp hOne
  have hUnshIn₅ : unshOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds unshOp hUnsh
  have hSignIn₆ : signOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds signOp hSign
  have hImaxIn₇ : imaxOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds imaxOp hImax
  have hOvIn₈ : ovOp.InBounds ctx₈.raw := WfRewriter.createOp_new_inBounds ovOp hOv
  have hSatIn₉ : satOp.InBounds ctx₉.raw := WfRewriter.createOp_new_inBounds satOp hSat
  have hWozIn₁₀ : wozOp.InBounds ctx₁₀.raw := WfRewriter.createOp_new_inBounds wozOp hWoz
  have hSozIn₁₁ : sozOp.InBounds ctx₁₁.raw := WfRewriter.createOp_new_inBounds sozOp hSoz
  have hSelIn₁₂ : selOp.InBounds ctx₁₂.raw := WfRewriter.createOp_new_inBounds selOp hSel
  have hCbIn₁₃ : cbOp.InBounds ctx₁₃.raw := WfRewriter.createOp_new_inBounds cbOp hCb
  -- Structural facts about the thirteen created ops, in the final context.
  have hLCastType : lcastOp.getOpType! ctx₁₃.raw = .builtin .unrealized_conversion_cast := by
    rw [F₁.opType lcastOp hLCastIn₁]; grind
  have hRCastType : rcastOp.getOpType! ctx₁₃.raw = .builtin .unrealized_conversion_cast := by
    rw [F₂.opType rcastOp hRCastIn₂]; grind
  have hShType : shOp.getOpType! ctx₁₃.raw = .riscv .sll := by
    rw [F₃.opType shOp hShIn₃]; grind
  have hOneType : oneOp.getOpType! ctx₁₃.raw = .riscv .li := by
    rw [F₄.opType oneOp hOneIn₄]; grind
  have hUnshType : unshOp.getOpType! ctx₁₃.raw = .riscv .sra := by
    rw [F₅.opType unshOp hUnshIn₅]; grind
  have hSignType : signOp.getOpType! ctx₁₃.raw = .riscv .srai := by
    rw [F₆.opType signOp hSignIn₆]; grind
  have hImaxType : imaxOp.getOpType! ctx₁₃.raw = .riscv .srli := by
    rw [F₇.opType imaxOp hImaxIn₇]; grind
  have hOvType : ovOp.getOpType! ctx₁₃.raw = .riscv .xor := by
    rw [F₈.opType ovOp hOvIn₈]; grind
  have hSatType : satOp.getOpType! ctx₁₃.raw = .riscv .xor := by
    rw [F₉.opType satOp hSatIn₉]; grind
  have hWozType : wozOp.getOpType! ctx₁₃.raw = .riscv .czeronez := by
    rw [F₁₀.opType wozOp hWozIn₁₀]; grind
  have hSozType : sozOp.getOpType! ctx₁₃.raw = .riscv .czeroeqz := by
    rw [F₁₁.opType sozOp hSozIn₁₁]; grind
  have hSelType : selOp.getOpType! ctx₁₃.raw = .riscv .or := by
    rw [F₁₂.opType selOp hSelIn₁₂]; grind
  have hCbType : cbOp.getOpType! ctx₁₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hLCastOperands : lcastOp.getOperands! ctx₁₃.raw = #[lhs] := by
    rw [F₁.operands lcastOp hLCastIn₁]; grind
  have hRCastOperands : rcastOp.getOperands! ctx₁₃.raw = #[rhs] := by
    rw [F₂.operands rcastOp hRCastIn₂]; grind
  have hShOperands : shOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    rw [F₃.operands shOp hShIn₃]; grind
  have hOneOperands : oneOp.getOperands! ctx₁₃.raw = #[] := by
    rw [F₄.operands oneOp hOneIn₄]; grind
  have hUnshOperands : unshOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (shOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    rw [F₅.operands unshOp hUnshIn₅]; grind
  have hSignOperands : signOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0)] := by
    rw [F₆.operands signOp hSignIn₆]; grind
  have hImaxOperands : imaxOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (oneOp.getResult 0)] := by
    rw [F₇.operands imaxOp hImaxIn₇]; grind
  have hOvOperands : ovOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (unshOp.getResult 0)] := by
    rw [F₈.operands ovOp hOvIn₈]; grind
  have hSatOperands : satOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (signOp.getResult 0), ValuePtr.opResult (imaxOp.getResult 0)] := by
    rw [F₉.operands satOp hSatIn₉]; grind
  have hWozOperands : wozOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (shOp.getResult 0), ValuePtr.opResult (ovOp.getResult 0)] := by
    rw [F₁₀.operands wozOp hWozIn₁₀]; grind
  have hSozOperands : sozOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (satOp.getResult 0), ValuePtr.opResult (ovOp.getResult 0)] := by
    rw [F₁₁.operands sozOp hSozIn₁₁]; grind
  have hSelOperands : selOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (sozOp.getResult 0), ValuePtr.opResult (wozOp.getResult 0)] := by
    rw [F₁₂.operands selOp hSelIn₁₂]; grind
  have hCbOperands : cbOp.getOperands! ctx₁₃.raw
      = #[ValuePtr.opResult (selOp.getResult 0)] := by grind
  have hLCastResTypes : lcastOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁.resultTypes lcastOp hLCastIn₁]; grind
  have hRCastResTypes : rcastOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₂.resultTypes rcastOp hRCastIn₂]; grind
  have hShResTypes : shOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₃.resultTypes shOp hShIn₃]; grind
  have hOneResTypes : oneOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₄.resultTypes oneOp hOneIn₄]; grind
  have hUnshResTypes : unshOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₅.resultTypes unshOp hUnshIn₅]; grind
  have hSignResTypes : signOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₆.resultTypes signOp hSignIn₆]; grind
  have hImaxResTypes : imaxOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₇.resultTypes imaxOp hImaxIn₇]; grind
  have hOvResTypes : ovOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₈.resultTypes ovOp hOvIn₈]; grind
  have hSatResTypes : satOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₉.resultTypes satOp hSatIn₉]; grind
  have hWozResTypes : wozOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁₀.resultTypes wozOp hWozIn₁₀]; grind
  have hSozResTypes : sozOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁₁.resultTypes sozOp hSozIn₁₁]; grind
  have hSelResTypes : selOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [F₁₂.resultTypes selOp hSelIn₁₂]; grind
  -- The immediate properties of the `li`/`srai`/`srli`.
  have hOneProps : oneOp.getProperties! ctx₁₃.raw (.riscv .li) = mkRISCVImm (-1) := by
    rw [F₄.properties oneOp hOneIn₄,
      OperationPtr.getProperties!_WfRewriter_createOp hOne (operation := oneOp)]
    rw [if_pos rfl]; rfl
  have hSignProps : signOp.getProperties! ctx₁₃.raw (.riscv .srai) = mkRISCVImm 63 := by
    rw [F₆.properties signOp hSignIn₆,
      OperationPtr.getProperties!_WfRewriter_createOp hSign (operation := signOp)]
    rw [if_pos rfl]; rfl
  have hSignImm : BitVec.ofInt 6 (signOp.getProperties! ctx₁₃.raw (.riscv .srai)).value.value
      = BitVec.ofInt 6 63 := by rw [hSignProps]; simp [mkRISCVImm]
  have hImaxProps : imaxOp.getProperties! ctx₁₃.raw (.riscv .srli) = mkRISCVImm 1 := by
    rw [F₇.properties imaxOp hImaxIn₇,
      OperationPtr.getProperties!_WfRewriter_createOp hImax (operation := imaxOp)]
    rw [if_pos rfl]; rfl
  have hImaxImm : BitVec.ofInt 6 (imaxOp.getProperties! ctx₁₃.raw (.riscv .srli)).value.value
      = BitVec.ofInt 6 1 := by rw [hImaxProps]; simp [mkRISCVImm]
  -- The cast-back op's result type is `i64`.
  have hCBType : ((op.getResult 0).get! ctx₁₂.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw :=
      G₁₂.valueType _ hResIn
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hCbResTypes : cbOp.getResultTypes! ctx₁₃.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
  -- Freshness facts for the frame clauses.
  have hLCastFresh : ¬ lcastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds lcastOp hLCast
  have hRCastFresh : ¬ rcastOp.InBounds ctx₁.raw :=
    WfRewriter.createOp_new_not_inBounds rcastOp hRCast
  have hShFresh : ¬ shOp.InBounds ctx₂.raw :=
    WfRewriter.createOp_new_not_inBounds shOp hSh
  have hOneFresh : ¬ oneOp.InBounds ctx₃.raw :=
    WfRewriter.createOp_new_not_inBounds oneOp hOne
  have hUnshFresh : ¬ unshOp.InBounds ctx₄.raw :=
    WfRewriter.createOp_new_not_inBounds unshOp hUnsh
  have hSignFresh : ¬ signOp.InBounds ctx₅.raw :=
    WfRewriter.createOp_new_not_inBounds signOp hSign
  have hImaxFresh : ¬ imaxOp.InBounds ctx₆.raw :=
    WfRewriter.createOp_new_not_inBounds imaxOp hImax
  have hOvFresh : ¬ ovOp.InBounds ctx₇.raw :=
    WfRewriter.createOp_new_not_inBounds ovOp hOv
  have hSatFresh : ¬ satOp.InBounds ctx₈.raw :=
    WfRewriter.createOp_new_not_inBounds satOp hSat
  have hWozFresh : ¬ wozOp.InBounds ctx₉.raw :=
    WfRewriter.createOp_new_not_inBounds wozOp hWoz
  have hSozFresh : ¬ sozOp.InBounds ctx₁₀.raw :=
    WfRewriter.createOp_new_not_inBounds sozOp hSoz
  -- In-bounds facts for the fresh op results in the intermediate contexts they must survive to.
  have hXIn₁ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₁.raw :=
    opResult_getResult_inBounds_of_createOp hLCast (by simp)
  have hXIn₂ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₂.raw :=
    E₂.valueInBounds _ hXIn₁
  have hXIn₃ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₃.raw :=
    E₃.valueInBounds _ hXIn₂
  have hXIn₄ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₄.raw :=
    E₄.valueInBounds _ hXIn₃
  have hXIn₅ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₅.raw :=
    E₅.valueInBounds _ hXIn₄
  have hXIn₆ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₆.raw :=
    E₆.valueInBounds _ hXIn₅
  have hYIn₂ : (ValuePtr.opResult (rcastOp.getResult 0)).InBounds ctx₂.raw :=
    opResult_getResult_inBounds_of_createOp hRCast (by simp)
  have hYIn₃ : (ValuePtr.opResult (rcastOp.getResult 0)).InBounds ctx₃.raw :=
    E₃.valueInBounds _ hYIn₂
  have hSHIn₃ : (ValuePtr.opResult (shOp.getResult 0)).InBounds ctx₃.raw :=
    opResult_getResult_inBounds_of_createOp hSh (by simp)
  have hSHIn₄ : (ValuePtr.opResult (shOp.getResult 0)).InBounds ctx₄.raw :=
    E₄.valueInBounds _ hSHIn₃
  have hSHIn₅ : (ValuePtr.opResult (shOp.getResult 0)).InBounds ctx₅.raw :=
    E₅.valueInBounds _ hSHIn₄
  have hSHIn₆ : (ValuePtr.opResult (shOp.getResult 0)).InBounds ctx₆.raw :=
    E₆.valueInBounds _ hSHIn₅
  have hSHIn₇ : (ValuePtr.opResult (shOp.getResult 0)).InBounds ctx₇.raw :=
    E₇.valueInBounds _ hSHIn₆
  have hSHIn₈ : (ValuePtr.opResult (shOp.getResult 0)).InBounds ctx₈.raw :=
    E₈.valueInBounds _ hSHIn₇
  have hMIn₄ : (ValuePtr.opResult (oneOp.getResult 0)).InBounds ctx₄.raw :=
    opResult_getResult_inBounds_of_createOp hOne (by simp)
  have hMIn₅ : (ValuePtr.opResult (oneOp.getResult 0)).InBounds ctx₅.raw :=
    E₅.valueInBounds _ hMIn₄
  have hMIn₆ : (ValuePtr.opResult (oneOp.getResult 0)).InBounds ctx₆.raw :=
    E₆.valueInBounds _ hMIn₅
  have hUNSHIn₅ : (ValuePtr.opResult (unshOp.getResult 0)).InBounds ctx₅.raw :=
    opResult_getResult_inBounds_of_createOp hUnsh (by simp)
  have hUNSHIn₆ : (ValuePtr.opResult (unshOp.getResult 0)).InBounds ctx₆.raw :=
    E₆.valueInBounds _ hUNSHIn₅
  have hSIGNIn₆ : (ValuePtr.opResult (signOp.getResult 0)).InBounds ctx₆.raw :=
    opResult_getResult_inBounds_of_createOp hSign (by simp)
  have hSIGNIn₇ : (ValuePtr.opResult (signOp.getResult 0)).InBounds ctx₇.raw :=
    E₇.valueInBounds _ hSIGNIn₆
  have hIMAXIn₇ : (ValuePtr.opResult (imaxOp.getResult 0)).InBounds ctx₇.raw :=
    opResult_getResult_inBounds_of_createOp hImax (by simp)
  have hOVIn₈ : (ValuePtr.opResult (ovOp.getResult 0)).InBounds ctx₈.raw :=
    opResult_getResult_inBounds_of_createOp hOv (by simp)
  have hOVIn₉ : (ValuePtr.opResult (ovOp.getResult 0)).InBounds ctx₉.raw :=
    E₉.valueInBounds _ hOVIn₈
  have hSATIn₉ : (ValuePtr.opResult (satOp.getResult 0)).InBounds ctx₉.raw :=
    opResult_getResult_inBounds_of_createOp hSat (by simp)
  have hWOZIn₁₀ : (ValuePtr.opResult (wozOp.getResult 0)).InBounds ctx₁₀.raw :=
    opResult_getResult_inBounds_of_createOp hWoz (by simp)
  -- Interpretation tail: execute the thirteen-op list in `state'`. The frame clauses carry earlier
  -- register bindings across later steps; `shifted` in particular must survive five intervening
  -- ops to reach the `czeronez`, and `X` five to reach the overflow `xor`.
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
  -- `shifted = sll X Y`
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := F₃.inBounds shOp hShIn₃)
      (f := fun r₁ r₂ => Data.RISCV.sll r₂ r₁) (fun _ _ _ _ => rfl) hShType hShOperands
      hShResTypes hX₂ hRes₂
  have hX₃ : s₃.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hXIn₂ hShFresh)]
    exact hX₂
  have hY₃ : s₃.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hYIn₂ hShFresh)]
    exact hRes₂
  -- `li -1`
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
    interpretOp_riscv_li_forward (state := s₃) (inBounds := F₄.inBounds oneOp hOneIn₄)
      hOneType hOneProps hOneOperands hOneResTypes
  have hM₄ : s₄.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := hRes₄
  have hX₄ : s₄.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hXIn₃ hOneFresh)]
    exact hX₃
  have hY₄ : s₄.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hYIn₃ hOneFresh)]
    exact hY₃
  have hSH₄ : s₄.variables.getVar? (ValuePtr.opResult (shOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSHIn₃ hOneFresh)]
    exact hRes₃
  -- `unshifted = sra shifted Y`
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₄) (inBounds := F₅.inBounds unshOp hUnshIn₅)
      (f := fun r₁ r₂ => Data.RISCV.sra r₂ r₁) (fun _ _ _ _ => rfl) hUnshType hUnshOperands
      hUnshResTypes hSH₄ hY₄
  have hX₅ : s₅.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hXIn₄ hUnshFresh)]
    exact hX₄
  have hM₅ : s₅.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hMIn₄ hUnshFresh)]
    exact hM₄
  have hSH₅ : s₅.variables.getVar? (ValuePtr.opResult (shOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSHIn₄ hUnshFresh)]
    exact hSH₄
  -- `sign = srai 63 X`
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
    interpretOp_riscv_srai_forward (state := s₅) (inBounds := F₆.inBounds signOp hSignIn₆)
      (k := BitVec.ofInt 6 63) hSignType hSignImm hSignOperands hSignResTypes hX₅
  have hX₆ : s₆.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hXIn₅ hSignFresh)]
    exact hX₅
  have hM₆ : s₆.variables.getVar? (ValuePtr.opResult (oneOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 (-1)))) := by
    rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hMIn₅ hSignFresh)]
    exact hM₅
  have hSH₆ : s₆.variables.getVar? (ValuePtr.opResult (shOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSHIn₅ hSignFresh)]
    exact hSH₅
  have hUNSH₆ : s₆.variables.getVar? (ValuePtr.opResult (unshOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sra (LLVM.Int.toReg yt)
          (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hUNSHIn₅ hSignFresh)]
    exact hRes₅
  -- `intMax = srli 1 (li -1)`
  obtain ⟨s₇, hI₇, hMem₇, hRes₇, hFrame₇⟩ :=
    interpretOp_riscv_srli_forward (state := s₆) (inBounds := F₇.inBounds imaxOp hImaxIn₇)
      (k := BitVec.ofInt 6 1) hImaxType hImaxImm hImaxOperands hImaxResTypes hM₆
  have hX₇ : s₇.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hXIn₆ hImaxFresh)]
    exact hX₆
  have hSH₇ : s₇.variables.getVar? (ValuePtr.opResult (shOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSHIn₆ hImaxFresh)]
    exact hSH₆
  have hUNSH₇ : s₇.variables.getVar? (ValuePtr.opResult (unshOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sra (LLVM.Int.toReg yt)
          (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hUNSHIn₆ hImaxFresh)]
    exact hUNSH₆
  have hSIGN₇ : s₇.variables.getVar? (ValuePtr.opResult (signOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srai (BitVec.ofInt 6 63) (LLVM.Int.toReg xt))) := by
    rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSIGNIn₆ hImaxFresh)]
    exact hRes₆
  -- `overflow = xor X unshifted`
  obtain ⟨s₈, hI₈, hMem₈, hRes₈, hFrame₈⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₇) (inBounds := F₈.inBounds ovOp hOvIn₈)
      (f := fun r₁ r₂ => Data.RISCV.xor r₂ r₁) (fun _ _ _ _ => rfl) hOvType hOvOperands
      hOvResTypes hX₇ hUNSH₇
  have hSH₈ : s₈.variables.getVar? (ValuePtr.opResult (shOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₈ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSHIn₇ hOvFresh)]
    exact hSH₇
  have hSIGN₈ : s₈.variables.getVar? (ValuePtr.opResult (signOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srai (BitVec.ofInt 6 63) (LLVM.Int.toReg xt))) := by
    rw [hFrame₈ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSIGNIn₇ hOvFresh)]
    exact hSIGN₇
  have hIMAX₈ : s₈.variables.getVar? (ValuePtr.opResult (imaxOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.srli (BitVec.ofInt 6 1)
          (Data.RISCV.li (BitVec.ofInt 64 (-1))))) := by
    rw [hFrame₈ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hIMAXIn₇ hOvFresh)]
    exact hRes₇
  -- `sat = xor sign intMax`
  obtain ⟨s₉, hI₉, hMem₉, hRes₉, hFrame₉⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₈) (inBounds := F₉.inBounds satOp hSatIn₉)
      (f := fun r₁ r₂ => Data.RISCV.xor r₂ r₁) (fun _ _ _ _ => rfl) hSatType hSatOperands
      hSatResTypes hSIGN₈ hIMAX₈
  have hSH₉ : s₉.variables.getVar? (ValuePtr.opResult (shOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) := by
    rw [hFrame₉ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSHIn₈ hSatFresh)]
    exact hSH₈
  have hOV₉ : s₉.variables.getVar? (ValuePtr.opResult (ovOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.xor
          (Data.RISCV.sra (LLVM.Int.toReg yt)
            (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (LLVM.Int.toReg xt))) := by
    rw [hFrame₉ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hOVIn₈ hSatFresh)]
    exact hRes₈
  -- `wrappedOrZero = czeronez shifted overflow`
  obtain ⟨s₁₀, hI₁₀, hMem₁₀, hRes₁₀, hFrame₁₀⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₉) (inBounds := F₁₀.inBounds wozOp hWozIn₁₀)
      (f := fun r₁ r₂ => Data.RISCV.czeronez r₂ r₁) (fun _ _ _ _ => rfl) hWozType hWozOperands
      hWozResTypes hSH₉ hOV₉
  have hOV₁₀ : s₁₀.variables.getVar? (ValuePtr.opResult (ovOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.xor
          (Data.RISCV.sra (LLVM.Int.toReg yt)
            (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (LLVM.Int.toReg xt))) := by
    rw [hFrame₁₀ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hOVIn₉ hWozFresh)]
    exact hOV₉
  have hSAT₁₀ : s₁₀.variables.getVar? (ValuePtr.opResult (satOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.xor
          (Data.RISCV.srli (BitVec.ofInt 6 1) (Data.RISCV.li (BitVec.ofInt 64 (-1))))
          (Data.RISCV.srai (BitVec.ofInt 6 63) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₁₀ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hSATIn₉ hWozFresh)]
    exact hRes₉
  -- `satOrZero = czeroeqz sat overflow`
  obtain ⟨s₁₁, hI₁₁, hMem₁₁, hRes₁₁, hFrame₁₁⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₁₀) (inBounds := F₁₁.inBounds sozOp hSozIn₁₁)
      (f := fun r₁ r₂ => Data.RISCV.czeroeqz r₂ r₁) (fun _ _ _ _ => rfl) hSozType hSozOperands
      hSozResTypes hSAT₁₀ hOV₁₀
  have hWOZ₁₁ : s₁₁.variables.getVar? (ValuePtr.opResult (wozOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.czeronez
          (Data.RISCV.xor
            (Data.RISCV.sra (LLVM.Int.toReg yt)
              (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
            (LLVM.Int.toReg xt))
          (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))) := by
    rw [hFrame₁₁ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hWOZIn₁₀ hSozFresh)]
    exact hRes₁₀
  -- `select = or satOrZero wrappedOrZero`
  obtain ⟨s₁₂, hI₁₂, hMem₁₂, hRes₁₂, hFrame₁₂⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₁₁) (inBounds := F₁₂.inBounds selOp hSelIn₁₂)
      (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl) hSelType hSelOperands
      hSelResTypes hRes₁₁ hWOZ₁₁
  obtain ⟨s₁₃, hI₁₃, hMem₁₃, hRes₁₃, -⟩ :=
    interpretOp_castBack_forward (state := s₁₂) (inBounds := hCbIn₁₃)
      hCbType hCbOperands hCbResTypes hRes₁₂
  refine ⟨s₁₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, hI₈, hI₉, hI₁₀, hI₁₁, hI₁₂,
      hI₁₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.czeronez
            (Data.RISCV.xor
              (Data.RISCV.sra (LLVM.Int.toReg yt)
                (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (LLVM.Int.toReg xt))
            (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
          (Data.RISCV.czeroeqz
            (Data.RISCV.xor
              (Data.RISCV.sra (LLVM.Int.toReg yt)
                (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)))
              (LLVM.Int.toReg xt))
            (Data.RISCV.xor
              (Data.RISCV.srli (BitVec.ofInt 6 1) (Data.RISCV.li (BitVec.ofInt 64 (-1))))
              (Data.RISCV.srai (BitVec.ofInt 6 63) (LLVM.Int.toReg xt))))) 64)], ?_, ?_⟩
    · simp [hRes₁₃, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using sshlSat_isRefinedBy_toInt hxtRef hytRef⟩

/--
info: 'Veir.sshlSat_local_preservesSemantics' depends on axioms: [propext,
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
 sshlSat_isRefinedBy_toInt._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms sshlSat_local_preservesSemantics

end Veir
