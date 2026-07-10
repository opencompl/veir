import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.Casting
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRotate
import Veir.Passes.InstructionSelection.RewriteProofs.LowerIcmp

namespace Veir

/-!
## Correctness of `fshlGeneral_local` / `fshrGeneral_local`

The general (distinct-operand) funnel shifts mirror LLVM's `expandFunnelShift`:

    fshl x y z = (x << (z % w)) | ((y >> 1) >> ((w-1) - (z % w)))
    fshr x y z = ((x << 1) << ((w-1) - (z % w))) | (y >> (z % w))

lowered to three `unrealized_conversion_cast`s (all three operands to registers) → `xori _, -1`
(the inverse shift amount `~z`; the hardware masks it modulo the width) → the four shift/or ops
(`W`-suffixed on `i32`) → `unrealized_conversion_cast` back. The nine-op chain is the deepest
linear chain proven so far, so unlike `selectGeneral_local_preservesSemantics` (seven ops) the
structural facts are transported with the `CtxExtends` bundles of `LowerIcmp` instead of
per-fact `grind` seeding, and the operand dominance facts are transported once at the end
(`CtxExtends.dominates`) instead of once per creation.

The data-level refinement lemmas restate `fshlGeneral_refinement`/... from
`InstructionSelection/Proofs.lean` with refined operands (`x ⊒ xt`, …) and in the exact operand
order the interpreter produces (`Riscv.interpretOp'` applies binary data ops as
`RISCV.op op2 op1`, so the final `or` takes `shy` first).
-/

/-! ### Data-level refinement lemmas -/

/-- `fshl x y c ⊒ or shy shx` at `i64`, where `shx = sll c x` and
    `shy = srl (xori (-1) c) (srli 1 y)` (the `expandFunnelShift` shape). -/
theorem fshlGeneral_isRefinedBy_toInt_64 {x y c xt yt ct : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) (h₃ : c ⊒ ct) :
    Data.LLVM.Int.fshl x y c
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.or
            (Data.RISCV.srl (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.srli (BitVec.ofInt 6 1) (LLVM.Int.toReg yt)))
            (Data.RISCV.sll (LLVM.Int.toReg ct) (LLVM.Int.toReg xt))) 64 := by
  revert h₁ h₂ h₃
  veir_bv_decide

/-- `fshl x y c ⊒ or shy shx` at `i32`, with the `w`-suffixed shifts (which mask the amount
    modulo 32; only the low 32 bits of the `or` are observed). -/
theorem fshlGeneral_isRefinedBy_toInt_32 {x y c xt yt ct : Data.LLVM.Int 32}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) (h₃ : c ⊒ ct) :
    Data.LLVM.Int.fshl x y c
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.or
            (Data.RISCV.srlw (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.srliw (BitVec.ofInt 5 1) (LLVM.Int.toReg yt)))
            (Data.RISCV.sllw (LLVM.Int.toReg ct) (LLVM.Int.toReg xt))) 32 := by
  revert h₁ h₂ h₃
  veir_bv_decide

/-- `fshr x y c ⊒ or shy shx` at `i64`, where `shx = sll (xori (-1) c) (slli 1 x)` and
    `shy = srl c y` (the `expandFunnelShift` shape). -/
theorem fshrGeneral_isRefinedBy_toInt_64 {x y c xt yt ct : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) (h₃ : c ⊒ ct) :
    Data.LLVM.Int.fshr x y c
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.or
            (Data.RISCV.srl (LLVM.Int.toReg ct) (LLVM.Int.toReg yt))
            (Data.RISCV.sll (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.slli (BitVec.ofInt 6 1) (LLVM.Int.toReg xt)))) 64 := by
  revert h₁ h₂ h₃
  veir_bv_decide

/-- `fshr x y c ⊒ or shy shx` at `i32`, with the `w`-suffixed shifts. -/
theorem fshrGeneral_isRefinedBy_toInt_32 {x y c xt yt ct : Data.LLVM.Int 32}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) (h₃ : c ⊒ ct) :
    Data.LLVM.Int.fshr x y c
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.or
            (Data.RISCV.srlw (LLVM.Int.toReg ct) (LLVM.Int.toReg yt))
            (Data.RISCV.sllw (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.slliw (BitVec.ofInt 5 1) (LLVM.Int.toReg xt)))) 32 := by
  revert h₁ h₂ h₃
  veir_bv_decide

/-- The first result of a freshly created op (with at least one result type) is in bounds in the
    creation's output context. Proven once here so the nine-creation proofs below can use it as a
    term: the equivalent inline `grind` blows its E-matching budget in their large contexts. -/
theorem opResult_getResult_inBounds_of_createOp
    {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr} {opType : OpCode}
    {resultTypes operands blockOperands regions} {properties : HasOpInfo.propertiesOf opType}
    {hoper hblock hreg hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties none
      hoper hblock hreg hins = some (ctx', newOp))
    (hsize : 0 < resultTypes.size) :
    (ValuePtr.opResult (newOp.getResult 0)).InBounds ctx'.raw := by
  grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]

/-! ### Correctness of `fshlGeneral_local` -/

set_option maxHeartbeats 3200000 in
/-- Correctness of the `fshlGeneral_local` lowering: the
    `castToReg ×3 → xori -1 → sll/sllw → srli/srliw 1 → srl/srlw → or → castBack` round trip
    refines `llvm.intr.fshl x y z` on `i64`/`i32`. -/
theorem fshlGeneral_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics fshlGeneral_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, fshlGeneral_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the `matchFshl` matcher.
  have hMatchSome : (matchFshl op ctx.raw).isSome := by
    cases hM : matchFshl op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, b, amt⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchFshl_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type, hOp2Type⟩ :=
    OperationPtr.Verified.llvm_intr__fshl opVerif hOpType
  have hAEq : a = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hBEq : b = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hAmtEq : amt = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = a := by
    rw [hAEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = b := by
    rw [hBEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = amt := by
    rw [hAmtEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hAType : (a.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hBType : (b.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hAmtType : (amt.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, hOp2Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  -- The validity proof for the (integer) result type, reused for the fresh `TypeAttr`s below.
  have isT : Attribute.isType (Attribute.integerType intType) :=
    hResTypeVal ▸ (((op.getResult 0).get! ctx.raw).type).2
  -- Resolve the result-type-destructuring match on `intType`.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- The bitwidth guard must be false (else the RHS would be `some (ctx, none)`).
  peelSplittableCondition [hBw] hpattern
  -- Unfold the interpretation of the matched `fshl`: exposes the three operand values.
  obtain ⟨xa, xb, xc, haVal, hbVal, hcVal, hMem, hRes, hCf⟩ :=
    matchTernaryOp_interpretOp_unfold (srcFn := fun {_} x y z => Data.LLVM.Int.fshl x y z)
      opInBounds hOpType hNumResults hOperands
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hinterp hAType hBType hAmtType
  subst hCf
  -- In-bounds and dominance facts for the three operands, established before any op creation.
  have hAIn : a.InBounds ctx.raw := by grind
  have hBIn : b.InBounds ctx.raw := by grind
  have hCIn : amt.InBounds ctx.raw := by grind
  have hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  have hDomCtxA : a.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxB : b.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxC : amt.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `fshl` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have aNotOp : ¬ a ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have bNotOp : ¬ b ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have cNotOp : ¬ amt ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the four shared creations (three casts and the `xori`). Dominance and structural facts
  -- are transported once at the end via `CtxExtends`, so the plain peel suffices.
  peelOpCreation hpattern ctx₁ xCastOp hXCast
  simp only [castToRegLocal] at hXCast
  replace hXCast := WfRewriter.createOp!_none_some hXCast
  obtain ⟨_, _, _, hXCast⟩ := hXCast
  peelOpCreation hpattern ctx₂ yCastOp hYCast
  simp only [castToRegLocal] at hYCast
  replace hYCast := WfRewriter.createOp!_none_some hYCast
  obtain ⟨_, _, _, hYCast⟩ := hYCast
  peelOpCreation hpattern ctx₃ zCastOp hZCast
  simp only [castToRegLocal] at hZCast
  replace hZCast := WfRewriter.createOp!_none_some hZCast
  obtain ⟨_, _, _, hZCast⟩ := hZCast
  peelOpCreation hpattern ctx₄ notzOp hNotz
  replace hNotz := WfRewriter.createOp!_none_some hNotz
  obtain ⟨_, _, _, hNotz⟩ := hNotz
  -- Branch on the result bitwidth.
  have hBwCases : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  rcases hBwCases with hbw | hbw
  · -- ===== 64-bit case: `sll`/`srli`/`srl`/`or` =====
    rw [if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    simp only [] at hpattern
    peelOpCreation hpattern ctx₅ shxOp hShx
    replace hShx := WfRewriter.createOp!_none_some hShx
    obtain ⟨_, _, _, hShx⟩ := hShx
    peelOpCreation hpattern ctx₆ y1Op hY1
    replace hY1 := WfRewriter.createOp!_none_some hY1
    obtain ⟨_, _, _, hY1⟩ := hY1
    peelOpCreation hpattern ctx₇ shyOp hShy
    replace hShy := WfRewriter.createOp!_none_some hShy
    obtain ⟨_, _, _, hShy⟩ := hShy
    peelOpCreation hpattern ctx₈ orOp hOr
    replace hOr := WfRewriter.createOp!_none_some hOr
    obtain ⟨_, _, _, hOr⟩ := hOr
    peelOpCreation hpattern ctx₉ castBackOp hCastBack
    simp only [replaceWithRegLocal] at hCastBack
    replace hCastBack := WfRewriter.createOp!_none_some hCastBack
    obtain ⟨_, _, _, hCastBack⟩ := hCastBack
    cleanupHpattern hpattern
    -- `op` stays in bounds through the creations (inputs to the `CtxExtends` witnesses).
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hXCast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hYCast hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hZCast hOpIn₂
    have hOpIn₄ : op.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hNotz hOpIn₃
    have hOpIn₅ : op.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hShx hOpIn₄
    have hOpIn₆ : op.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hY1 hOpIn₅
    have hOpIn₇ : op.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hShy hOpIn₆
    have hOpIn₈ : op.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOr hOpIn₇
    -- One-step context extensions and their compositions up to the final context `ctx₉`.
    have E₁ := CtxExtends.of_createOp (op := op) hXCast opInBounds
    have E₂ := CtxExtends.of_createOp (op := op) hYCast hOpIn₁
    have E₃ := CtxExtends.of_createOp (op := op) hZCast hOpIn₂
    have E₄ := CtxExtends.of_createOp (op := op) hNotz hOpIn₃
    have E₅ := CtxExtends.of_createOp (op := op) hShx hOpIn₄
    have E₆ := CtxExtends.of_createOp (op := op) hY1 hOpIn₅
    have E₇ := CtxExtends.of_createOp (op := op) hShy hOpIn₆
    have E₈ := CtxExtends.of_createOp (op := op) hOr hOpIn₇
    have E₉ := CtxExtends.of_createOp (op := op) hCastBack hOpIn₈
    have F₈ : CtxExtends op ctx₈ ctx₉ := E₉
    have F₇ : CtxExtends op ctx₇ ctx₉ := E₈.trans F₈
    have F₆ : CtxExtends op ctx₆ ctx₉ := E₇.trans F₇
    have F₅ : CtxExtends op ctx₅ ctx₉ := E₆.trans F₆
    have F₄ : CtxExtends op ctx₄ ctx₉ := E₅.trans F₅
    have F₃ : CtxExtends op ctx₃ ctx₉ := E₄.trans F₄
    have F₂ : CtxExtends op ctx₂ ctx₉ := E₃.trans F₃
    have F₁ : CtxExtends op ctx₁ ctx₉ := E₂.trans F₂
    have Ectx : CtxExtends op ctx ctx₉ := E₁.trans F₁
    have G₈ : CtxExtends op ctx ctx₈ :=
      E₁.trans (E₂.trans (E₃.trans (E₄.trans (E₅.trans (E₆.trans (E₇.trans E₈))))))
    -- Read the refined values `xt`/`yt`/`ct` of `a`/`b`/`amt` in the target state `state'`.
    obtain ⟨xt, hAVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hAIn haVal
        hDomCtxA (Ectx.dominates a hDomCtxA) aNotOp
    obtain ⟨yt, hBVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hBIn hbVal
        hDomCtxB (Ectx.dominates b hDomCtxB) bNotOp
    obtain ⟨ct, hCVal', hctRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hCIn hcVal
        hDomCtxC (Ectx.dominates amt hDomCtxC) cNotOp
    -- Normalise the bitwidth to the literal `64`.
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- In-bounds facts for the nine created ops in their creation contexts.
    have hXCastIn₁ : xCastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds xCastOp hXCast
    have hYCastIn₂ : yCastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds yCastOp hYCast
    have hZCastIn₃ : zCastOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds zCastOp hZCast
    have hNotzIn₄ : notzOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds notzOp hNotz
    have hShxIn₅ : shxOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds shxOp hShx
    have hY1In₆ : y1Op.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds y1Op hY1
    have hShyIn₇ : shyOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds shyOp hShy
    have hOrIn₈ : orOp.InBounds ctx₈.raw := WfRewriter.createOp_new_inBounds orOp hOr
    have hCBIn₉ : castBackOp.InBounds ctx₉.raw :=
      WfRewriter.createOp_new_inBounds castBackOp hCastBack
    -- Structural facts about the nine created ops, in the final context.
    have hXCastType : xCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType xCastOp hXCastIn₁]; grind
    have hYCastType : yCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType yCastOp hYCastIn₂]; grind
    have hZCastType : zCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₃.opType zCastOp hZCastIn₃]; grind
    have hNotzType : notzOp.getOpType! ctx₉.raw = .riscv .xori := by
      rw [F₄.opType notzOp hNotzIn₄]; grind
    have hShxType : shxOp.getOpType! ctx₉.raw = .riscv .sll := by
      rw [F₅.opType shxOp hShxIn₅]; grind
    have hY1Type : y1Op.getOpType! ctx₉.raw = .riscv .srli := by
      rw [F₆.opType y1Op hY1In₆]; grind
    have hShyType : shyOp.getOpType! ctx₉.raw = .riscv .srl := by
      rw [F₇.opType shyOp hShyIn₇]; grind
    have hOrType : orOp.getOpType! ctx₉.raw = .riscv .or := by
      rw [F₈.opType orOp hOrIn₈]; grind
    have hCastBackType : castBackOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hXCastOperands : xCastOp.getOperands! ctx₉.raw = #[a] := by
      rw [F₁.operands xCastOp hXCastIn₁]; grind
    have hYCastOperands : yCastOp.getOperands! ctx₉.raw = #[b] := by
      rw [F₂.operands yCastOp hYCastIn₂]; grind
    have hZCastOperands : zCastOp.getOperands! ctx₉.raw = #[amt] := by
      rw [F₃.operands zCastOp hZCastIn₃]; grind
    have hNotzOperands :
        notzOp.getOperands! ctx₉.raw = #[ValuePtr.opResult (zCastOp.getResult 0)] := by
      rw [F₄.operands notzOp hNotzIn₄]; grind
    have hShxOperands : shxOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (xCastOp.getResult 0), ValuePtr.opResult (zCastOp.getResult 0)] := by
      rw [F₅.operands shxOp hShxIn₅]; grind
    have hY1Operands :
        y1Op.getOperands! ctx₉.raw = #[ValuePtr.opResult (yCastOp.getResult 0)] := by
      rw [F₆.operands y1Op hY1In₆]; grind
    have hShyOperands : shyOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (y1Op.getResult 0), ValuePtr.opResult (notzOp.getResult 0)] := by
      rw [F₇.operands shyOp hShyIn₇]; grind
    have hOrOperands : orOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (shxOp.getResult 0), ValuePtr.opResult (shyOp.getResult 0)] := by
      rw [F₈.operands orOp hOrIn₈]; grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₉.raw = #[ValuePtr.opResult (orOp.getResult 0)] := by grind
    have hXCastResTypes : xCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes xCastOp hXCastIn₁]; grind
    have hYCastResTypes : yCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes yCastOp hYCastIn₂]; grind
    have hZCastResTypes : zCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₃.resultTypes zCastOp hZCastIn₃]; grind
    have hNotzResTypes : notzOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₄.resultTypes notzOp hNotzIn₄]; grind
    have hShxResTypes : shxOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₅.resultTypes shxOp hShxIn₅]; grind
    have hY1ResTypes : y1Op.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₆.resultTypes y1Op hY1In₆]; grind
    have hShyResTypes : shyOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₇.resultTypes shyOp hShyIn₇]; grind
    have hOrResTypes : orOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₈.resultTypes orOp hOrIn₈]; grind
    -- The immediate properties of the `xori` and `srli`.
    have hNotzProps : notzOp.getProperties! ctx₉.raw (.riscv .xori)
        = RISCVImmediateProperties.mk (IntegerAttr.mk (-1) (IntegerType.mk 64)) := by
      rw [F₄.properties notzOp hNotzIn₄]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hNotz (operation := notzOp)]
    have hY1Props : y1Op.getProperties! ctx₉.raw (.riscv .srli)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)) := by
      rw [F₆.properties y1Op hY1In₆]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hY1 (operation := y1Op)]
    -- The cast-back op's result type is `i64`.
    have hCBType : ((op.getResult 0).get! ctx₈.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₈.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw :=
        G₈.valueType _ hResIn
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.integerType { bitwidth := 64 }, isT⟩] := by grind
    -- Freshness facts (non-membership in results) for the frame clauses, each built from a
    -- context where the value already exists but the interfering op is not yet created.
    have hXCastFresh : ¬ xCastOp.InBounds ctx.raw :=
      WfRewriter.createOp_new_not_inBounds xCastOp hXCast
    have hYCastFresh : ¬ yCastOp.InBounds ctx₁.raw :=
      WfRewriter.createOp_new_not_inBounds yCastOp hYCast
    have hZCastFresh : ¬ zCastOp.InBounds ctx₂.raw :=
      WfRewriter.createOp_new_not_inBounds zCastOp hZCast
    have hNotzFresh : ¬ notzOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_new_not_inBounds notzOp hNotz
    have hShxFresh : ¬ shxOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_new_not_inBounds shxOp hShx
    have hY1Fresh : ¬ y1Op.InBounds ctx₅.raw :=
      WfRewriter.createOp_new_not_inBounds y1Op hY1
    have hShyFresh : ¬ shyOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_new_not_inBounds shyOp hShy
    -- In-bounds facts for the fresh cast/op results in intermediate contexts.
    have hXResIn₁ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₁.raw :=
      opResult_getResult_inBounds_of_createOp hXCast (by simp)
    have hXResIn₂ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₂.raw :=
      E₂.valueInBounds _ hXResIn₁
    have hXResIn₃ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₃.raw :=
      E₃.valueInBounds _ hXResIn₂
    have hYResIn₂ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₂.raw :=
      opResult_getResult_inBounds_of_createOp hYCast (by simp)
    have hYResIn₃ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₃.raw :=
      E₃.valueInBounds _ hYResIn₂
    have hYResIn₄ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₄.raw :=
      E₄.valueInBounds _ hYResIn₃
    have hZResIn₃ : (ValuePtr.opResult (zCastOp.getResult 0)).InBounds ctx₃.raw :=
      opResult_getResult_inBounds_of_createOp hZCast (by simp)
    have hNotzResIn₄ : (ValuePtr.opResult (notzOp.getResult 0)).InBounds ctx₄.raw :=
      opResult_getResult_inBounds_of_createOp hNotz (by simp)
    have hNotzResIn₅ : (ValuePtr.opResult (notzOp.getResult 0)).InBounds ctx₅.raw :=
      E₅.valueInBounds _ hNotzResIn₄
    have hShxResIn₅ : (ValuePtr.opResult (shxOp.getResult 0)).InBounds ctx₅.raw :=
      opResult_getResult_inBounds_of_createOp hShx (by simp)
    have hShxResIn₆ : (ValuePtr.opResult (shxOp.getResult 0)).InBounds ctx₆.raw :=
      E₆.valueInBounds _ hShxResIn₅
    -- Interpretation tail: `[xCast, yCast, zCast, notz, shx, y1, shy, or, castBack]` in `state'`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state')
        (inBounds := F₁.inBounds xCastOp hXCastIn₁)
        hXCastType hXCastOperands hXCastResTypes hAVal'
    have hBVal₁ : s₁.variables.getVar? b = some (RuntimeValue.int 64 yt) := by
      rw [hFrame₁ b (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hBIn hXCastFresh)]
      exact hBVal'
    have hCVal₁ : s₁.variables.getVar? amt = some (RuntimeValue.int 64 ct) := by
      rw [hFrame₁ amt (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCIn hXCastFresh)]
      exact hCVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁)
        (inBounds := F₂.inBounds yCastOp hYCastIn₂)
        hYCastType hYCastOperands hYCastResTypes hBVal₁
    have hCVal₂ : s₂.variables.getVar? amt = some (RuntimeValue.int 64 ct) := by
      rw [hFrame₂ amt (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        (E₁.valueInBounds amt hCIn) hYCastFresh)]
      exact hCVal₁
    have hXRes₂ : s₂.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₁ hYCastFresh)]
      exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_castToReg_forward (state := s₂)
        (inBounds := F₃.inBounds zCastOp hZCastIn₃)
        hZCastType hZCastOperands hZCastResTypes hCVal₂
    have hXRes₃ : s₃.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₂ hZCastFresh)]
      exact hXRes₂
    have hYRes₃ : s₃.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₂ hZCastFresh)]
      exact hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₃)
        (inBounds := F₄.inBounds notzOp hNotzIn₄)
        (res := Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hNotzType hNotzProps hNotzOperands hNotzResTypes hRes₃
    have hXRes₄ : s₄.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₃ hNotzFresh)]
      exact hXRes₃
    have hYRes₄ : s₄.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₃ hNotzFresh)]
      exact hYRes₃
    have hZRes₄ : s₄.variables.getVar? (ValuePtr.opResult (zCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg ct)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hZResIn₃ hNotzFresh)]
      exact hRes₃
    obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₄)
        (inBounds := F₅.inBounds shxOp hShxIn₅)
        (f := fun r₁ r₂ => Data.RISCV.sll r₂ r₁) (fun _ _ _ _ => rfl)
        hShxType hShxOperands hShxResTypes hXRes₄ hZRes₄
    have hYRes₅ : s₅.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₄ hShxFresh)]
      exact hYRes₄
    have hNotzRes₅ : s₅.variables.getVar? (ValuePtr.opResult (notzOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hNotzResIn₄ hShxFresh)]
      exact hRes₄
    obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₅)
        (inBounds := F₆.inBounds y1Op hY1In₆)
        (res := Data.RISCV.srli (BitVec.ofInt 6 1) (LLVM.Int.toReg yt))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hY1Type hY1Props hY1Operands hY1ResTypes hYRes₅
    have hNotzRes₆ : s₆.variables.getVar? (ValuePtr.opResult (notzOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))) := by
      rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hNotzResIn₅ hY1Fresh)]
      exact hNotzRes₅
    obtain ⟨s₇, hI₇, hMem₇, hRes₇, hFrame₇⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₆)
        (inBounds := F₇.inBounds shyOp hShyIn₇)
        (f := fun r₁ r₂ => Data.RISCV.srl r₂ r₁) (fun _ _ _ _ => rfl)
        hShyType hShyOperands hShyResTypes hRes₆ hNotzRes₆
    have hShxRes₇ : s₇.variables.getVar? (ValuePtr.opResult (shxOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.sll (LLVM.Int.toReg ct) (LLVM.Int.toReg xt))) := by
      rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hShxResIn₆ hShyFresh),
        hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hShxResIn₅ hY1Fresh)]
      exact hRes₅
    obtain ⟨s₈, hI₈, hMem₈, hRes₈, hFrame₈⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₇)
        (inBounds := F₈.inBounds orOp hOrIn₈)
        (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl)
        hOrType hOrOperands hOrResTypes hShxRes₇ hRes₇
    obtain ⟨s₉, hI₉, hMem₉, hRes₉, -⟩ :=
      interpretOp_castBack_forward (state := s₈) (inBounds := hCBIn₉)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₈
    refine ⟨s₉, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, hI₈, hI₉, liftM, monadLift,
        MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
          (Data.RISCV.or
            (Data.RISCV.srl (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.srli (BitVec.ofInt 6 1) (LLVM.Int.toReg yt)))
            (Data.RISCV.sll (LLVM.Int.toReg ct) (LLVM.Int.toReg xt))) 64)], ?_, ?_⟩
      · simp [hRes₉, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using fshlGeneral_isRefinedBy_toInt_64 hxtRef hytRef hctRef⟩
  · -- ===== 32-bit case: `sllw`/`srliw`/`srlw`/`or` =====
    rw [if_pos hbw] at hpattern
    simp only [] at hpattern
    peelOpCreation hpattern ctx₅ shxOp hShx
    replace hShx := WfRewriter.createOp!_none_some hShx
    obtain ⟨_, _, _, hShx⟩ := hShx
    peelOpCreation hpattern ctx₆ y1Op hY1
    replace hY1 := WfRewriter.createOp!_none_some hY1
    obtain ⟨_, _, _, hY1⟩ := hY1
    peelOpCreation hpattern ctx₇ shyOp hShy
    replace hShy := WfRewriter.createOp!_none_some hShy
    obtain ⟨_, _, _, hShy⟩ := hShy
    peelOpCreation hpattern ctx₈ orOp hOr
    replace hOr := WfRewriter.createOp!_none_some hOr
    obtain ⟨_, _, _, hOr⟩ := hOr
    peelOpCreation hpattern ctx₉ castBackOp hCastBack
    simp only [replaceWithRegLocal] at hCastBack
    replace hCastBack := WfRewriter.createOp!_none_some hCastBack
    obtain ⟨_, _, _, hCastBack⟩ := hCastBack
    cleanupHpattern hpattern
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hXCast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hYCast hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hZCast hOpIn₂
    have hOpIn₄ : op.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hNotz hOpIn₃
    have hOpIn₅ : op.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hShx hOpIn₄
    have hOpIn₆ : op.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hY1 hOpIn₅
    have hOpIn₇ : op.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hShy hOpIn₆
    have hOpIn₈ : op.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOr hOpIn₇
    have E₁ := CtxExtends.of_createOp (op := op) hXCast opInBounds
    have E₂ := CtxExtends.of_createOp (op := op) hYCast hOpIn₁
    have E₃ := CtxExtends.of_createOp (op := op) hZCast hOpIn₂
    have E₄ := CtxExtends.of_createOp (op := op) hNotz hOpIn₃
    have E₅ := CtxExtends.of_createOp (op := op) hShx hOpIn₄
    have E₆ := CtxExtends.of_createOp (op := op) hY1 hOpIn₅
    have E₇ := CtxExtends.of_createOp (op := op) hShy hOpIn₆
    have E₈ := CtxExtends.of_createOp (op := op) hOr hOpIn₇
    have E₉ := CtxExtends.of_createOp (op := op) hCastBack hOpIn₈
    have F₈ : CtxExtends op ctx₈ ctx₉ := E₉
    have F₇ : CtxExtends op ctx₇ ctx₉ := E₈.trans F₈
    have F₆ : CtxExtends op ctx₆ ctx₉ := E₇.trans F₇
    have F₅ : CtxExtends op ctx₅ ctx₉ := E₆.trans F₆
    have F₄ : CtxExtends op ctx₄ ctx₉ := E₅.trans F₅
    have F₃ : CtxExtends op ctx₃ ctx₉ := E₄.trans F₄
    have F₂ : CtxExtends op ctx₂ ctx₉ := E₃.trans F₃
    have F₁ : CtxExtends op ctx₁ ctx₉ := E₂.trans F₂
    have Ectx : CtxExtends op ctx ctx₉ := E₁.trans F₁
    have G₈ : CtxExtends op ctx ctx₈ :=
      E₁.trans (E₂.trans (E₃.trans (E₄.trans (E₅.trans (E₆.trans (E₇.trans E₈))))))
    obtain ⟨xt, hAVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hAIn haVal
        hDomCtxA (Ectx.dominates a hDomCtxA) aNotOp
    obtain ⟨yt, hBVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hBIn hbVal
        hDomCtxB (Ectx.dominates b hDomCtxB) bNotOp
    obtain ⟨ct, hCVal', hctRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hCIn hcVal
        hDomCtxC (Ectx.dominates amt hDomCtxC) cNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    have hXCastIn₁ : xCastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds xCastOp hXCast
    have hYCastIn₂ : yCastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds yCastOp hYCast
    have hZCastIn₃ : zCastOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds zCastOp hZCast
    have hNotzIn₄ : notzOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds notzOp hNotz
    have hShxIn₅ : shxOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds shxOp hShx
    have hY1In₆ : y1Op.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds y1Op hY1
    have hShyIn₇ : shyOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds shyOp hShy
    have hOrIn₈ : orOp.InBounds ctx₈.raw := WfRewriter.createOp_new_inBounds orOp hOr
    have hCBIn₉ : castBackOp.InBounds ctx₉.raw :=
      WfRewriter.createOp_new_inBounds castBackOp hCastBack
    have hXCastType : xCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType xCastOp hXCastIn₁]; grind
    have hYCastType : yCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType yCastOp hYCastIn₂]; grind
    have hZCastType : zCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₃.opType zCastOp hZCastIn₃]; grind
    have hNotzType : notzOp.getOpType! ctx₉.raw = .riscv .xori := by
      rw [F₄.opType notzOp hNotzIn₄]; grind
    have hShxType : shxOp.getOpType! ctx₉.raw = .riscv .sllw := by
      rw [F₅.opType shxOp hShxIn₅]; grind
    have hY1Type : y1Op.getOpType! ctx₉.raw = .riscv .srliw := by
      rw [F₆.opType y1Op hY1In₆]; grind
    have hShyType : shyOp.getOpType! ctx₉.raw = .riscv .srlw := by
      rw [F₇.opType shyOp hShyIn₇]; grind
    have hOrType : orOp.getOpType! ctx₉.raw = .riscv .or := by
      rw [F₈.opType orOp hOrIn₈]; grind
    have hCastBackType : castBackOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hXCastOperands : xCastOp.getOperands! ctx₉.raw = #[a] := by
      rw [F₁.operands xCastOp hXCastIn₁]; grind
    have hYCastOperands : yCastOp.getOperands! ctx₉.raw = #[b] := by
      rw [F₂.operands yCastOp hYCastIn₂]; grind
    have hZCastOperands : zCastOp.getOperands! ctx₉.raw = #[amt] := by
      rw [F₃.operands zCastOp hZCastIn₃]; grind
    have hNotzOperands :
        notzOp.getOperands! ctx₉.raw = #[ValuePtr.opResult (zCastOp.getResult 0)] := by
      rw [F₄.operands notzOp hNotzIn₄]; grind
    have hShxOperands : shxOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (xCastOp.getResult 0), ValuePtr.opResult (zCastOp.getResult 0)] := by
      rw [F₅.operands shxOp hShxIn₅]; grind
    have hY1Operands :
        y1Op.getOperands! ctx₉.raw = #[ValuePtr.opResult (yCastOp.getResult 0)] := by
      rw [F₆.operands y1Op hY1In₆]; grind
    have hShyOperands : shyOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (y1Op.getResult 0), ValuePtr.opResult (notzOp.getResult 0)] := by
      rw [F₇.operands shyOp hShyIn₇]; grind
    have hOrOperands : orOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (shxOp.getResult 0), ValuePtr.opResult (shyOp.getResult 0)] := by
      rw [F₈.operands orOp hOrIn₈]; grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₉.raw = #[ValuePtr.opResult (orOp.getResult 0)] := by grind
    have hXCastResTypes : xCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes xCastOp hXCastIn₁]; grind
    have hYCastResTypes : yCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes yCastOp hYCastIn₂]; grind
    have hZCastResTypes : zCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₃.resultTypes zCastOp hZCastIn₃]; grind
    have hNotzResTypes : notzOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₄.resultTypes notzOp hNotzIn₄]; grind
    have hShxResTypes : shxOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₅.resultTypes shxOp hShxIn₅]; grind
    have hY1ResTypes : y1Op.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₆.resultTypes y1Op hY1In₆]; grind
    have hShyResTypes : shyOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₇.resultTypes shyOp hShyIn₇]; grind
    have hOrResTypes : orOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₈.resultTypes orOp hOrIn₈]; grind
    have hNotzProps : notzOp.getProperties! ctx₉.raw (.riscv .xori)
        = RISCVImmediateProperties.mk (IntegerAttr.mk (-1) (IntegerType.mk 64)) := by
      rw [F₄.properties notzOp hNotzIn₄]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hNotz (operation := notzOp)]
    have hY1Props : y1Op.getProperties! ctx₉.raw (.riscv .srliw)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)) := by
      rw [F₆.properties y1Op hY1In₆]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hY1 (operation := y1Op)]
    have hCBType : ((op.getResult 0).get! ctx₈.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₈.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw :=
        G₈.valueType _ hResIn
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.integerType { bitwidth := 32 }, isT⟩] := by grind
    have hXCastFresh : ¬ xCastOp.InBounds ctx.raw :=
      WfRewriter.createOp_new_not_inBounds xCastOp hXCast
    have hYCastFresh : ¬ yCastOp.InBounds ctx₁.raw :=
      WfRewriter.createOp_new_not_inBounds yCastOp hYCast
    have hZCastFresh : ¬ zCastOp.InBounds ctx₂.raw :=
      WfRewriter.createOp_new_not_inBounds zCastOp hZCast
    have hNotzFresh : ¬ notzOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_new_not_inBounds notzOp hNotz
    have hShxFresh : ¬ shxOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_new_not_inBounds shxOp hShx
    have hY1Fresh : ¬ y1Op.InBounds ctx₅.raw :=
      WfRewriter.createOp_new_not_inBounds y1Op hY1
    have hShyFresh : ¬ shyOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_new_not_inBounds shyOp hShy
    have hXResIn₁ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₁.raw :=
      opResult_getResult_inBounds_of_createOp hXCast (by simp)
    have hXResIn₂ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₂.raw :=
      E₂.valueInBounds _ hXResIn₁
    have hXResIn₃ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₃.raw :=
      E₃.valueInBounds _ hXResIn₂
    have hYResIn₂ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₂.raw :=
      opResult_getResult_inBounds_of_createOp hYCast (by simp)
    have hYResIn₃ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₃.raw :=
      E₃.valueInBounds _ hYResIn₂
    have hYResIn₄ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₄.raw :=
      E₄.valueInBounds _ hYResIn₃
    have hZResIn₃ : (ValuePtr.opResult (zCastOp.getResult 0)).InBounds ctx₃.raw :=
      opResult_getResult_inBounds_of_createOp hZCast (by simp)
    have hNotzResIn₄ : (ValuePtr.opResult (notzOp.getResult 0)).InBounds ctx₄.raw :=
      opResult_getResult_inBounds_of_createOp hNotz (by simp)
    have hNotzResIn₅ : (ValuePtr.opResult (notzOp.getResult 0)).InBounds ctx₅.raw :=
      E₅.valueInBounds _ hNotzResIn₄
    have hShxResIn₅ : (ValuePtr.opResult (shxOp.getResult 0)).InBounds ctx₅.raw :=
      opResult_getResult_inBounds_of_createOp hShx (by simp)
    have hShxResIn₆ : (ValuePtr.opResult (shxOp.getResult 0)).InBounds ctx₆.raw :=
      E₆.valueInBounds _ hShxResIn₅
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state')
        (inBounds := F₁.inBounds xCastOp hXCastIn₁)
        hXCastType hXCastOperands hXCastResTypes hAVal'
    have hBVal₁ : s₁.variables.getVar? b = some (RuntimeValue.int 32 yt) := by
      rw [hFrame₁ b (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hBIn hXCastFresh)]
      exact hBVal'
    have hCVal₁ : s₁.variables.getVar? amt = some (RuntimeValue.int 32 ct) := by
      rw [hFrame₁ amt (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCIn hXCastFresh)]
      exact hCVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁)
        (inBounds := F₂.inBounds yCastOp hYCastIn₂)
        hYCastType hYCastOperands hYCastResTypes hBVal₁
    have hCVal₂ : s₂.variables.getVar? amt = some (RuntimeValue.int 32 ct) := by
      rw [hFrame₂ amt (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        (E₁.valueInBounds amt hCIn) hYCastFresh)]
      exact hCVal₁
    have hXRes₂ : s₂.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₁ hYCastFresh)]
      exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_castToReg_forward (state := s₂)
        (inBounds := F₃.inBounds zCastOp hZCastIn₃)
        hZCastType hZCastOperands hZCastResTypes hCVal₂
    have hXRes₃ : s₃.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₂ hZCastFresh)]
      exact hXRes₂
    have hYRes₃ : s₃.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₂ hZCastFresh)]
      exact hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₃)
        (inBounds := F₄.inBounds notzOp hNotzIn₄)
        (res := Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hNotzType hNotzProps hNotzOperands hNotzResTypes hRes₃
    have hXRes₄ : s₄.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₃ hNotzFresh)]
      exact hXRes₃
    have hYRes₄ : s₄.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₃ hNotzFresh)]
      exact hYRes₃
    have hZRes₄ : s₄.variables.getVar? (ValuePtr.opResult (zCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg ct)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hZResIn₃ hNotzFresh)]
      exact hRes₃
    obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₄)
        (inBounds := F₅.inBounds shxOp hShxIn₅)
        (f := fun r₁ r₂ => Data.RISCV.sllw r₂ r₁) (fun _ _ _ _ => rfl)
        hShxType hShxOperands hShxResTypes hXRes₄ hZRes₄
    have hYRes₅ : s₅.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₄ hShxFresh)]
      exact hYRes₄
    have hNotzRes₅ : s₅.variables.getVar? (ValuePtr.opResult (notzOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hNotzResIn₄ hShxFresh)]
      exact hRes₄
    obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₅)
        (inBounds := F₆.inBounds y1Op hY1In₆)
        (res := Data.RISCV.srliw (BitVec.ofInt 5 1) (LLVM.Int.toReg yt))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hY1Type hY1Props hY1Operands hY1ResTypes hYRes₅
    have hNotzRes₆ : s₆.variables.getVar? (ValuePtr.opResult (notzOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))) := by
      rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hNotzResIn₅ hY1Fresh)]
      exact hNotzRes₅
    obtain ⟨s₇, hI₇, hMem₇, hRes₇, hFrame₇⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₆)
        (inBounds := F₇.inBounds shyOp hShyIn₇)
        (f := fun r₁ r₂ => Data.RISCV.srlw r₂ r₁) (fun _ _ _ _ => rfl)
        hShyType hShyOperands hShyResTypes hRes₆ hNotzRes₆
    have hShxRes₇ : s₇.variables.getVar? (ValuePtr.opResult (shxOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.sllw (LLVM.Int.toReg ct) (LLVM.Int.toReg xt))) := by
      rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hShxResIn₆ hShyFresh),
        hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hShxResIn₅ hY1Fresh)]
      exact hRes₅
    obtain ⟨s₈, hI₈, hMem₈, hRes₈, hFrame₈⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₇)
        (inBounds := F₈.inBounds orOp hOrIn₈)
        (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl)
        hOrType hOrOperands hOrResTypes hShxRes₇ hRes₇
    obtain ⟨s₉, hI₉, hMem₉, hRes₉, -⟩ :=
      interpretOp_castBack_forward (state := s₈) (inBounds := hCBIn₉)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₈
    refine ⟨s₉, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, hI₈, hI₉, liftM, monadLift,
        MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 32 (RISCV.Reg.toInt
          (Data.RISCV.or
            (Data.RISCV.srlw (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.srliw (BitVec.ofInt 5 1) (LLVM.Int.toReg yt)))
            (Data.RISCV.sllw (LLVM.Int.toReg ct) (LLVM.Int.toReg xt))) 32)], ?_, ?_⟩
      · simp [hRes₉, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using fshlGeneral_isRefinedBy_toInt_32 hxtRef hytRef hctRef⟩

/-! ### Correctness of `fshrGeneral_local` -/

set_option maxHeartbeats 3200000 in
/-- Correctness of the `fshrGeneral_local` lowering: the
    `castToReg ×3 → xori -1 → slli/slliw 1 → sll/sllw → srl/srlw → or → castBack` round trip
    refines `llvm.intr.fshr x y z` on `i64`/`i32`. -/
theorem fshrGeneral_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics fshrGeneral_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, fshrGeneral_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the `matchFshr` matcher.
  have hMatchSome : (matchFshr op ctx.raw).isSome := by
    cases hM : matchFshr op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, b, amt⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchFshr_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type, hOp2Type⟩ :=
    OperationPtr.Verified.llvm_intr__fshr opVerif hOpType
  have hAEq : a = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hBEq : b = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hAmtEq : amt = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = a := by
    rw [hAEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = b := by
    rw [hBEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = amt := by
    rw [hAmtEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hAType : (a.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hBType : (b.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hAmtType : (amt.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, hOp2Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  have isT : Attribute.isType (Attribute.integerType intType) :=
    hResTypeVal ▸ (((op.getResult 0).get! ctx.raw).type).2
  -- Resolve the result-type-destructuring match on `intType`.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- The bitwidth guard must be false (else the RHS would be `some (ctx, none)`).
  peelSplittableCondition [hBw] hpattern
  -- Unfold the interpretation of the matched `fshr`: exposes the three operand values.
  obtain ⟨xa, xb, xc, haVal, hbVal, hcVal, hMem, hRes, hCf⟩ :=
    matchTernaryOp_interpretOp_unfold (srcFn := fun {_} x y z => Data.LLVM.Int.fshr x y z)
      opInBounds hOpType hNumResults hOperands
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hinterp hAType hBType hAmtType
  subst hCf
  -- In-bounds and dominance facts for the three operands, established before any op creation.
  have hAIn : a.InBounds ctx.raw := by grind
  have hBIn : b.InBounds ctx.raw := by grind
  have hCIn : amt.InBounds ctx.raw := by grind
  have hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  have hDomCtxA : a.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxB : b.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxC : amt.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `fshr` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have aNotOp : ¬ a ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have bNotOp : ¬ b ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have cNotOp : ¬ amt ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the four shared creations (three casts and the `xori`).
  peelOpCreation hpattern ctx₁ xCastOp hXCast
  simp only [castToRegLocal] at hXCast
  replace hXCast := WfRewriter.createOp!_none_some hXCast
  obtain ⟨_, _, _, hXCast⟩ := hXCast
  peelOpCreation hpattern ctx₂ yCastOp hYCast
  simp only [castToRegLocal] at hYCast
  replace hYCast := WfRewriter.createOp!_none_some hYCast
  obtain ⟨_, _, _, hYCast⟩ := hYCast
  peelOpCreation hpattern ctx₃ zCastOp hZCast
  simp only [castToRegLocal] at hZCast
  replace hZCast := WfRewriter.createOp!_none_some hZCast
  obtain ⟨_, _, _, hZCast⟩ := hZCast
  peelOpCreation hpattern ctx₄ notzOp hNotz
  replace hNotz := WfRewriter.createOp!_none_some hNotz
  obtain ⟨_, _, _, hNotz⟩ := hNotz
  -- Branch on the result bitwidth.
  have hBwCases : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  rcases hBwCases with hbw | hbw
  · -- ===== 64-bit case: `slli`/`sll`/`srl`/`or` =====
    rw [if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    simp only [] at hpattern
    peelOpCreation hpattern ctx₅ x1Op hX1
    replace hX1 := WfRewriter.createOp!_none_some hX1
    obtain ⟨_, _, _, hX1⟩ := hX1
    peelOpCreation hpattern ctx₆ shxOp hShx
    replace hShx := WfRewriter.createOp!_none_some hShx
    obtain ⟨_, _, _, hShx⟩ := hShx
    peelOpCreation hpattern ctx₇ shyOp hShy
    replace hShy := WfRewriter.createOp!_none_some hShy
    obtain ⟨_, _, _, hShy⟩ := hShy
    peelOpCreation hpattern ctx₈ orOp hOr
    replace hOr := WfRewriter.createOp!_none_some hOr
    obtain ⟨_, _, _, hOr⟩ := hOr
    peelOpCreation hpattern ctx₉ castBackOp hCastBack
    simp only [replaceWithRegLocal] at hCastBack
    replace hCastBack := WfRewriter.createOp!_none_some hCastBack
    obtain ⟨_, _, _, hCastBack⟩ := hCastBack
    cleanupHpattern hpattern
    -- `op` stays in bounds through the creations.
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hXCast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hYCast hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hZCast hOpIn₂
    have hOpIn₄ : op.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hNotz hOpIn₃
    have hOpIn₅ : op.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hX1 hOpIn₄
    have hOpIn₆ : op.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hShx hOpIn₅
    have hOpIn₇ : op.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hShy hOpIn₆
    have hOpIn₈ : op.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOr hOpIn₇
    -- One-step context extensions and their compositions up to the final context `ctx₉`.
    have E₁ := CtxExtends.of_createOp (op := op) hXCast opInBounds
    have E₂ := CtxExtends.of_createOp (op := op) hYCast hOpIn₁
    have E₃ := CtxExtends.of_createOp (op := op) hZCast hOpIn₂
    have E₄ := CtxExtends.of_createOp (op := op) hNotz hOpIn₃
    have E₅ := CtxExtends.of_createOp (op := op) hX1 hOpIn₄
    have E₆ := CtxExtends.of_createOp (op := op) hShx hOpIn₅
    have E₇ := CtxExtends.of_createOp (op := op) hShy hOpIn₆
    have E₈ := CtxExtends.of_createOp (op := op) hOr hOpIn₇
    have E₉ := CtxExtends.of_createOp (op := op) hCastBack hOpIn₈
    have F₈ : CtxExtends op ctx₈ ctx₉ := E₉
    have F₇ : CtxExtends op ctx₇ ctx₉ := E₈.trans F₈
    have F₆ : CtxExtends op ctx₆ ctx₉ := E₇.trans F₇
    have F₅ : CtxExtends op ctx₅ ctx₉ := E₆.trans F₆
    have F₄ : CtxExtends op ctx₄ ctx₉ := E₅.trans F₅
    have F₃ : CtxExtends op ctx₃ ctx₉ := E₄.trans F₄
    have F₂ : CtxExtends op ctx₂ ctx₉ := E₃.trans F₃
    have F₁ : CtxExtends op ctx₁ ctx₉ := E₂.trans F₂
    have Ectx : CtxExtends op ctx ctx₉ := E₁.trans F₁
    have G₈ : CtxExtends op ctx ctx₈ :=
      E₁.trans (E₂.trans (E₃.trans (E₄.trans (E₅.trans (E₆.trans (E₇.trans E₈))))))
    -- Read the refined values `xt`/`yt`/`ct` of `a`/`b`/`amt` in the target state `state'`.
    obtain ⟨xt, hAVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hAIn haVal
        hDomCtxA (Ectx.dominates a hDomCtxA) aNotOp
    obtain ⟨yt, hBVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hBIn hbVal
        hDomCtxB (Ectx.dominates b hDomCtxB) bNotOp
    obtain ⟨ct, hCVal', hctRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hCIn hcVal
        hDomCtxC (Ectx.dominates amt hDomCtxC) cNotOp
    -- Normalise the bitwidth to the literal `64`.
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- In-bounds facts for the nine created ops in their creation contexts.
    have hXCastIn₁ : xCastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds xCastOp hXCast
    have hYCastIn₂ : yCastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds yCastOp hYCast
    have hZCastIn₃ : zCastOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds zCastOp hZCast
    have hNotzIn₄ : notzOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds notzOp hNotz
    have hX1In₅ : x1Op.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds x1Op hX1
    have hShxIn₆ : shxOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds shxOp hShx
    have hShyIn₇ : shyOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds shyOp hShy
    have hOrIn₈ : orOp.InBounds ctx₈.raw := WfRewriter.createOp_new_inBounds orOp hOr
    have hCBIn₉ : castBackOp.InBounds ctx₉.raw :=
      WfRewriter.createOp_new_inBounds castBackOp hCastBack
    -- Structural facts about the nine created ops, in the final context.
    have hXCastType : xCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType xCastOp hXCastIn₁]; grind
    have hYCastType : yCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType yCastOp hYCastIn₂]; grind
    have hZCastType : zCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₃.opType zCastOp hZCastIn₃]; grind
    have hNotzType : notzOp.getOpType! ctx₉.raw = .riscv .xori := by
      rw [F₄.opType notzOp hNotzIn₄]; grind
    have hX1Type : x1Op.getOpType! ctx₉.raw = .riscv .slli := by
      rw [F₅.opType x1Op hX1In₅]; grind
    have hShxType : shxOp.getOpType! ctx₉.raw = .riscv .sll := by
      rw [F₆.opType shxOp hShxIn₆]; grind
    have hShyType : shyOp.getOpType! ctx₉.raw = .riscv .srl := by
      rw [F₇.opType shyOp hShyIn₇]; grind
    have hOrType : orOp.getOpType! ctx₉.raw = .riscv .or := by
      rw [F₈.opType orOp hOrIn₈]; grind
    have hCastBackType : castBackOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hXCastOperands : xCastOp.getOperands! ctx₉.raw = #[a] := by
      rw [F₁.operands xCastOp hXCastIn₁]; grind
    have hYCastOperands : yCastOp.getOperands! ctx₉.raw = #[b] := by
      rw [F₂.operands yCastOp hYCastIn₂]; grind
    have hZCastOperands : zCastOp.getOperands! ctx₉.raw = #[amt] := by
      rw [F₃.operands zCastOp hZCastIn₃]; grind
    have hNotzOperands :
        notzOp.getOperands! ctx₉.raw = #[ValuePtr.opResult (zCastOp.getResult 0)] := by
      rw [F₄.operands notzOp hNotzIn₄]; grind
    have hX1Operands :
        x1Op.getOperands! ctx₉.raw = #[ValuePtr.opResult (xCastOp.getResult 0)] := by
      rw [F₅.operands x1Op hX1In₅]; grind
    have hShxOperands : shxOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (x1Op.getResult 0), ValuePtr.opResult (notzOp.getResult 0)] := by
      rw [F₆.operands shxOp hShxIn₆]; grind
    have hShyOperands : shyOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (yCastOp.getResult 0), ValuePtr.opResult (zCastOp.getResult 0)] := by
      rw [F₇.operands shyOp hShyIn₇]; grind
    have hOrOperands : orOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (shxOp.getResult 0), ValuePtr.opResult (shyOp.getResult 0)] := by
      rw [F₈.operands orOp hOrIn₈]; grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₉.raw = #[ValuePtr.opResult (orOp.getResult 0)] := by grind
    have hXCastResTypes : xCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes xCastOp hXCastIn₁]; grind
    have hYCastResTypes : yCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes yCastOp hYCastIn₂]; grind
    have hZCastResTypes : zCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₃.resultTypes zCastOp hZCastIn₃]; grind
    have hNotzResTypes : notzOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₄.resultTypes notzOp hNotzIn₄]; grind
    have hX1ResTypes : x1Op.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₅.resultTypes x1Op hX1In₅]; grind
    have hShxResTypes : shxOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₆.resultTypes shxOp hShxIn₆]; grind
    have hShyResTypes : shyOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₇.resultTypes shyOp hShyIn₇]; grind
    have hOrResTypes : orOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₈.resultTypes orOp hOrIn₈]; grind
    -- The immediate properties of the `xori` and `slli`.
    have hNotzProps : notzOp.getProperties! ctx₉.raw (.riscv .xori)
        = RISCVImmediateProperties.mk (IntegerAttr.mk (-1) (IntegerType.mk 64)) := by
      rw [F₄.properties notzOp hNotzIn₄]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hNotz (operation := notzOp)]
    have hX1Props : x1Op.getProperties! ctx₉.raw (.riscv .slli)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)) := by
      rw [F₅.properties x1Op hX1In₅]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hX1 (operation := x1Op)]
    -- The cast-back op's result type is `i64`.
    have hCBType : ((op.getResult 0).get! ctx₈.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₈.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw :=
        G₈.valueType _ hResIn
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.integerType { bitwidth := 64 }, isT⟩] := by grind
    -- Freshness facts for the frame clauses.
    have hXCastFresh : ¬ xCastOp.InBounds ctx.raw :=
      WfRewriter.createOp_new_not_inBounds xCastOp hXCast
    have hYCastFresh : ¬ yCastOp.InBounds ctx₁.raw :=
      WfRewriter.createOp_new_not_inBounds yCastOp hYCast
    have hZCastFresh : ¬ zCastOp.InBounds ctx₂.raw :=
      WfRewriter.createOp_new_not_inBounds zCastOp hZCast
    have hNotzFresh : ¬ notzOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_new_not_inBounds notzOp hNotz
    have hX1Fresh : ¬ x1Op.InBounds ctx₄.raw :=
      WfRewriter.createOp_new_not_inBounds x1Op hX1
    have hShxFresh : ¬ shxOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_new_not_inBounds shxOp hShx
    have hShyFresh : ¬ shyOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_new_not_inBounds shyOp hShy
    -- In-bounds facts for the fresh cast/op results in intermediate contexts.
    have hXResIn₁ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₁.raw :=
      opResult_getResult_inBounds_of_createOp hXCast (by simp)
    have hXResIn₂ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₂.raw :=
      E₂.valueInBounds _ hXResIn₁
    have hXResIn₃ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₃.raw :=
      E₃.valueInBounds _ hXResIn₂
    have hYResIn₂ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₂.raw :=
      opResult_getResult_inBounds_of_createOp hYCast (by simp)
    have hYResIn₃ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₃.raw :=
      E₃.valueInBounds _ hYResIn₂
    have hYResIn₄ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₄.raw :=
      E₄.valueInBounds _ hYResIn₃
    have hYResIn₅ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₅.raw :=
      E₅.valueInBounds _ hYResIn₄
    have hZResIn₃ : (ValuePtr.opResult (zCastOp.getResult 0)).InBounds ctx₃.raw :=
      opResult_getResult_inBounds_of_createOp hZCast (by simp)
    have hZResIn₄ : (ValuePtr.opResult (zCastOp.getResult 0)).InBounds ctx₄.raw :=
      E₄.valueInBounds _ hZResIn₃
    have hZResIn₅ : (ValuePtr.opResult (zCastOp.getResult 0)).InBounds ctx₅.raw :=
      E₅.valueInBounds _ hZResIn₄
    have hNotzResIn₄ : (ValuePtr.opResult (notzOp.getResult 0)).InBounds ctx₄.raw :=
      opResult_getResult_inBounds_of_createOp hNotz (by simp)
    have hShxResIn₆ : (ValuePtr.opResult (shxOp.getResult 0)).InBounds ctx₆.raw :=
      opResult_getResult_inBounds_of_createOp hShx (by simp)
    -- Interpretation tail: `[xCast, yCast, zCast, notz, x1, shx, shy, or, castBack]` in `state'`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state')
        (inBounds := F₁.inBounds xCastOp hXCastIn₁)
        hXCastType hXCastOperands hXCastResTypes hAVal'
    have hBVal₁ : s₁.variables.getVar? b = some (RuntimeValue.int 64 yt) := by
      rw [hFrame₁ b (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hBIn hXCastFresh)]
      exact hBVal'
    have hCVal₁ : s₁.variables.getVar? amt = some (RuntimeValue.int 64 ct) := by
      rw [hFrame₁ amt (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCIn hXCastFresh)]
      exact hCVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁)
        (inBounds := F₂.inBounds yCastOp hYCastIn₂)
        hYCastType hYCastOperands hYCastResTypes hBVal₁
    have hCVal₂ : s₂.variables.getVar? amt = some (RuntimeValue.int 64 ct) := by
      rw [hFrame₂ amt (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        (E₁.valueInBounds amt hCIn) hYCastFresh)]
      exact hCVal₁
    have hXRes₂ : s₂.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₁ hYCastFresh)]
      exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_castToReg_forward (state := s₂)
        (inBounds := F₃.inBounds zCastOp hZCastIn₃)
        hZCastType hZCastOperands hZCastResTypes hCVal₂
    have hXRes₃ : s₃.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₂ hZCastFresh)]
      exact hXRes₂
    have hYRes₃ : s₃.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₂ hZCastFresh)]
      exact hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₃)
        (inBounds := F₄.inBounds notzOp hNotzIn₄)
        (res := Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hNotzType hNotzProps hNotzOperands hNotzResTypes hRes₃
    have hXRes₄ : s₄.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₃ hNotzFresh)]
      exact hXRes₃
    have hYRes₄ : s₄.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₃ hNotzFresh)]
      exact hYRes₃
    have hZRes₄ : s₄.variables.getVar? (ValuePtr.opResult (zCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg ct)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hZResIn₃ hNotzFresh)]
      exact hRes₃
    obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₄)
        (inBounds := F₅.inBounds x1Op hX1In₅)
        (res := Data.RISCV.slli (BitVec.ofInt 6 1) (LLVM.Int.toReg xt))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hX1Type hX1Props hX1Operands hX1ResTypes hXRes₄
    have hYRes₅ : s₅.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₄ hX1Fresh)]
      exact hYRes₄
    have hZRes₅ : s₅.variables.getVar? (ValuePtr.opResult (zCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg ct)) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hZResIn₄ hX1Fresh)]
      exact hZRes₄
    have hNotzRes₅ : s₅.variables.getVar? (ValuePtr.opResult (notzOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hNotzResIn₄ hX1Fresh)]
      exact hRes₄
    obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₅)
        (inBounds := F₆.inBounds shxOp hShxIn₆)
        (f := fun r₁ r₂ => Data.RISCV.sll r₂ r₁) (fun _ _ _ _ => rfl)
        hShxType hShxOperands hShxResTypes hRes₅ hNotzRes₅
    have hYRes₆ : s₆.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₅ hShxFresh)]
      exact hYRes₅
    have hZRes₆ : s₆.variables.getVar? (ValuePtr.opResult (zCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg ct)) := by
      rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hZResIn₅ hShxFresh)]
      exact hZRes₅
    obtain ⟨s₇, hI₇, hMem₇, hRes₇, hFrame₇⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₆)
        (inBounds := F₇.inBounds shyOp hShyIn₇)
        (f := fun r₁ r₂ => Data.RISCV.srl r₂ r₁) (fun _ _ _ _ => rfl)
        hShyType hShyOperands hShyResTypes hYRes₆ hZRes₆
    have hShxRes₇ : s₇.variables.getVar? (ValuePtr.opResult (shxOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.sll (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.slli (BitVec.ofInt 6 1) (LLVM.Int.toReg xt)))) := by
      rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hShxResIn₆ hShyFresh)]
      exact hRes₆
    obtain ⟨s₈, hI₈, hMem₈, hRes₈, hFrame₈⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₇)
        (inBounds := F₈.inBounds orOp hOrIn₈)
        (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl)
        hOrType hOrOperands hOrResTypes hShxRes₇ hRes₇
    obtain ⟨s₉, hI₉, hMem₉, hRes₉, -⟩ :=
      interpretOp_castBack_forward (state := s₈) (inBounds := hCBIn₉)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₈
    refine ⟨s₉, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, hI₈, hI₉, liftM, monadLift,
        MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
          (Data.RISCV.or
            (Data.RISCV.srl (LLVM.Int.toReg ct) (LLVM.Int.toReg yt))
            (Data.RISCV.sll (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.slli (BitVec.ofInt 6 1) (LLVM.Int.toReg xt)))) 64)], ?_, ?_⟩
      · simp [hRes₉, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using fshrGeneral_isRefinedBy_toInt_64 hxtRef hytRef hctRef⟩
  · -- ===== 32-bit case: `slliw`/`sllw`/`srlw`/`or` =====
    rw [if_pos hbw] at hpattern
    simp only [] at hpattern
    peelOpCreation hpattern ctx₅ x1Op hX1
    replace hX1 := WfRewriter.createOp!_none_some hX1
    obtain ⟨_, _, _, hX1⟩ := hX1
    peelOpCreation hpattern ctx₆ shxOp hShx
    replace hShx := WfRewriter.createOp!_none_some hShx
    obtain ⟨_, _, _, hShx⟩ := hShx
    peelOpCreation hpattern ctx₇ shyOp hShy
    replace hShy := WfRewriter.createOp!_none_some hShy
    obtain ⟨_, _, _, hShy⟩ := hShy
    peelOpCreation hpattern ctx₈ orOp hOr
    replace hOr := WfRewriter.createOp!_none_some hOr
    obtain ⟨_, _, _, hOr⟩ := hOr
    peelOpCreation hpattern ctx₉ castBackOp hCastBack
    simp only [replaceWithRegLocal] at hCastBack
    replace hCastBack := WfRewriter.createOp!_none_some hCastBack
    obtain ⟨_, _, _, hCastBack⟩ := hCastBack
    cleanupHpattern hpattern
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hXCast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hYCast hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hZCast hOpIn₂
    have hOpIn₄ : op.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hNotz hOpIn₃
    have hOpIn₅ : op.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hX1 hOpIn₄
    have hOpIn₆ : op.InBounds ctx₆.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hShx hOpIn₅
    have hOpIn₇ : op.InBounds ctx₇.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hShy hOpIn₆
    have hOpIn₈ : op.InBounds ctx₈.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOr hOpIn₇
    have E₁ := CtxExtends.of_createOp (op := op) hXCast opInBounds
    have E₂ := CtxExtends.of_createOp (op := op) hYCast hOpIn₁
    have E₃ := CtxExtends.of_createOp (op := op) hZCast hOpIn₂
    have E₄ := CtxExtends.of_createOp (op := op) hNotz hOpIn₃
    have E₅ := CtxExtends.of_createOp (op := op) hX1 hOpIn₄
    have E₆ := CtxExtends.of_createOp (op := op) hShx hOpIn₅
    have E₇ := CtxExtends.of_createOp (op := op) hShy hOpIn₆
    have E₈ := CtxExtends.of_createOp (op := op) hOr hOpIn₇
    have E₉ := CtxExtends.of_createOp (op := op) hCastBack hOpIn₈
    have F₈ : CtxExtends op ctx₈ ctx₉ := E₉
    have F₇ : CtxExtends op ctx₇ ctx₉ := E₈.trans F₈
    have F₆ : CtxExtends op ctx₆ ctx₉ := E₇.trans F₇
    have F₅ : CtxExtends op ctx₅ ctx₉ := E₆.trans F₆
    have F₄ : CtxExtends op ctx₄ ctx₉ := E₅.trans F₅
    have F₃ : CtxExtends op ctx₃ ctx₉ := E₄.trans F₄
    have F₂ : CtxExtends op ctx₂ ctx₉ := E₃.trans F₃
    have F₁ : CtxExtends op ctx₁ ctx₉ := E₂.trans F₂
    have Ectx : CtxExtends op ctx ctx₉ := E₁.trans F₁
    have G₈ : CtxExtends op ctx ctx₈ :=
      E₁.trans (E₂.trans (E₃.trans (E₄.trans (E₅.trans (E₆.trans (E₇.trans E₈))))))
    obtain ⟨xt, hAVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hAIn haVal
        hDomCtxA (Ectx.dominates a hDomCtxA) aNotOp
    obtain ⟨yt, hBVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hBIn hbVal
        hDomCtxB (Ectx.dominates b hDomCtxB) bNotOp
    obtain ⟨ct, hCVal', hctRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hCIn hcVal
        hDomCtxC (Ectx.dominates amt hDomCtxC) cNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    have hXCastIn₁ : xCastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds xCastOp hXCast
    have hYCastIn₂ : yCastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds yCastOp hYCast
    have hZCastIn₃ : zCastOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds zCastOp hZCast
    have hNotzIn₄ : notzOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds notzOp hNotz
    have hX1In₅ : x1Op.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds x1Op hX1
    have hShxIn₆ : shxOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds shxOp hShx
    have hShyIn₇ : shyOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds shyOp hShy
    have hOrIn₈ : orOp.InBounds ctx₈.raw := WfRewriter.createOp_new_inBounds orOp hOr
    have hCBIn₉ : castBackOp.InBounds ctx₉.raw :=
      WfRewriter.createOp_new_inBounds castBackOp hCastBack
    have hXCastType : xCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType xCastOp hXCastIn₁]; grind
    have hYCastType : yCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType yCastOp hYCastIn₂]; grind
    have hZCastType : zCastOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      rw [F₃.opType zCastOp hZCastIn₃]; grind
    have hNotzType : notzOp.getOpType! ctx₉.raw = .riscv .xori := by
      rw [F₄.opType notzOp hNotzIn₄]; grind
    have hX1Type : x1Op.getOpType! ctx₉.raw = .riscv .slliw := by
      rw [F₅.opType x1Op hX1In₅]; grind
    have hShxType : shxOp.getOpType! ctx₉.raw = .riscv .sllw := by
      rw [F₆.opType shxOp hShxIn₆]; grind
    have hShyType : shyOp.getOpType! ctx₉.raw = .riscv .srlw := by
      rw [F₇.opType shyOp hShyIn₇]; grind
    have hOrType : orOp.getOpType! ctx₉.raw = .riscv .or := by
      rw [F₈.opType orOp hOrIn₈]; grind
    have hCastBackType : castBackOp.getOpType! ctx₉.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hXCastOperands : xCastOp.getOperands! ctx₉.raw = #[a] := by
      rw [F₁.operands xCastOp hXCastIn₁]; grind
    have hYCastOperands : yCastOp.getOperands! ctx₉.raw = #[b] := by
      rw [F₂.operands yCastOp hYCastIn₂]; grind
    have hZCastOperands : zCastOp.getOperands! ctx₉.raw = #[amt] := by
      rw [F₃.operands zCastOp hZCastIn₃]; grind
    have hNotzOperands :
        notzOp.getOperands! ctx₉.raw = #[ValuePtr.opResult (zCastOp.getResult 0)] := by
      rw [F₄.operands notzOp hNotzIn₄]; grind
    have hX1Operands :
        x1Op.getOperands! ctx₉.raw = #[ValuePtr.opResult (xCastOp.getResult 0)] := by
      rw [F₅.operands x1Op hX1In₅]; grind
    have hShxOperands : shxOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (x1Op.getResult 0), ValuePtr.opResult (notzOp.getResult 0)] := by
      rw [F₆.operands shxOp hShxIn₆]; grind
    have hShyOperands : shyOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (yCastOp.getResult 0), ValuePtr.opResult (zCastOp.getResult 0)] := by
      rw [F₇.operands shyOp hShyIn₇]; grind
    have hOrOperands : orOp.getOperands! ctx₉.raw
        = #[ValuePtr.opResult (shxOp.getResult 0), ValuePtr.opResult (shyOp.getResult 0)] := by
      rw [F₈.operands orOp hOrIn₈]; grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₉.raw = #[ValuePtr.opResult (orOp.getResult 0)] := by grind
    have hXCastResTypes : xCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes xCastOp hXCastIn₁]; grind
    have hYCastResTypes : yCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes yCastOp hYCastIn₂]; grind
    have hZCastResTypes : zCastOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₃.resultTypes zCastOp hZCastIn₃]; grind
    have hNotzResTypes : notzOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₄.resultTypes notzOp hNotzIn₄]; grind
    have hX1ResTypes : x1Op.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₅.resultTypes x1Op hX1In₅]; grind
    have hShxResTypes : shxOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₆.resultTypes shxOp hShxIn₆]; grind
    have hShyResTypes : shyOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₇.resultTypes shyOp hShyIn₇]; grind
    have hOrResTypes : orOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₈.resultTypes orOp hOrIn₈]; grind
    have hNotzProps : notzOp.getProperties! ctx₉.raw (.riscv .xori)
        = RISCVImmediateProperties.mk (IntegerAttr.mk (-1) (IntegerType.mk 64)) := by
      rw [F₄.properties notzOp hNotzIn₄]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hNotz (operation := notzOp)]
    have hX1Props : x1Op.getProperties! ctx₉.raw (.riscv .slliw)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)) := by
      rw [F₅.properties x1Op hX1In₅]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hX1 (operation := x1Op)]
    have hCBType : ((op.getResult 0).get! ctx₈.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₈.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw :=
        G₈.valueType _ hResIn
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₉.raw
        = #[⟨Attribute.integerType { bitwidth := 32 }, isT⟩] := by grind
    have hXCastFresh : ¬ xCastOp.InBounds ctx.raw :=
      WfRewriter.createOp_new_not_inBounds xCastOp hXCast
    have hYCastFresh : ¬ yCastOp.InBounds ctx₁.raw :=
      WfRewriter.createOp_new_not_inBounds yCastOp hYCast
    have hZCastFresh : ¬ zCastOp.InBounds ctx₂.raw :=
      WfRewriter.createOp_new_not_inBounds zCastOp hZCast
    have hNotzFresh : ¬ notzOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_new_not_inBounds notzOp hNotz
    have hX1Fresh : ¬ x1Op.InBounds ctx₄.raw :=
      WfRewriter.createOp_new_not_inBounds x1Op hX1
    have hShxFresh : ¬ shxOp.InBounds ctx₅.raw :=
      WfRewriter.createOp_new_not_inBounds shxOp hShx
    have hShyFresh : ¬ shyOp.InBounds ctx₆.raw :=
      WfRewriter.createOp_new_not_inBounds shyOp hShy
    have hXResIn₁ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₁.raw :=
      opResult_getResult_inBounds_of_createOp hXCast (by simp)
    have hXResIn₂ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₂.raw :=
      E₂.valueInBounds _ hXResIn₁
    have hXResIn₃ : (ValuePtr.opResult (xCastOp.getResult 0)).InBounds ctx₃.raw :=
      E₃.valueInBounds _ hXResIn₂
    have hYResIn₂ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₂.raw :=
      opResult_getResult_inBounds_of_createOp hYCast (by simp)
    have hYResIn₃ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₃.raw :=
      E₃.valueInBounds _ hYResIn₂
    have hYResIn₄ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₄.raw :=
      E₄.valueInBounds _ hYResIn₃
    have hYResIn₅ : (ValuePtr.opResult (yCastOp.getResult 0)).InBounds ctx₅.raw :=
      E₅.valueInBounds _ hYResIn₄
    have hZResIn₃ : (ValuePtr.opResult (zCastOp.getResult 0)).InBounds ctx₃.raw :=
      opResult_getResult_inBounds_of_createOp hZCast (by simp)
    have hZResIn₄ : (ValuePtr.opResult (zCastOp.getResult 0)).InBounds ctx₄.raw :=
      E₄.valueInBounds _ hZResIn₃
    have hZResIn₅ : (ValuePtr.opResult (zCastOp.getResult 0)).InBounds ctx₅.raw :=
      E₅.valueInBounds _ hZResIn₄
    have hNotzResIn₄ : (ValuePtr.opResult (notzOp.getResult 0)).InBounds ctx₄.raw :=
      opResult_getResult_inBounds_of_createOp hNotz (by simp)
    have hShxResIn₆ : (ValuePtr.opResult (shxOp.getResult 0)).InBounds ctx₆.raw :=
      opResult_getResult_inBounds_of_createOp hShx (by simp)
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state')
        (inBounds := F₁.inBounds xCastOp hXCastIn₁)
        hXCastType hXCastOperands hXCastResTypes hAVal'
    have hBVal₁ : s₁.variables.getVar? b = some (RuntimeValue.int 32 yt) := by
      rw [hFrame₁ b (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hBIn hXCastFresh)]
      exact hBVal'
    have hCVal₁ : s₁.variables.getVar? amt = some (RuntimeValue.int 32 ct) := by
      rw [hFrame₁ amt (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCIn hXCastFresh)]
      exact hCVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁)
        (inBounds := F₂.inBounds yCastOp hYCastIn₂)
        hYCastType hYCastOperands hYCastResTypes hBVal₁
    have hCVal₂ : s₂.variables.getVar? amt = some (RuntimeValue.int 32 ct) := by
      rw [hFrame₂ amt (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        (E₁.valueInBounds amt hCIn) hYCastFresh)]
      exact hCVal₁
    have hXRes₂ : s₂.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₁ hYCastFresh)]
      exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_castToReg_forward (state := s₂)
        (inBounds := F₃.inBounds zCastOp hZCastIn₃)
        hZCastType hZCastOperands hZCastResTypes hCVal₂
    have hXRes₃ : s₃.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₂ hZCastFresh)]
      exact hXRes₂
    have hYRes₃ : s₃.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₂ hZCastFresh)]
      exact hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₃)
        (inBounds := F₄.inBounds notzOp hNotzIn₄)
        (res := Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hNotzType hNotzProps hNotzOperands hNotzResTypes hRes₃
    have hXRes₄ : s₄.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hXResIn₃ hNotzFresh)]
      exact hXRes₃
    have hYRes₄ : s₄.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₃ hNotzFresh)]
      exact hYRes₃
    have hZRes₄ : s₄.variables.getVar? (ValuePtr.opResult (zCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg ct)) := by
      rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hZResIn₃ hNotzFresh)]
      exact hRes₃
    obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₄)
        (inBounds := F₅.inBounds x1Op hX1In₅)
        (res := Data.RISCV.slliw (BitVec.ofInt 5 1) (LLVM.Int.toReg xt))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hX1Type hX1Props hX1Operands hX1ResTypes hXRes₄
    have hYRes₅ : s₅.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₄ hX1Fresh)]
      exact hYRes₄
    have hZRes₅ : s₅.variables.getVar? (ValuePtr.opResult (zCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg ct)) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hZResIn₄ hX1Fresh)]
      exact hZRes₄
    have hNotzRes₅ : s₅.variables.getVar? (ValuePtr.opResult (notzOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))) := by
      rw [hFrame₅ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hNotzResIn₄ hX1Fresh)]
      exact hRes₄
    obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₅)
        (inBounds := F₆.inBounds shxOp hShxIn₆)
        (f := fun r₁ r₂ => Data.RISCV.sllw r₂ r₁) (fun _ _ _ _ => rfl)
        hShxType hShxOperands hShxResTypes hRes₅ hNotzRes₅
    have hYRes₆ : s₆.variables.getVar? (ValuePtr.opResult (yCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hYResIn₅ hShxFresh)]
      exact hYRes₅
    have hZRes₆ : s₆.variables.getVar? (ValuePtr.opResult (zCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg ct)) := by
      rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hZResIn₅ hShxFresh)]
      exact hZRes₅
    obtain ⟨s₇, hI₇, hMem₇, hRes₇, hFrame₇⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₆)
        (inBounds := F₇.inBounds shyOp hShyIn₇)
        (f := fun r₁ r₂ => Data.RISCV.srlw r₂ r₁) (fun _ _ _ _ => rfl)
        hShyType hShyOperands hShyResTypes hYRes₆ hZRes₆
    have hShxRes₇ : s₇.variables.getVar? (ValuePtr.opResult (shxOp.getResult 0))
        = some (RuntimeValue.reg
            (Data.RISCV.sllw (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.slliw (BitVec.ofInt 5 1) (LLVM.Int.toReg xt)))) := by
      rw [hFrame₇ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hShxResIn₆ hShyFresh)]
      exact hRes₆
    obtain ⟨s₈, hI₈, hMem₈, hRes₈, hFrame₈⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₇)
        (inBounds := F₈.inBounds orOp hOrIn₈)
        (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl)
        hOrType hOrOperands hOrResTypes hShxRes₇ hRes₇
    obtain ⟨s₉, hI₉, hMem₉, hRes₉, -⟩ :=
      interpretOp_castBack_forward (state := s₈) (inBounds := hCBIn₉)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₈
    refine ⟨s₉, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, hI₈, hI₉, liftM, monadLift,
        MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 32 (RISCV.Reg.toInt
          (Data.RISCV.or
            (Data.RISCV.srlw (LLVM.Int.toReg ct) (LLVM.Int.toReg yt))
            (Data.RISCV.sllw (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg ct))
              (Data.RISCV.slliw (BitVec.ofInt 5 1) (LLVM.Int.toReg xt)))) 32)], ?_, ?_⟩
      · simp [hRes₉, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using fshrGeneral_isRefinedBy_toInt_32 hxtRef hytRef hctRef⟩

/--
info: 'Veir.fshlGeneral_local_preservesSemantics' depends on axioms: [propext,
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
 fshlGeneral_isRefinedBy_toInt_32._native.bv_decide.ax_1_5,
 fshlGeneral_isRefinedBy_toInt_64._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms fshlGeneral_local_preservesSemantics

/--
info: 'Veir.fshrGeneral_local_preservesSemantics' depends on axioms: [propext,
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
 fshrGeneral_isRefinedBy_toInt_32._native.bv_decide.ax_1_5,
 fshrGeneral_isRefinedBy_toInt_64._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms fshrGeneral_local_preservesSemantics

end Veir
