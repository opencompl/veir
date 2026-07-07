import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBinaryW

namespace Veir

/-!
## Generic correctness of `lowerSignedMinMaxLocal`

`lowerSignedMinMaxLocal match? rop props` lowers a two-operand LLVM integer op whose result has type
`i64` or `i32` to `unrealized_conversion_cast` (each operand to a register) → a single signed `riscv`
op `rop` (`max`/`min`) → `unrealized_conversion_cast` (back to the source type). It is the *signed*
cousin of `lowerBinaryRegLocal`: `rop` is the same instruction at both bitwidths, but for `i32` the
two register operands are first sign-extended with `riscv.sextw`, because `castToRegLocal` puts the
operand into the register *zero-extended* (`LLVM.Int.toReg` computes `getValue.zeroExtend 64`).
Zero-extension preserves the unsigned order — so `umax`/`umin` need no fixup — but breaks the signed
order, so the signed compare needs the sign re-established first.

The proof shares the `lowerBinaryRegLocal` structure, but here the two bitwidths take *different*
op chains (four ops for `i64`, six for `i32`), so the proof splits on the bitwidth after the two
casts and executes each chain separately. Instantiating it for a concrete lowering (`smax`, `smin`)
only requires the matcher facts, the interpreter computation facts, and the two data-level
refinement lemmas.
-/

set_option maxHeartbeats 1600000 in
/-- Shared correctness proof for every `lowerSignedMinMaxLocal` lowering. For `i64` the round trip
    `int × int → reg × reg → rop → int` refines `srcFn`; for `i32` the two registers are
    sign-extended (`riscv.sextw`) before `rop`.

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier facts
    (`hVerified`), the interpreter computation facts for the source op and the riscv op
    (`hSemSrc`/`hSemR`, discharged by `simp`/`rfl` at concrete opcodes), and the two data-level
    refinement lemmas (`hRefine64`/`hRefine32`; the `i32` one carries the extra `sextw`). -/
theorem lowerSignedMinMaxLocal_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    {rop : Riscv} {props : propertiesOf (.riscv rop)}
    {f : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs},
        match? op ctx = some (lhs, rhs) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[lhs, rhs])
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedIntegerBinop ctx)
    (hSemSrc : ∀ (bw : Nat) (x y : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw y] blockOperands mem
          = some (.ok (#[.int bw (srcFn x y props)], mem, none)))
    (hSemR : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf rop)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' rop props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f r₁ r₂)], mem, none)))
    (hRefine64 : ∀ (x y xt yt : Data.LLVM.Int 64) (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcFn x y props ⊒ RISCV.Reg.toInt (f (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 64)
    (hRefine32 : ∀ (x y xt yt : Data.LLVM.Int 32) (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcFn x y props ⊒ RISCV.Reg.toInt
          (f (Data.RISCV.sextw (LLVM.Int.toReg xt)) (Data.RISCV.sextw (LLVM.Int.toReg yt))) 32)
    {h : LocalRewritePattern.ReturnOps (lowerSignedMinMaxLocal match? rop props)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (lowerSignedMinMaxLocal match? rop props)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (lowerSignedMinMaxLocal match? rop props)}
    {h₄ : LocalRewritePattern.ReturnValues (lowerSignedMinMaxLocal match? rop props)} :
    LocalRewritePattern.PreservesSemantics
      (lowerSignedMinMaxLocal match? rop props) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lowerSignedMinMaxLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    hVerified opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- Both operand types and the result type are the integer type `intType`.
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  -- Resolve the result-type-destructuring match on `intType`.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand values and their `srcFn`.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands rfl hSemSrc
      hinterp hLhsType hRhsType
  subst hCf
  -- The matched operands dominate the rewrite point in the source context.
  have hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  peelSplittableCondition [hBw] hpattern
  -- Source value: `op`'s single result is `srcFn` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `lhs`/`rhs` are not among `op`'s results.
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the two `castToRegLocal` creations (shared prefix of both bitwidth branches).
  peelCastToRegLocal₂ hpattern ctx₁ lcastOp hLCast hDomCtxL hDomL₁ hDomCtxR hDomR₁
  peelCastToRegLocal₂ hpattern ctx₂ rcastOp hRCast hDomL₁ hDomL₂ hDomR₁ hDomR₂
  -- Freshness facts shared by both branches.
  have hLCastFresh : ¬ lcastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds lcastOp hLCast
  have hRhsIn : rhs.InBounds ctx.raw := by clear hpattern; grind
  have hRhsNeLCastRes : ∀ i, rhs ≠ ValuePtr.opResult (lcastOp.getResult i) := by
    intro i heq
    rw [heq] at hRhsIn
    rw [ValuePtr.inBounds_opResult] at hRhsIn
    obtain ⟨hIn, -⟩ := hRhsIn
    exact hLCastFresh hIn
  have hLCastNeRCast : lcastOp ≠ rcastOp := by clear hpattern; grind
  -- Split on the bitwidth: `i32` sign-extends before the compare, `i64` does not.
  split at hpattern
  · -- ================= i32 branch =================
    rename_i hb32
    -- The two `castToRegLocal` peels are shared above; peel the two `sextw`s with the macro (their
    -- dominance transports are shallow enough for `grind`).
    peelOpCreation!₂ hpattern ctx₃ lsOp hLs hDomL₂ hDomL₃ hDomR₂ hDomR₃
    peelOpCreation!₂ hpattern ctx₄ rsOp hRs hDomL₃ hDomL₄ hDomR₃ hDomR₄
    -- Peel `mOp` and the cast-back manually. Their dominance transports need `op.InBounds` four/five
    -- creations deep, which `grind` cannot chain, and any `InBounds` hypothesis added to the context
    -- breaks the surrounding `grind`s (non-monotonicity). So build every `InBounds` witness inline —
    -- both `op.InBounds` (from `opInBounds` and the creation hypotheses) and each op's operand
    -- in-bounds fact (inside the `createOp!_none_eq` discharge, where `grind` needs the op-in-bounds
    -- and result-count facts as direct seeds) — and clear the `op.InBounds` facts before continuing.
    have ⟨⟨ctx₅, mOp⟩, hM, pat'⟩ := hpattern
    clear hpattern; have hpattern := pat'; clear pat'
    rw [WfRewriter.createOp!_none_eq
      (by clear hpattern; intro oper ho
          simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl
          · have hIn : lsOp.InBounds ctx₄.raw :=
              WfRewriter.createOp_inBounds_mono (ptr := .operation lsOp) hRs
                (WfRewriter.createOp_new_inBounds lsOp hLs)
            have hNum : lsOp.getNumResults! ctx₄.raw = 1 :=
              by grind [OperationPtr.getNumResults!_WfRewriter_createOp hLs (operation := lsOp),
                OperationPtr.getNumResults!_WfRewriter_createOp hRs (operation := lsOp)]
            grind
          · have hIn : rsOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds rsOp hRs
            have hNum : rsOp.getNumResults! ctx₄.raw = 1 :=
              by grind [OperationPtr.getNumResults!_WfRewriter_createOp hRs (operation := rsOp)]
            grind)
      (by clear hpattern; simp) (by clear hpattern; simp)] at hM
    have hOpInM : op.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRs
        (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLs
          (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRCast
            (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLCast opInBounds)))
    have hOpNeM : op ≠ mOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds mOp hM (heq ▸ hOpInM)
    have hDomL₅ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hM hOpInM hOpNeM).mpr hDomL₄
    have hDomR₅ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hM hOpInM hOpNeM).mpr hDomR₄
    have hOpInCB : op.InBounds ctx₅.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hM hOpInM
    clear hOpNeM hOpInM
    have ⟨⟨ctx₆, castBackOp⟩, hCastBack, pat'⟩ := hpattern
    clear hpattern; have hpattern := pat'; clear pat'
    simp only [replaceWithRegLocal] at hCastBack
    rw [WfRewriter.createOp!_none_eq
      (by clear hpattern; intro oper ho
          simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl
          have hIn : mOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds mOp hM
          have hNum : mOp.getNumResults! ctx₅.raw = 1 :=
            by grind [OperationPtr.getNumResults!_WfRewriter_createOp hM (operation := mOp)]
          grind)
      (by clear hpattern; simp) (by clear hpattern; simp)] at hCastBack
    have hOpNeCB : op ≠ castBackOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds castBackOp hCastBack (heq ▸ hOpInCB)
    have hDomL₆ :=
      (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack hOpInCB hOpNeCB).mpr hDomL₅
    have hDomR₆ :=
      (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack hOpInCB hOpNeCB).mpr hDomR₅
    clear hOpInCB hOpNeCB
    cleanupHpattern hpattern
    -- Read the refined values `xt`/`yt` of `lhs`/`rhs` in the target state `state'`.
    obtain ⟨xt, hLVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtxL hDomL₆ lNotOp
    obtain ⟨yt, hRVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
        hDomCtxR hDomR₆ rNotOp
    -- More freshness facts for the two extra `sextw` ops.
    have hRCastNeLs : rcastOp ≠ lsOp := by grind
    have hLsNeRs : lsOp ≠ rsOp := by grind
    -- Structural facts about the six created ops (bitwidth is 32).
    have hLCastType : lcastOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by grind
    have hRCastType : rcastOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by grind
    -- Both `sextw` ops share the opcode, so seed the opType transports explicitly to keep `grind`
    -- from conflating them.
    have hLsType : lsOp.getOpType! ctx₆.raw = .riscv .sextw := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hLs (operation := lsOp),
        OperationPtr.getOpType!_WfRewriter_createOp hRs (operation := lsOp),
        OperationPtr.getOpType!_WfRewriter_createOp hM (operation := lsOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lsOp)]
    have hRsType : rsOp.getOpType! ctx₆.raw = .riscv .sextw := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hRs (operation := rsOp),
        OperationPtr.getOpType!_WfRewriter_createOp hM (operation := rsOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rsOp)]
    have hMType : mOp.getOpType! ctx₆.raw = .riscv rop := by grind
    have hCastBackType : castBackOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hLCastOperands : lcastOp.getOperands! ctx₆.raw = #[lhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hLs (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRs (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hM (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastOperands : rcastOp.getOperands! ctx₆.raw = #[rhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hLs (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRs (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hM (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hLsOperands : lsOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (lcastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hLs (operation := lsOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRs (operation := lsOp),
        OperationPtr.getOperands!_WfRewriter_createOp hM (operation := lsOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lsOp)]
    have hRsOperands : rsOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (rcastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRs (operation := rsOp),
        OperationPtr.getOperands!_WfRewriter_createOp hM (operation := rsOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rsOp)]
    have hMOperands : mOp.getOperands! ctx₆.raw
        = #[ValuePtr.opResult (lsOp.getResult 0), ValuePtr.opResult (rsOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hM (operation := mOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := mOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (mOp.getResult 0)] := by grind
    -- The cast-back op's result type is the integer type `intType`.
    have hCBType : ((op.getResult 0).get! ctx₅.raw).type
        = (⟨Attribute.integerType intType, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₅.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hM
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hRs
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hLs
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hRCast
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hLCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hLCastResTypes : lcastOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hLs (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRs (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hM (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastResTypes : rcastOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hLs (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRs (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hM (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hLsResTypes : lsOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLs (operation := lsOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRs (operation := lsOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hM (operation := lsOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lsOp)]
    have hRsResTypes : rsOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRs (operation := rsOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hM (operation := rsOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rsOp)]
    have hMResTypes : mOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hM (operation := mOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := mOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₆.raw
        = #[⟨Attribute.integerType intType, by grind⟩] := by grind
    -- Interpretation tail: execute the six-op list in `state'`, carrying earlier bindings across
    -- later steps with the frame clauses.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hLCastType hLCastOperands hLCastResTypes hLVal'
    have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₆.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₆.raw rhs lcastOp
        with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (hRhsNeLCastRes i)
    have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int intType.bitwidth yt) := by
      rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
        hRCastType hRCastOperands hRCastResTypes hRVal₁
    have hLCastNotRCastRes :
        ValuePtr.opResult (lcastOp.getResult 0) ∉ rcastOp.getResults! ctx₆.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₆.raw
          (ValuePtr.opResult (lcastOp.getResult 0)) rcastOp with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (by grind [OperationPtr.getResult])
    have hLRes₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
    -- ls = sextw (lcast result).
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₂) (inBounds := by grind)
        (f := Data.RISCV.sextw) (fun _ _ _ _ => rfl) hLsType hLsOperands hLsResTypes hLRes₂
    have hRCastNotLsRes :
        ValuePtr.opResult (rcastOp.getResult 0) ∉ lsOp.getResults! ctx₆.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₆.raw
          (ValuePtr.opResult (rcastOp.getResult 0)) lsOp with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (by grind [OperationPtr.getResult])
    have hRRes₃ : s₃.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₃ _ hRCastNotLsRes]; exact hRes₂
    -- rs = sextw (rcast result).
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₃) (inBounds := by grind)
        (f := Data.RISCV.sextw) (fun _ _ _ _ => rfl) hRsType hRsOperands hRsResTypes hRRes₃
    have hLsNotRsRes :
        ValuePtr.opResult (lsOp.getResult 0) ∉ rsOp.getResults! ctx₆.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₆.raw
          (ValuePtr.opResult (lsOp.getResult 0)) rsOp with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (by grind [OperationPtr.getResult])
    have hLsRes₄ : s₄.variables.getVar? (ValuePtr.opResult (lsOp.getResult 0))
        = some (RuntimeValue.reg (Data.RISCV.sextw (LLVM.Int.toReg xt))) := by
      rw [hFrame₄ _ hLsNotRsRes]; exact hRes₃
    -- mOp (ls, rs).
    obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₄) (inBounds := by grind)
        (f := f) (hSemR _ _) hMType hMOperands hMResTypes hLsRes₄ hRes₄
    obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
      interpretOp_castBack_forward (state := s₅) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₅
    refine ⟨s₆, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, liftM, monadLift,
        MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int intType.bitwidth
          (RISCV.Reg.toInt (f (Data.RISCV.sextw (LLVM.Int.toReg xt))
            (Data.RISCV.sextw (LLVM.Int.toReg yt))) intType.bitwidth)], ?_, ?_⟩
      · simp [hRes₆, Option.bind, Option.map]
      · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
        obtain ⟨bw⟩ := intType; simp only at hb32; subst hb32
        simpa using hRefine32 xVal yVal xt yt _ hxtRef hytRef
  · -- ================= i64 branch =================
    rename_i hb32
    peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
    peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
    cleanupHpattern hpattern
    obtain ⟨xt, hLVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtxL hDomL₄ lNotOp
    obtain ⟨yt, hRVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
        hDomCtxR hDomR₄ rNotOp
    have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hRetType : retOp.getOpType! ctx₄.raw = .riscv rop := by grind
    have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hLCastOperands : lcastOp.getOperands! ctx₄.raw = #[lhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastOperands : rcastOp.getOperands! ctx₄.raw = #[rhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hRetOperands : retOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := retOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := retOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
    have hCBType : ((op.getResult 0).get! ctx₃.raw).type
        = (⟨Attribute.integerType intType, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRet
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hRCast
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hLCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hLCastResTypes : lcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastResTypes : rcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hRetResTypes : retOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := retOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := retOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.integerType intType, by grind⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hLCastType hLCastOperands hLCastResTypes hLVal'
    have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw rhs lcastOp
        with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (hRhsNeLCastRes i)
    have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int intType.bitwidth yt) := by
      rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
        hRCastType hRCastOperands hRCastResTypes hRVal₁
    have hLCastNotRCastRes :
        ValuePtr.opResult (lcastOp.getResult 0) ∉ rcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw
          (ValuePtr.opResult (lcastOp.getResult 0)) rcastOp with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (by grind [OperationPtr.getResult])
    have hLRes₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
        (f := f) (hSemR _ _) hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.int intType.bitwidth
          (RISCV.Reg.toInt (f (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) intType.bitwidth)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
        obtain ⟨bw⟩ := intType; simp only at hb32 hBw ⊢
        have hbw : bw = 64 := by omega
        subst hbw
        simpa using hRefine64 xVal yVal xt yt _ hxtRef hytRef

/-!
## RISC-V lowering of `llvm.intr.smax` and `llvm.intr.smin`

`llvm.intr.smax`/`smin` on 64- or 32-bit integers is lowered to two `unrealized_conversion_cast`s
(operands to registers) → `riscv.max`/`riscv.min` → `unrealized_conversion_cast` (back to the integer
type); for `i32` each register operand is first sign-extended with `riscv.sextw`. These are the actual
`Veir.smax_local`/`Veir.smin_local` patterns.

The structural part of the proof is shared with `lowerSignedMinMaxLocal_preservesSemantics`; only the
data-level refinement lemmas per op/width are `smax`/`smin`-specific. As with the other binary
lowerings, the interpreter applies the data-level op as `RISCV.op op2 op1`, so the lemmas take
`(toReg yt)` (or `sextw (toReg yt)` for `i32`) first.
-/

/-- Correctness of the `riscv.max` lowering of a 64-bit `llvm.intr.smax`. -/
theorem smax_isRefinedBy_toInt_max {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.smax x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.max (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_smax] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_smax] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.max]
  veir_bv_decide

/-- Correctness of the `riscv.max` lowering of a 32-bit `llvm.intr.smax`: the operands are
    sign-extended (`riscv.sextw`) before the signed compare. -/
theorem smax_isRefinedBy_toInt_max_32 {x y xt yt : Data.LLVM.Int 32}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.smax x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.max (Data.RISCV.sextw (LLVM.Int.toReg yt))
          (Data.RISCV.sextw (LLVM.Int.toReg xt))) 32 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_smax] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_smax] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.max, Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

theorem smax_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics smax_local h h₂ h₃ h₄ :=
  lowerSignedMinMaxLocal_preservesSemantics
    (srcOp := .intr__smax)
    (srcFn := fun x y _ => Data.LLVM.Int.smax x y)
    (f := fun r₁ r₂ => Data.RISCV.max r₂ r₁)
    matchSmax_implies
    OperationPtr.Verified.llvm_intr__smax
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ h₁ h₂ => smax_isRefinedBy_toInt_max h₁ h₂)
    (fun _ _ _ _ _ h₁ h₂ => smax_isRefinedBy_toInt_max_32 h₁ h₂)

/-- Correctness of the `riscv.min` lowering of a 64-bit `llvm.intr.smin`. -/
theorem smin_isRefinedBy_toInt_min {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.smin x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.min (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_smin] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_smin] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.min]
  veir_bv_decide

/-- Correctness of the `riscv.min` lowering of a 32-bit `llvm.intr.smin`: the operands are
    sign-extended (`riscv.sextw`) before the signed compare. -/
theorem smin_isRefinedBy_toInt_min_32 {x y xt yt : Data.LLVM.Int 32}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.smin x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.min (Data.RISCV.sextw (LLVM.Int.toReg yt))
          (Data.RISCV.sextw (LLVM.Int.toReg xt))) 32 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_smin] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_smin] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.min, Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

theorem smin_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics smin_local h h₂ h₃ h₄ :=
  lowerSignedMinMaxLocal_preservesSemantics
    (srcOp := .intr__smin)
    (srcFn := fun x y _ => Data.LLVM.Int.smin x y)
    (f := fun r₁ r₂ => Data.RISCV.min r₂ r₁)
    matchSmin_implies
    OperationPtr.Verified.llvm_intr__smin
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ h₁ h₂ => smin_isRefinedBy_toInt_min h₁ h₂)
    (fun _ _ _ _ _ h₁ h₂ => smin_isRefinedBy_toInt_min_32 h₁ h₂)

end Veir
