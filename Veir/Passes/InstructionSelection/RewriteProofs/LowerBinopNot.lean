import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.InstructionSelection.RISCV64Sdag
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns

namespace Veir

/-!
## Generic correctness of `lowerBinopNotLocal`

`lowerBinopNotLocal match? dst props` lowers a two-operand LLVM integer op on `i64`, one of
whose operands is a `not` (`xor _, -1`), to `unrealized_conversion_cast` ×2 (both operands to
registers) → binary reg-reg `riscv` op `dst` → `unrealized_conversion_cast` (back to `i64`).
Its `PreservesSemantics` proof is shared: instantiating it for a concrete lowering
(`andn_local`, `orn_local`, `xnor_local`) only requires the matcher facts, the interpreter
computation facts (discharged by `rfl`/`simp` at concrete opcodes), and the two data-level
refinement lemmas (one per `not`-operand orientation).

Unlike the unary lowerings, the pattern matches *through* a defining op (`matchNot`), so the
proof is the first to use the `EquationLemmaAt` hypothesis of `PreservesSemantics`, via
`matchNot_getVar?_of_EquationLemmaAt` (`CommonGraphLemmas.lean`).
-/

set_option maxHeartbeats 1600000 in
/-- Shared correctness proof for every `lowerBinopNotLocal` lowering: the round trip
    `int ×2 → reg ×2 → dst → int` refines `srcFn` applied to the matched op's operands, one of
    which is semantically `xor y (-1)`.

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier facts
    (`hVerified`), the interpreter computation facts for the source op and the riscv op
    (`hSemSrc`/`hSemR`), and the two data-level refinement lemmas (`hRefineR` for
    `srcOp x (not y)`, `hRefineL` for `srcOp (not y) x`). -/
theorem lowerBinopNotLocal_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode →
      Option (ValuePtr × ValuePtr × propertiesOf (.llvm srcOp))}
    {dst : Riscv} {props : propertiesOf (.riscv dst)}
    {f : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat},
      Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) → Data.LLVM.Int bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props},
        match? op ctx = some (lhs, rhs, props) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[lhs, rhs] ∧
        props = op.getProperties! ctx (.llvm srcOp))
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedIntegerBinop ctx)
    (hSemSrc : ∀ (bw : Nat) (x y : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw y] blockOperands mem
          = some (.ok (#[.int bw (srcFn x y props)], mem, none)))
    (hSemR : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf dst)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' dst props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f r₁ r₂)], mem, none)))
    (hRefineR : ∀ (x y xt yt : Data.LLVM.Int 64) (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcFn x (Data.LLVM.Int.xor y (Data.LLVM.Int.constant 64 (-1))) props
          ⊒ RISCV.Reg.toInt (f (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 64)
    (hRefineL : ∀ (x y xt yt : Data.LLVM.Int 64) (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcFn (Data.LLVM.Int.xor y (Data.LLVM.Int.constant 64 (-1))) x props
          ⊒ RISCV.Reg.toInt (f (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 64)
    {h : LocalRewritePattern.ReturnOps (lowerBinopNotLocal match? dst props)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (lowerBinopNotLocal match? dst props)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (lowerBinopNotLocal match? dst props)}
    {h₄ : LocalRewritePattern.ReturnValues (lowerBinopNotLocal match? dst props)} :
    LocalRewritePattern.PreservesSemantics (lowerBinopNotLocal match? dst props) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lowerBinopNotLocal]
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
  obtain ⟨⟨lhs, rhs, matchProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := hMatchImplies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    hVerified opVerif hOpType
  -- Resolve the result-type destructuring match in the pattern.
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hBw
  -- Both operands have the integer type `intType`.
  have hLhsIdx : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsIdx : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsIdx]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsIdx]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the interpretation of the matched op: exposes both operand values and `srcFn`.
  obtain ⟨xlv, xrv, hlVal, hrVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps
      (fun bw x y props rt bo mem res h => by
        rw [hSemSrc bw x y props rt bo mem] at h
        injection h with h; injection h with h; exact h.symm)
      hinterp hLhsType hRhsType
  subst hCf
  -- Both matched operands dominate the rewrite point in the source context.
  have hDomLhs : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomRhs : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `srcFn` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- The matched operands are not results of `op`.
  have vNotOpLhs : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have vNotOpRhs : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Split on the `not`-operand orientation.
  cases hNotR : matchNot rhs ctx.raw with
  | some y =>
    -- Case A: `op x (not y)` with `x := lhs`.
    rw [hNotR] at hpattern
    simp only [] at hpattern
    -- Graph semantics of the matched `not`: pins `rhs`'s runtime value to `xor yv (-1)`.
    obtain ⟨yv, hyVal, hrhsVal, hyType, hyDomCtx, hyIn, hyNotRes⟩ :=
      matchNot_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hNotR
        (by rw [hOperands]; simp) hRhsType
    obtain rfl : xrv = Data.LLVM.Int.xor yv (Data.LLVM.Int.constant intType.bitwidth (-1)) := by
      have := hrVal.symm.trans hrhsVal
      simpa using this
    -- Peel the four op creations (in program order), transporting the dominance facts of
    -- `lhs` (via the macros) and `y` (manually) through each creation.
    peelCastToRegLocal hpattern ctx₁ xCastOp hCastX hDomLhs hDomLhs₁
    have hDomY₁ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastX
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hyDomCtx
    peelCastToRegLocal hpattern ctx₂ yCastOp hCastY hDomLhs₁ hDomLhs₂
    have hDomY₂ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastY
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomY₁
    peelOpCreation! hpattern ctx₃ retOp hRet hDomLhs₂ hDomLhs₃
    have hDomY₃ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hRet
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomY₂
    peelReplaceWithRegLocal hpattern ctx₄ castBackOp hCastBack hDomLhs₃ hDomLhs₄
    have hDomY₄ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomY₃
    cleanupHpattern hpattern
    -- Read the refined values `xt` (of `lhs`) and `yt` (of `y`) in the target state `state'`.
    obtain ⟨xt, hXVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hlVal
        hDomLhs hDomLhs₄ vNotOpLhs
    obtain ⟨yt, hYVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
        hyDomCtx hDomY₄ hyNotRes
    -- Normalise the bitwidth to the literal `64`.
    obtain ⟨bw⟩ := intType; simp only at hBw
    subst hBw
    -- Structural facts about the four created ops.
    have hCastXType : xCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastYType : yCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hRetType : retOp.getOpType! ctx₄.raw = .riscv dst := by grind
    have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastXOperands : xCastOp.getOperands! ctx₄.raw = #[lhs] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hCastX (operation := xCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCastY (operation := xCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := xCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xCastOp)]
    have hCastYOperands : yCastOp.getOperands! ctx₄.raw = #[y] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hCastY (operation := yCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := yCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := yCastOp)]
    have hRetOperands : retOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (xCastOp.getResult 0), ValuePtr.opResult (yCastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := retOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := retOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
    -- The cast-back op's result type is `i64`.
    have hCBType : ((op.getResult 0).get! ctx₃.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hCastX
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCastY
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hRet
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastXResTypes : xCastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastX (operation := xCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastY (operation := xCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := xCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xCastOp)]
    have hCastYResTypes : yCastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastY (operation := yCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := yCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := yCastOp)]
    have hRetResTypes : retOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := retOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := retOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
    -- Freshness facts for the frame clauses.
    have hyNotXCast : y ∉ xCastOp.getResults! ctx₄.raw :=
      ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hyIn (by grind)
    have hXCastNotYCast :
        ValuePtr.opResult (xCastOp.getResult 0) ∉ yCastOp.getResults! ctx₄.raw :=
      ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds (ctx := ctx₁.raw)
        (by grind [ValuePtr.InBounds, OpResultPtr.InBounds,
          OperationPtr.getNumResults!_WfRewriter_createOp hCastX (operation := xCastOp)])
        (by grind)
    -- Interpretation tail: execute
    -- `interpretOpList [xCastOp, yCastOp, retOp, castBackOp]` in `state'`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastXType hCastXOperands hCastXResTypes hXVal'
    have hYVal₁ : s₁.variables.getVar? y = some (RuntimeValue.int 64 yt) := by
      rw [hFrame₁ y hyNotXCast]; exact hYVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
        hCastYType hCastYOperands hCastYResTypes hYVal₁
    have hRes₁' : s₂.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ hXCastNotYCast]; exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
        (f := f) (hSemR _ _) hRetType hRetOperands hRetResTypes hRes₁' hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · -- The list interpretation is the chain of the four op interpretations.
      simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.int 64
          (RISCV.Reg.toInt (f (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 64)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefineR xlv yv xt yt matchProps hxtRef hytRef⟩
  | none =>
    -- Case B: `op (not y) x` with `x := rhs`.
    rw [hNotR] at hpattern
    cases hNotL : matchNot lhs ctx.raw with
    | none => rw [hNotL] at hpattern; simp at hpattern
    | some y =>
      rw [hNotL] at hpattern
      simp only [] at hpattern
      -- Graph semantics of the matched `not`: pins `lhs`'s runtime value to `xor yv (-1)`.
      obtain ⟨yv, hyVal, hlhsVal, hyType, hyDomCtx, hyIn, hyNotRes⟩ :=
        matchNot_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hNotL
          (by rw [hOperands]; simp) hLhsType
      obtain rfl : xlv = Data.LLVM.Int.xor yv (Data.LLVM.Int.constant intType.bitwidth (-1)) := by
        have := hlVal.symm.trans hlhsVal
        simpa using this
      -- Peel the four op creations, transporting the dominance facts of `rhs` and `y`.
      peelCastToRegLocal hpattern ctx₁ xCastOp hCastX hDomRhs hDomRhs₁
      have hDomY₁ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastX
        (by clear hpattern; grind) (by clear hpattern; grind)).mpr hyDomCtx
      peelCastToRegLocal hpattern ctx₂ yCastOp hCastY hDomRhs₁ hDomRhs₂
      have hDomY₂ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastY
        (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomY₁
      peelOpCreation! hpattern ctx₃ retOp hRet hDomRhs₂ hDomRhs₃
      have hDomY₃ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hRet
        (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomY₂
      peelReplaceWithRegLocal hpattern ctx₄ castBackOp hCastBack hDomRhs₃ hDomRhs₄
      have hDomY₄ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack
        (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomY₃
      cleanupHpattern hpattern
      -- Read the refined values `xt` (of `rhs`) and `yt` (of `y`) in the target state `state'`.
      obtain ⟨xt, hXVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hrVal
          hDomRhs hDomRhs₄ vNotOpRhs
      obtain ⟨yt, hYVal', hytRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
          hyDomCtx hDomY₄ hyNotRes
      -- Normalise the bitwidth to the literal `64`.
      obtain ⟨bw⟩ := intType; simp only at hBw
      subst hBw
      -- Structural facts about the four created ops.
      have hCastXType : xCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind
      have hCastYType : yCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind
      have hRetType : retOp.getOpType! ctx₄.raw = .riscv dst := by grind
      have hCastBackType :
          castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind
      have hCastXOperands : xCastOp.getOperands! ctx₄.raw = #[rhs] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hCastX (operation := xCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCastY (operation := xCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := xCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xCastOp)]
      have hCastYOperands : yCastOp.getOperands! ctx₄.raw = #[y] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hCastY (operation := yCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := yCastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := yCastOp)]
      have hRetOperands : retOp.getOperands! ctx₄.raw
          = #[ValuePtr.opResult (xCastOp.getResult 0),
              ValuePtr.opResult (yCastOp.getResult 0)] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := retOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := retOp)]
      have hCastBackOperands :
          castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
      -- The cast-back op's result type is `i64`.
      have hCBType : ((op.getResult 0).get! ctx₃.raw).type
          = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
        have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
            = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
          grind [ValuePtr.getType!_WfRewriter_createOp hCastX
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hCastY
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hRet
              (value := ValuePtr.opResult (op.getResult 0))]
        simpa only [ValuePtr.getType!_opResult, hResType] using h1
      have hCastXResTypes : xCastOp.getResultTypes! ctx₄.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastX (operation := xCastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCastY (operation := xCastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := xCastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xCastOp)]
      have hCastYResTypes : yCastOp.getResultTypes! ctx₄.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastY (operation := yCastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := yCastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := yCastOp)]
      have hRetResTypes : retOp.getResultTypes! ctx₄.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := retOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := retOp)]
      have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
          = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
      -- Freshness facts for the frame clauses.
      have hyNotXCast : y ∉ xCastOp.getResults! ctx₄.raw :=
        ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hyIn (by grind)
      have hXCastNotYCast :
          ValuePtr.opResult (xCastOp.getResult 0) ∉ yCastOp.getResults! ctx₄.raw :=
        ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds (ctx := ctx₁.raw)
          (by grind [ValuePtr.InBounds, OpResultPtr.InBounds,
          OperationPtr.getNumResults!_WfRewriter_createOp hCastX (operation := xCastOp)])
        (by grind)
      -- Interpretation tail: execute
      -- `interpretOpList [xCastOp, yCastOp, retOp, castBackOp]` in `state'`.
      obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
        interpretOp_castToReg_forward (state := state') (inBounds := by grind)
          hCastXType hCastXOperands hCastXResTypes hXVal'
      have hYVal₁ : s₁.variables.getVar? y = some (RuntimeValue.int 64 yt) := by
        rw [hFrame₁ y hyNotXCast]; exact hYVal'
      obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
        interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
          hCastYType hCastYOperands hCastYResTypes hYVal₁
      have hRes₁' : s₂.variables.getVar? (ValuePtr.opResult (xCastOp.getResult 0))
          = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
        rw [hFrame₂ _ hXCastNotYCast]; exact hRes₁
      obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
        interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
          (f := f) (hSemR _ _) hRetType hRetOperands hRetResTypes hRes₁' hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
        interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₃
      refine ⟨s₄, ?_, by grind, ?_⟩
      · -- The list interpretation is the chain of the four op interpretations.
        simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
          Interp]
      · refine ⟨#[RuntimeValue.int 64
            (RISCV.Reg.toInt (f (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 64)], ?_, ?_⟩
        · simp [hRes₄, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            ⟨rfl, by simpa using hRefineL xrv yv xt yt matchProps hxtRef hytRef⟩

/-!
## RISC-V lowering of `and x (not y)` (`riscv.andn`)

The structural part of the proof is shared (`lowerBinopNotLocal_preservesSemantics`); only the
two data-level refinement lemmas below (one per `not`-operand orientation) are `andn`-specific,
and similarly for `orn`/`xnor` further down.
-/

/-- Correctness of the `riscv.andn` lowering of `and x (not y)`: the round trip
    `int ×2 → reg ×2 → andn → int` refines `and x (xor y (-1))`. (`xt`/`yt` are the
    possibly-more-defined target-side values of the operands.) -/
theorem and_not_isRefinedBy_toInt_andn {x y xt yt : Data.LLVM.Int 64}
    (hx : x ⊒ xt) (hy : y ⊒ yt) :
    Data.LLVM.Int.and x (Data.LLVM.Int.xor y (Data.LLVM.Int.constant 64 (-1)))
      ⊒ RISCV.Reg.toInt (Data.RISCV.andn (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  revert hx hy
  veir_bv_decide

/-- Correctness of the `riscv.andn` lowering of `and (not y) x` (the `not` on the left). -/
theorem not_and_isRefinedBy_toInt_andn {x y xt yt : Data.LLVM.Int 64}
    (hx : x ⊒ xt) (hy : y ⊒ yt) :
    Data.LLVM.Int.and (Data.LLVM.Int.xor y (Data.LLVM.Int.constant 64 (-1))) x
      ⊒ RISCV.Reg.toInt (Data.RISCV.andn (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  revert hx hy
  veir_bv_decide

theorem andn_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics andn_local h h₂ h₃ h₄ :=
  lowerBinopNotLocal_preservesSemantics
    (srcOp := .and)
    (srcFn := fun x y _ => Data.LLVM.Int.and x y)
    (f := fun r₁ r₂ => Data.RISCV.andn r₂ r₁)
    matchAnd_implies
    OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ hx hy => and_not_isRefinedBy_toInt_andn hx hy)
    (fun _ _ _ _ _ hx hy => not_and_isRefinedBy_toInt_andn hx hy)

/--
info: 'Veir.andn_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 OperationPtr.strictlyDominates_trans,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 ValuePtr.dominatesIp_before_of_strictlyDominates,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 and_not_isRefinedBy_toInt_andn._native.bv_decide.ax_1_5,
 not_and_isRefinedBy_toInt_andn._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms andn_local_preservesSemantics

/-! ## RISC-V lowering of `or x (not y)` (`riscv.orn`) -/

/-- Correctness of the `riscv.orn` lowering of `or x (not y)` (any `disjoint` flag): the round
    trip `int ×2 → reg ×2 → orn → int` refines `or x (xor y (-1))`. -/
theorem or_not_isRefinedBy_toInt_orn {x y xt yt : Data.LLVM.Int 64} (disjoint : Bool)
    (hx : x ⊒ xt) (hy : y ⊒ yt) :
    Data.LLVM.Int.or x (Data.LLVM.Int.xor y (Data.LLVM.Int.constant 64 (-1))) disjoint
      ⊒ RISCV.Reg.toInt (Data.RISCV.orn (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  revert hx hy
  veir_bv_decide

/-- Correctness of the `riscv.orn` lowering of `or (not y) x` (the `not` on the left). -/
theorem not_or_isRefinedBy_toInt_orn {x y xt yt : Data.LLVM.Int 64} (disjoint : Bool)
    (hx : x ⊒ xt) (hy : y ⊒ yt) :
    Data.LLVM.Int.or (Data.LLVM.Int.xor y (Data.LLVM.Int.constant 64 (-1))) x disjoint
      ⊒ RISCV.Reg.toInt (Data.RISCV.orn (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  revert hx hy
  veir_bv_decide

theorem orn_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics orn_local h h₂ h₃ h₄ :=
  lowerBinopNotLocal_preservesSemantics
    (srcOp := .or)
    (srcFn := fun x y props => Data.LLVM.Int.or x y props.disjoint)
    (f := fun r₁ r₂ => Data.RISCV.orn r₂ r₁)
    matchOr_implies
    OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ props hx hy => or_not_isRefinedBy_toInt_orn props.disjoint hx hy)
    (fun _ _ _ _ props hx hy => not_or_isRefinedBy_toInt_orn props.disjoint hx hy)

/--
info: 'Veir.orn_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 OperationPtr.strictlyDominates_trans,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 ValuePtr.dominatesIp_before_of_strictlyDominates,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 not_or_isRefinedBy_toInt_orn._native.bv_decide.ax_1_5,
 or_not_isRefinedBy_toInt_orn._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms orn_local_preservesSemantics

/-! ## RISC-V lowering of `xor x (not y)` (`riscv.xnor`) -/

/-- Correctness of the `riscv.xnor` lowering of `xor x (not y)`: the round trip
    `int ×2 → reg ×2 → xnor → int` refines `xor x (xor y (-1))`. -/
theorem xor_not_isRefinedBy_toInt_xnor {x y xt yt : Data.LLVM.Int 64}
    (hx : x ⊒ xt) (hy : y ⊒ yt) :
    Data.LLVM.Int.xor x (Data.LLVM.Int.xor y (Data.LLVM.Int.constant 64 (-1)))
      ⊒ RISCV.Reg.toInt (Data.RISCV.xnor (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  revert hx hy
  veir_bv_decide

/-- Correctness of the `riscv.xnor` lowering of `xor (not y) x` (the `not` on the left). -/
theorem not_xor_isRefinedBy_toInt_xnor {x y xt yt : Data.LLVM.Int 64}
    (hx : x ⊒ xt) (hy : y ⊒ yt) :
    Data.LLVM.Int.xor (Data.LLVM.Int.xor y (Data.LLVM.Int.constant 64 (-1))) x
      ⊒ RISCV.Reg.toInt (Data.RISCV.xnor (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  revert hx hy
  veir_bv_decide

theorem xnor_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics xnor_local h h₂ h₃ h₄ :=
  lowerBinopNotLocal_preservesSemantics
    (srcOp := .xor)
    (srcFn := fun x y _ => Data.LLVM.Int.xor x y)
    (f := fun r₁ r₂ => Data.RISCV.xnor r₂ r₁)
    matchXor_implies
    OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ hx hy => xor_not_isRefinedBy_toInt_xnor hx hy)
    (fun _ _ _ _ _ hx hy => not_xor_isRefinedBy_toInt_xnor hx hy)

/--
info: 'Veir.xnor_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 OperationPtr.strictlyDominates_trans,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 ValuePtr.dominatesIp_before_of_strictlyDominates,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 not_xor_isRefinedBy_toInt_xnor._native.bv_decide.ax_1_5,
 xor_not_isRefinedBy_toInt_xnor._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms xnor_local_preservesSemantics

end Veir
