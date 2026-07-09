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

namespace Veir

/-!
## Generic correctness of `lowerUnaryWLocal`

`lowerUnaryWLocal match? op64 op32` lowers a single-operand LLVM integer op to
`unrealized_conversion_cast` (to a register) → `riscv` op (`op64`, or its `W` variant `op32` for
`i32`) → `unrealized_conversion_cast` (back to the integer type). Its `PreservesSemantics` proof
is shared: instantiating it for a concrete lowering (`ctlz_local`, `cttz_local`, `ctpop_local`)
only requires the matcher facts, the interpreter computation facts (all `rfl`), and the two
data-level refinement lemmas.
-/

/-- Interpreting a matched single-operand LLVM op (of opcode `srcOp`, interpreted by `srcFn` per
    `hSemSrc`) whose operand has integer type `intType` reads that operand's `i{bw}` value `x` and
    stores `srcFn x props` in the result variable, leaving memory and control flow untouched. The
    operand's value `x` is derived internally (from the successful interpretation and the
    operand's type), so it is exposed as an existential output rather than required as an input. -/
theorem matchUnaryOp_interpretOp_unfold {srcOp : Llvm} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {operand : ValuePtr} {props : propertiesOf (.llvm srcOp)} {intType}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → propertiesOf (.llvm srcOp) → Data.LLVM.Int bw}
    {state : InterpreterState ctx} {newState cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm srcOp)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[operand])
    (hProps : props = op.getProperties! ctx.raw (.llvm srcOp))
    (hSemSrc : ∀ (bw : Nat) (x : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x] blockOperands mem
          = some (.ok (#[.int bw (srcFn x props)], mem, none)))
    (hinterp : interpretOp op state opInBounds = some (newState, cf))
    (hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ x, state.variables.getVar? operand = some (RuntimeValue.int intType.bitwidth x) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int intType.bitwidth (srcFn x props)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 1 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by
    rw [hOperands]; rfl
  simp only [liftM, monadLift, MonadLift.monadLift] at hinterp
  -- Derive the operand's `i{bw}` value from the successful interpretation and its integer type.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨val, hval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize
  have hgetVar : state.variables.getVar? operand = some val := by
    rw [hOperandEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hval
  have hconf := VariableState.getVar?_conforms hgetVar
  rw [show operand.getType! ctx.raw = ⟨.integerType intType, hOperandType ▸ (operand.getType! ctx.raw).2⟩
        from Subtype.ext hOperandType] at hconf
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType hconf
  refine ⟨x, hgetVar, ?_⟩
  -- With the value in hand, unfold the interpretation of the matched op.
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op = some #[RuntimeValue.int intType.bitwidth x] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    obtain rfl : i = 0 := by omega
    simpa [hOperand0] using hgetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [← hProps, interpretOp'] at hInterp'
  rw [hSemSrc] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ : resValues = #[RuntimeValue.int intType.bitwidth (srcFn x props)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for every `lowerUnaryWLocal` lowering: the round trip
    `int → reg → op64/op32 → int` refines `srcFn`.

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier facts
    (`hVerified`), the interpreter computation facts for the source op and the two riscv ops
    (`hSemSrc`/`hSemR64`/`hSemR32`, all discharged by `rfl` at concrete opcodes), and the two
    data-level refinement lemmas (`hRefine64`/`hRefine32`). -/
theorem lowerUnaryWLocal_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × propertiesOf (.llvm srcOp))}
    {op64 op32 : Riscv}
    {props64 : propertiesOf (.riscv op64)} {props32 : propertiesOf (.riscv op32)}
    {f64 f32 : Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → propertiesOf (.llvm srcOp) → Data.LLVM.Int bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {operand props},
        match? op ctx = some (operand, props) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[operand] ∧
        props = op.getProperties! ctx (.llvm srcOp))
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedIntegerUnop ctx)
    (hSemSrc : ∀ (bw : Nat) (x : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x] blockOperands mem
          = some (.ok (#[.int bw (srcFn x props)], mem, none)))
    (hSemR64 : ∀ (r : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op64)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op64 props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (f64 r)], mem, none)))
    (hSemR32 : ∀ (r : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op32)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op32 props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (f32 r)], mem, none)))
    (hRefine64 : ∀ (x xt : Data.LLVM.Int 64) (props : propertiesOf (.llvm srcOp)), x ⊒ xt →
        srcFn x props ⊒ RISCV.Reg.toInt (f64 (LLVM.Int.toReg xt)) 64)
    (hRefine32 : ∀ (x xt : Data.LLVM.Int 32) (props : propertiesOf (.llvm srcOp)), x ⊒ xt →
        srcFn x props ⊒ RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt)) 32)
    {h : LocalRewritePattern.ReturnOps (lowerUnaryWLocal match? op64 op32 props64 props32)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (lowerUnaryWLocal match? op64 op32 props64 props32)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (lowerUnaryWLocal match? op64 op32 props64 props32)}
    {h₄ : LocalRewritePattern.ReturnValues (lowerUnaryWLocal match? op64 op32 props64 props32)} :
    LocalRewritePattern.PreservesSemantics
      (lowerUnaryWLocal match? op64 op32 props64 props32) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lowerUnaryWLocal]
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
  obtain ⟨⟨operand, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := hMatchImplies hMatch
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by
    rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, hResOperType, intType, isT, hResType⟩ :=
    hVerified opVerif hOpType
  -- The operand type is the integer type `intType`; resolve the type-destructuring match.
  have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [show operand.getType! ctx.raw = ⟨.integerType intType, isT⟩ from by grind]
  rw [hOperandType] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand's value and its `srcFn`.
  obtain ⟨xVal, hxVal, hMem, hRes, hCf⟩ :=
    matchUnaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps hSemSrc
      hinterp hOperandType
  subst hCf
  -- The matched operand dominates the rewrite point in the source context.
  have hDomCtx : operand.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  peelSplittableCondition [hBw] hpattern
  -- Source value: `op`'s single result is `srcFn` of its operand.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `operand` is not one of `op`'s results.
  have vNotOp : ¬ operand ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the first `castToRegLocal` creation (a `builtin.unrealized_conversion_cast`),
  -- transporting the operand's dominance fact `hDomCtx` into `ctx₁` as `hDom₁`.
  peelCastToRegLocal hpattern ctx₁ castOp hCast hDomCtx hDom₁
  have hBwCases : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  rcases hBwCases with hbw | hbw
  · -- 64-bit case: lowered to `op64`
    rw [if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    simp only [] at hpattern
    -- Peel the `op64` creation and the `replaceWithRegLocal` cast-back, converting each
    -- from the `createOp!`/helper form to plain `createOp` (`hCast` was already converted by
    -- `peelCastToRegLocal`).
    peelOpCreation! hpattern ctx₂ retOp hRet hDom₁ hDom₂
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    -- Read the refined value `xt` of `operand` in the target state `state'`.
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtx hDom₃ vNotOp
    -- Normalise the bitwidth to the literal `64`.
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Structural facts about the three created ops.
    have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRetType : retOp.getOpType! ctx₃.raw = .riscv op64 := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[operand] := by grind
    have hRetOperands : retOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
    -- The cast-back op's result type is `i64`.
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRet
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hRetResTypes : retOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := retOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := retOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.integerType { bitwidth := 64 }, isT⟩] := by grind
    -- Interpretation tail: execute `interpretOpList [castOp, retOp, castBackOp]` in `state'`:
    -- one cast-forward lemma per cast, one `interpretOp_riscv_unaryReg_forward` for the middle op.
    -- `castOp` reads `operand = .int 64 xt` and casts it to `.reg (toReg xt)`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    -- `retOp` (`op64`) maps `.reg r` to `.reg (f64 r)`.
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
        (f := f64) (hSemR64 _) hRetType hRetOperands hRetResTypes hRes₁
    -- `castBackOp` casts `.reg (f64 (toReg xt))` back to `.int 64 (toInt (f64 (toReg xt)) 64)`.
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · -- The list interpretation is the chain of the three op interpretations.
      simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt (f64 (LLVM.Int.toReg xt)) 64)],
        ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine64 xVal xt props hxtRef⟩
  · -- 32-bit case: lowered to `op32`
    rw [if_pos hbw] at hpattern
    simp only [] at hpattern
    -- Peel the `op32` creation and the `replaceWithRegLocal` cast-back, converting each
    -- from the `createOp!`/helper form to plain `createOp` (`hCast` was already converted by
    -- `peelCastToRegLocal`).
    peelOpCreation! hpattern ctx₂ retOp hRet hDom₁ hDom₂
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    -- Read the refined value `xt` of `operand` in the target state `state'`.
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtx hDom₃ vNotOp
    -- Normalise the bitwidth to the literal `32`.
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Structural facts about the three created ops.
    have hRetType : retOp.getOpType! ctx₃.raw = .riscv op32 := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[operand] := by grind
    have hRetOperands : retOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
    -- The cast-back op's result type is `i32`.
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRet
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hRetResTypes : retOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := retOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := retOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.integerType { bitwidth := 32 }, isT⟩] := by grind
    -- Interpretation tail: execute `interpretOpList [castOp, retOp, castBackOp]` in `state'`:
    -- one cast-forward lemma per cast, one `interpretOp_riscv_unaryReg_forward` for the middle op.
    -- `castOp` reads `operand = .int 32 xt` and casts it to `.reg (toReg xt)`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        (by grind) hCastOperands hCastResTypes hOpVal'
    -- `retOp` (`op32`) maps `.reg r` to `.reg (f32 r)`.
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
        (f := f32) (hSemR32 _) hRetType hRetOperands hRetResTypes hRes₁
    -- `castBackOp` casts `.reg (f32 (toReg xt))` back to `.int 32 (toInt (f32 (toReg xt)) 32)`.
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        (by grind) hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · -- The list interpretation is the chain of the three op interpretations.
      simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 32 (RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt)) 32)],
        ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine32 xVal xt props hxtRef⟩

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## RISC-V lowering of `llvm.intr.ctlz`

`llvm.intr.ctlz` on a 64- or 32-bit integer is lowered to
`unrealized_conversion_cast` (to a register) → `riscv.clz`/`riscv.clzw` →
`unrealized_conversion_cast` (back to the integer type). This is the actual
`Veir.ctlz_local` pattern from `Veir.Passes.InstructionSelection.RISCV64`.

The structural part of the proof is shared with the other unary lowerings
(`lowerUnaryWLocal_preservesSemantics`); only the two data-level refinement
lemmas below are `ctlz`-specific.
-/

/-- Correctness of the `riscv.clz` lowering of a 64-bit `llvm.intr.ctlz`: the round trip
    `int → reg → clz → int` refines `ctlz`. (`xt` is the possibly-more-defined target-side value
    of the operand.) -/
theorem ctlz_isRefinedBy_toInt_clz {x xt : Data.LLVM.Int 64} (pf : Bool) (h : x ⊒ xt) :
    Data.LLVM.Int.ctlz x pf ⊒ RISCV.Reg.toInt (Data.RISCV.clz (LLVM.Int.toReg xt)) 64 := by
  revert h
  veir_bv_decide

/-- Correctness of the `riscv.clzw` lowering of a 32-bit `llvm.intr.ctlz`. -/
theorem ctlz_isRefinedBy_toInt_clzw {x xt : Data.LLVM.Int 32} (pf : Bool) (h : x ⊒ xt) :
    Data.LLVM.Int.ctlz x pf ⊒ RISCV.Reg.toInt (Data.RISCV.clzw (LLVM.Int.toReg xt)) 32 := by
  revert h
  veir_bv_decide

theorem ctlz_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics ctlz_local h h₂ h₃ h₄ :=
  lowerUnaryWLocal_preservesSemantics
    (srcOp := .intr__ctlz)
    (srcFn := fun x props => Data.LLVM.Int.ctlz x props.is_zero_poison)
    (f64 := Data.RISCV.clz) (f32 := Data.RISCV.clzw)
    matchCtlz_implies
    OperationPtr.Verified.llvm_intr__ctlz
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ props h => ctlz_isRefinedBy_toInt_clz props.is_zero_poison h)
    (fun _ _ props h => ctlz_isRefinedBy_toInt_clzw props.is_zero_poison h)

/-!
## RISC-V lowering of `llvm.intr.ctpop`

`llvm.intr.ctpop` on a 64- or 32-bit integer is lowered to
`unrealized_conversion_cast` (to a register) → `riscv.cpop`/`riscv.cpopw` →
`unrealized_conversion_cast` (back to the integer type). The structural part of the proof is
shared with the other unary lowerings (`lowerUnaryWLocal_preservesSemantics`); only the two
data-level refinement lemmas below are `ctpop`-specific.
-/

/-- Correctness of the `riscv.cpop` lowering of a 64-bit `llvm.intr.ctpop`: the round trip
    `int → reg → cpop → int` refines `ctpop`. (`xt` is the possibly-more-defined target-side
    value of the operand.) -/
theorem ctpop_isRefinedBy_toInt_cpop {x xt : Data.LLVM.Int 64} (h : x ⊒ xt) :
    Data.LLVM.Int.ctpop x ⊒ RISCV.Reg.toInt (Data.RISCV.cpop (LLVM.Int.toReg xt)) 64 := by
  revert h
  veir_bv_decide

/-- Correctness of the `riscv.cpopw` lowering of a 32-bit `llvm.intr.ctpop`. -/
theorem ctpop_isRefinedBy_toInt_cpopw {x xt : Data.LLVM.Int 32} (h : x ⊒ xt) :
    Data.LLVM.Int.ctpop x ⊒ RISCV.Reg.toInt (Data.RISCV.cpopw (LLVM.Int.toReg xt)) 32 := by
  revert h
  veir_bv_decide

theorem ctpop_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics ctpop_local h h₂ h₃ h₄ :=
  lowerUnaryWLocal_preservesSemantics
    (srcOp := .intr__ctpop)
    (srcFn := fun x _ => Data.LLVM.Int.ctpop x)
    (f64 := Data.RISCV.cpop) (f32 := Data.RISCV.cpopw)
    matchCtpop_implies
    OperationPtr.Verified.llvm_intr__ctpop
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ h => ctpop_isRefinedBy_toInt_cpop h)
    (fun _ _ _ h => ctpop_isRefinedBy_toInt_cpopw h)

/-!
## RISC-V lowering of `llvm.intr.cttz`

`llvm.intr.cttz` on a 64- or 32-bit integer is lowered to
`unrealized_conversion_cast` (to a register) → `riscv.ctz`/`riscv.ctzw` →
`unrealized_conversion_cast` (back to the integer type). The structural part of the proof is
shared with the other unary lowerings (`lowerUnaryWLocal_preservesSemantics`); only the two
data-level refinement lemmas below are `cttz`-specific.
-/

/-- Correctness of the `riscv.ctz` lowering of a 64-bit `llvm.intr.cttz`: the round trip
    `int → reg → ctz → int` refines `cttz`. (`xt` is the possibly-more-defined target-side value
    of the operand.) -/
theorem cttz_isRefinedBy_toInt_ctz {x xt : Data.LLVM.Int 64} (pf : Bool) (h : x ⊒ xt) :
    Data.LLVM.Int.cttz x pf ⊒ RISCV.Reg.toInt (Data.RISCV.ctz (LLVM.Int.toReg xt)) 64 := by
  revert h
  veir_bv_decide

/-- Correctness of the `riscv.ctzw` lowering of a 32-bit `llvm.intr.cttz`. -/
theorem cttz_isRefinedBy_toInt_ctzw {x xt : Data.LLVM.Int 32} (pf : Bool) (h : x ⊒ xt) :
    Data.LLVM.Int.cttz x pf ⊒ RISCV.Reg.toInt (Data.RISCV.ctzw (LLVM.Int.toReg xt)) 32 := by
  revert h
  veir_bv_decide

theorem cttz_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics cttz_local h h₂ h₃ h₄ :=
  lowerUnaryWLocal_preservesSemantics
    (srcOp := .intr__cttz)
    (srcFn := fun x props => Data.LLVM.Int.cttz x props.is_zero_poison)
    (f64 := Data.RISCV.ctz) (f32 := Data.RISCV.ctzw)
    matchCttz_implies
    OperationPtr.Verified.llvm_intr__cttz
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ props h => cttz_isRefinedBy_toInt_ctz props.is_zero_poison h)
    (fun _ _ props h => cttz_isRefinedBy_toInt_ctzw props.is_zero_poison h)

end Veir
