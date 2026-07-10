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

namespace Veir

/-!
## Generic correctness of `lowerExtLocal`

`lowerExtLocal match? op8 op16 op32` lowers a single-operand LLVM integer *extension* op (whose
operand has integer type `i8`, `i16`, or `i32` and whose result is a strictly wider integer of
width at most 64) to `unrealized_conversion_cast` (to a register) → `riscv` extension op
(`op8`/`op16`/`op32`, selected by the *operand* width) → `unrealized_conversion_cast` (back to
the *result* type). It is the width-crossing cousin of `lowerUnaryWLocal`: the emitted 3-op chain
is identical, but the source op's result type differs from its operand type, so the interpreter
facts and the refinement obligations carry both widths. Its `PreservesSemantics` proof is shared:
instantiating it for a concrete lowering (`sext_local`, `zext_local`) only requires the matcher
facts, the interpreter computation facts, and the three data-level refinement lemmas (which are
generic in the result width, since any result width in `(opW, 64]` is accepted).
-/

/-- Interpreting a matched single-operand LLVM extension op (of opcode `srcOp`, interpreted by
    `srcFn` per `hSemSrc`) whose operand has integer type `opType` and whose single result has
    the strictly wider integer type `retType` reads the operand's `i{opW}` value `x` and stores
    `srcFn x hw props` (an `i{retW}` value) in the result variable, leaving memory and control
    flow untouched. This is the width-crossing analogue of `matchUnaryOp_interpretOp_unfold`:
    the interpretation of an extension op depends on the op's result type, so the op's result
    types are required as an input (`hResTypes`) and the semantic hypothesis `hSemSrc` is stated
    at a singleton integer result-type array. -/
theorem matchExtOp_interpretOp_unfold {srcOp : Llvm} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {operand : ValuePtr} {props : propertiesOf (.llvm srcOp)}
    {opType retType : IntegerType} {hIsTy}
    {srcFn : ∀ {w₁ w₂ : Nat}, Data.LLVM.Int w₁ → w₁ < w₂ → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int w₂}
    {state : InterpreterState ctx} {newState cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm srcOp)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[operand])
    (hProps : props = op.getProperties! ctx.raw (.llvm srcOp))
    (hResTypes : op.getResultTypes! ctx.raw = #[⟨.integerType retType, hIsTy⟩])
    (hw : opType.bitwidth < retType.bitwidth)
    (hSemSrc : ∀ (w₁ : Nat) (retTy : IntegerType) (hw : w₁ < retTy.bitwidth)
        (x : Data.LLVM.Int w₁) (props : propertiesOf (.llvm srcOp)) (hIsTy)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props #[⟨.integerType retTy, hIsTy⟩] #[.int w₁ x] blockOperands mem
          = some (.ok (#[.int retTy.bitwidth (srcFn x hw props)], mem, none)))
    (hinterp : interpretOp op state opInBounds = some (newState, cf))
    (hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType opType) :
    ∃ x, state.variables.getVar? operand = some (RuntimeValue.int opType.bitwidth x) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int retType.bitwidth (srcFn x hw props)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 1 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by
    rw [hOperands]; rfl
  simp only [liftM, monadLift, MonadLift.monadLift] at hinterp
  -- Derive the operand's `i{opW}` value from the successful interpretation and its integer type.
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
  rw [show operand.getType! ctx.raw = ⟨.integerType opType, hOperandType ▸ (operand.getType! ctx.raw).2⟩
        from Subtype.ext hOperandType] at hconf
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType hconf
  refine ⟨x, hgetVar, ?_⟩
  -- With the value in hand, unfold the interpretation of the matched op.
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op = some #[RuntimeValue.int opType.bitwidth x] := by
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
  rw [hResTypes] at hInterp'
  rw [hSemSrc _ _ hw] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ : resValues = #[RuntimeValue.int retType.bitwidth (srcFn x hw props)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for every `lowerExtLocal` lowering: the round trip
    `i{opW} → reg → op8/op16/op32 → i{retW}` refines `srcFn`.

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier facts
    (`hVerified`), the interpreter computation facts for the source op and the three riscv ops
    (`hSemSrc`/`hSemR8`/`hSemR16`/`hSemR32`), and the three data-level refinement lemmas
    (`hRefine8`/`hRefine16`/`hRefine32`), which are generic in the result width `retW ∈ (opW, 64]`. -/
theorem lowerExtLocal_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × propertiesOf (.llvm srcOp))}
    {op8 op16 op32 : Riscv}
    {props8 : propertiesOf (.riscv op8)} {props16 : propertiesOf (.riscv op16)}
    {props32 : propertiesOf (.riscv op32)}
    {f8 f16 f32 : Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {w₁ w₂ : Nat}, Data.LLVM.Int w₁ → w₁ < w₂ → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int w₂}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {operand props},
        match? op ctx = some (operand, props) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[operand] ∧
        props = op.getProperties! ctx (.llvm srcOp))
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedIntegerExtop ctx)
    (hSemSrc : ∀ (w₁ : Nat) (retTy : IntegerType) (hw : w₁ < retTy.bitwidth)
        (x : Data.LLVM.Int w₁) (props : propertiesOf (.llvm srcOp)) (hIsTy)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props #[⟨.integerType retTy, hIsTy⟩] #[.int w₁ x] blockOperands mem
          = some (.ok (#[.int retTy.bitwidth (srcFn x hw props)], mem, none)))
    (hSemR8 : ∀ (r : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op8)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op8 props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (f8 r)], mem, none)))
    (hSemR16 : ∀ (r : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op16)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op16 props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (f16 r)], mem, none)))
    (hSemR32 : ∀ (r : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op32)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op32 props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (f32 r)], mem, none)))
    (hRefine8 : ∀ (retW : Nat) (hw : 8 < retW) (_hle : retW ≤ 64) (x xt : Data.LLVM.Int 8)
        (props : propertiesOf (.llvm srcOp)), x ⊒ xt →
        srcFn x hw props ⊒ RISCV.Reg.toInt (f8 (LLVM.Int.toReg xt)) retW)
    (hRefine16 : ∀ (retW : Nat) (hw : 16 < retW) (_hle : retW ≤ 64) (x xt : Data.LLVM.Int 16)
        (props : propertiesOf (.llvm srcOp)), x ⊒ xt →
        srcFn x hw props ⊒ RISCV.Reg.toInt (f16 (LLVM.Int.toReg xt)) retW)
    (hRefine32 : ∀ (retW : Nat) (hw : 32 < retW) (_hle : retW ≤ 64) (x xt : Data.LLVM.Int 32)
        (props : propertiesOf (.llvm srcOp)), x ⊒ xt →
        srcFn x hw props ⊒ RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt)) retW)
    {h : LocalRewritePattern.ReturnOps (lowerExtLocal match? op8 op16 op32 props8 props16 props32)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges
      (lowerExtLocal match? op8 op16 op32 props8 props16 props32)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (lowerExtLocal match? op8 op16 op32 props8 props16 props32)}
    {h₄ : LocalRewritePattern.ReturnValues
      (lowerExtLocal match? op8 op16 op32 props8 props16 props32)} :
    LocalRewritePattern.PreservesSemantics
      (lowerExtLocal match? op8 op16 op32 props8 props16 props32) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lowerExtLocal]
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
  have ⟨hNRes, hNOper, hNSucc, hNReg, opIntTy, retIntTy, hOperTy, hResTy, hWlt⟩ :=
    hVerified opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The operand type is the integer type `opIntTy`; resolve the type-destructuring match.
  have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType opIntTy := by
    rw [← hOperand0, hOperTy]
  rw [hOperandType] at hpattern
  simp only [] at hpattern
  -- The legal-source-width guard must be false.
  peelSplittableCondition [hLegal] hpattern
  -- The result type is the integer type `retIntTy`; resolve the type-destructuring match.
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType retIntTy := by
    rw [hResTy]
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- The result-width guard must be false: `opW < retW ≤ 64`.
  peelSplittableCondition [hBw] hpattern
  have hRetLe : retIntTy.bitwidth ≤ 64 := by omega
  -- The op's result types, as needed by the width-dependent source interpretation.
  have hResTypes : op.getResultTypes! ctx.raw
      = #[⟨Attribute.integerType retIntTy, (by grind)⟩] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctx.raw) (index := 0)
        (by omega)
      grind
  -- Unfold the interpretation of the matched op: exposes the operand's value and its `srcFn`.
  obtain ⟨xVal, hxVal, hMem, hRes, hCf⟩ :=
    matchExtOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps hResTypes
      hWlt hSemSrc hinterp hOperandType
  subst hCf
  -- The matched operand dominates the rewrite point in the source context.
  have hDomCtx : operand.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `srcFn` of its operand.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `operand` is not one of `op`'s results.
  have vNotOp : ¬ operand ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the `castToRegLocal` creation (a `builtin.unrealized_conversion_cast`),
  -- transporting the operand's dominance fact `hDomCtx` into `ctx₁` as `hDom₁`.
  peelCastToRegLocal hpattern ctx₁ castOp hCast hDomCtx hDom₁
  -- The legal-width guard leaves three operand widths; each selects a different riscv op.
  have hBwCases : opIntTy.bitwidth = 8 ∨ opIntTy.bitwidth = 16 ∨ opIntTy.bitwidth = 32 := by
    simp [isLegalExtOpWidth] at hLegal
    omega
  rcases hBwCases with hbw | hbw | hbw
  · -- `i8` operand: lowered to `op8`
    rw [if_pos hbw] at hpattern
    simp only [] at hpattern
    peelOpCreation! hpattern ctx₂ retOp hRet hDom₁ hDom₂
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    -- Read the refined value `xt` of `operand` in the target state `state'`.
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtx hDom₃ vNotOp
    -- Normalise the operand bitwidth to the literal `8`.
    obtain ⟨bw⟩ := opIntTy; simp only at hbw; subst hbw
    -- Structural facts about the three created ops.
    have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRetType : retOp.getOpType! ctx₃.raw = .riscv op8 := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[operand] := by grind
    have hRetOperands : retOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
    -- The cast-back op's result type is `i{retW}`.
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType retIntTy, (by grind)⟩
            : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRet
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simp only [ValuePtr.getType!_opResult] at h1
      rw [h1, hResTy]
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
        = #[⟨Attribute.integerType retIntTy, (by grind)⟩] := by
      grind
    -- Interpretation tail: execute `interpretOpList [castOp, retOp, castBackOp]` in `state'`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
        (f := f8) (hSemR8 _) hRetType hRetOperands hRetResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · -- The list interpretation is the chain of the three op interpretations.
      simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int retIntTy.bitwidth
          (RISCV.Reg.toInt (f8 (LLVM.Int.toReg xt)) retIntTy.bitwidth)], ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine8 retIntTy.bitwidth hWlt hRetLe xVal xt props hxtRef⟩
  · -- `i16` operand: lowered to `op16`
    rw [if_neg (by omega), if_pos hbw] at hpattern
    simp only [] at hpattern
    peelOpCreation! hpattern ctx₂ retOp hRet hDom₁ hDom₂
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtx hDom₃ vNotOp
    -- Normalise the operand bitwidth to the literal `16`.
    obtain ⟨bw⟩ := opIntTy; simp only at hbw; subst hbw
    have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRetType : retOp.getOpType! ctx₃.raw = .riscv op16 := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[operand] := by grind
    have hRetOperands : retOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType retIntTy, (by grind)⟩
            : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRet
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simp only [ValuePtr.getType!_opResult] at h1
      rw [h1, hResTy]
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
        = #[⟨Attribute.integerType retIntTy, (by grind)⟩] := by
      grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
        (f := f16) (hSemR16 _) hRetType hRetOperands hRetResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int retIntTy.bitwidth
          (RISCV.Reg.toInt (f16 (LLVM.Int.toReg xt)) retIntTy.bitwidth)], ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine16 retIntTy.bitwidth hWlt hRetLe xVal xt props hxtRef⟩
  · -- `i32` operand: lowered to `op32`
    rw [if_neg (by omega), if_neg (by omega)] at hpattern
    simp only [] at hpattern
    peelOpCreation! hpattern ctx₂ retOp hRet hDom₁ hDom₂
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtx hDom₃ vNotOp
    -- Normalise the operand bitwidth to the literal `32`.
    obtain ⟨bw⟩ := opIntTy; simp only at hbw; subst hbw
    have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRetType : retOp.getOpType! ctx₃.raw = .riscv op32 := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[operand] := by grind
    have hRetOperands : retOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType retIntTy, (by grind)⟩
            : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRet
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simp only [ValuePtr.getType!_opResult] at h1
      rw [h1, hResTy]
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
        = #[⟨Attribute.integerType retIntTy, (by grind)⟩] := by
      grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
        (f := f32) (hSemR32 _) hRetType hRetOperands hRetResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int retIntTy.bitwidth
          (RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt)) retIntTy.bitwidth)], ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine32 retIntTy.bitwidth hWlt hRetLe xVal xt props hxtRef⟩

/-!
## Data-level refinement lemmas

The result width `retW` of an extension is any width in `(opW, 64]`, so the data-level lemmas are
generic in `retW` and cannot be closed by `bv_decide` directly. Instead, each riscv extension op
is characterised by a fixed-width value equation (`bv_decide`), and two width-generic helpers
(`sextLike_isRefinedBy_toInt`/`zextLike_isRefinedBy_toInt`) lift those equations to the round-trip
refinement statement.
-/

/-- Truncating a `64`-bit sign extension to a width `retW ≤ 64` at least as wide as the source
    is the direct sign extension to `retW`. -/
private theorem BitVec.setWidth_signExtend_of_le {opW retW : Nat} (v : BitVec opW)
    (hle : retW ≤ 64) :
    BitVec.setWidth retW (BitVec.signExtend 64 v) = BitVec.signExtend retW v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  grind

/-- Truncating a `64`-bit zero extension to a width `retW ≤ 64` at least as wide as the source
    is the direct zero extension to `retW`. -/
private theorem BitVec.setWidth_setWidth_of_le {opW retW : Nat} (v : BitVec opW)
    (hle : retW ≤ 64) :
    BitVec.setWidth retW (BitVec.setWidth 64 v) = BitVec.setWidth retW v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth]
  grind

/-- Width-generic correctness of a sign-extension lowering: if the riscv op `f` sign-extends the
    low `opW` bits of its register (hypothesis `hf`), then the round trip
    `i{opW} → reg → f → i{retW}` refines `llvm.sext` for any result width `retW ∈ (opW, 64]`.
    (`xt` is the possibly-more-defined target-side value of the operand.) -/
theorem sextLike_isRefinedBy_toInt {opW retW : Nat} (hlt : opW < retW) (hle : retW ≤ 64)
    {x xt : Data.LLVM.Int opW} {f : Data.RISCV.Reg → Data.RISCV.Reg}
    (hf : ∀ r, (f r).val = BitVec.signExtend 64 (BitVec.setWidth opW r.val))
    (h : x ⊒ xt) :
    Data.LLVM.Int.sext x retW hlt ⊒ RISCV.Reg.toInt (f (LLVM.Int.toReg xt)) retW := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_sext] at hnp; exact hnp
  have hvd : x.getValueD = xt.getValueD := by
    rw [Data.LLVM.Int.getValueD_eq, Data.LLVM.Int.getValueD_eq, dif_pos hxnp, dif_pos (hp hxnp)]
    exact hv hxnp (hp hxnp)
  rw [Data.LLVM.Int.getValue_sext, toInt_getValue, hf, val_toReg,
    dif_neg (show ¬xt.isPoison = true by simp [hp hxnp])]
  simp only [Data.LLVM.Int.getValue_eq_getValueD, hvd, BitVec.truncate_eq_setWidth]
  rw [BitVec.setWidth_setWidth_of_le xt.getValueD (by omega),
    BitVec.setWidth_eq, BitVec.setWidth_signExtend_of_le xt.getValueD hle]

/-- Width-generic correctness of a zero-extension lowering: if the riscv op `f` zero-extends the
    low `opW` bits of its register (hypothesis `hf`), then the round trip
    `i{opW} → reg → f → i{retW}` refines `llvm.zext` (for any `nneg` flag and any result width
    `retW ∈ (opW, 64]`). -/
theorem zextLike_isRefinedBy_toInt {opW retW : Nat} (hlt : opW < retW) (hle : retW ≤ 64)
    {nneg : Bool} {x xt : Data.LLVM.Int opW} {f : Data.RISCV.Reg → Data.RISCV.Reg}
    (hf : ∀ r, (f r).val = BitVec.setWidth 64 (BitVec.setWidth opW r.val))
    (h : x ⊒ xt) :
    Data.LLVM.Int.zext x retW nneg hlt ⊒ RISCV.Reg.toInt (f (LLVM.Int.toReg xt)) retW := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_zext] at hnp; grind
  have hvd : x.getValueD = xt.getValueD := by
    rw [Data.LLVM.Int.getValueD_eq, Data.LLVM.Int.getValueD_eq, dif_pos hxnp, dif_pos (hp hxnp)]
    exact hv hxnp (hp hxnp)
  rw [Data.LLVM.Int.getValue_zext, toInt_getValue, hf, val_toReg,
    dif_neg (show ¬xt.isPoison = true by simp [hp hxnp])]
  simp only [Data.LLVM.Int.getValue_eq_getValueD, hvd, BitVec.truncate_eq_setWidth]
  rw [BitVec.setWidth_setWidth_of_le xt.getValueD (by omega),
    BitVec.setWidth_eq, BitVec.setWidth_setWidth_of_le xt.getValueD hle]

/-! ### Value characterisations of the riscv extension ops -/

/-- `riscv.sextb` sign-extends the low byte. -/
theorem sextb_val (r : Data.RISCV.Reg) :
    (Data.RISCV.sextb r).val = BitVec.signExtend 64 (BitVec.setWidth 8 r.val) := by
  veir_bv_decide

/-- `riscv.sexth` sign-extends the low halfword. -/
theorem sexth_val (r : Data.RISCV.Reg) :
    (Data.RISCV.sexth r).val = BitVec.signExtend 64 (BitVec.setWidth 16 r.val) := by
  veir_bv_decide

/-- `riscv.sextw` sign-extends the low word. -/
theorem sextw_val (r : Data.RISCV.Reg) :
    (Data.RISCV.sextw r).val = BitVec.signExtend 64 (BitVec.setWidth 32 r.val) := by
  veir_bv_decide

/-- `riscv.zextb` zero-extends the low byte. -/
theorem zextb_val (r : Data.RISCV.Reg) :
    (Data.RISCV.zextb r).val = BitVec.setWidth 64 (BitVec.setWidth 8 r.val) := by
  veir_bv_decide

/-- `riscv.zexth` zero-extends the low halfword. -/
theorem zexth_val (r : Data.RISCV.Reg) :
    (Data.RISCV.zexth r).val = BitVec.setWidth 64 (BitVec.setWidth 16 r.val) := by
  veir_bv_decide

/-- `riscv.zextw` zero-extends the low word. -/
theorem zextw_val (r : Data.RISCV.Reg) :
    (Data.RISCV.zextw r).val = BitVec.setWidth 64 (BitVec.setWidth 32 r.val) := by
  veir_bv_decide

/-!
## RISC-V lowering of `llvm.sext`

`llvm.sext` from an `i8`/`i16`/`i32` operand to a strictly wider integer of width at most 64 is
lowered to `unrealized_conversion_cast` (to a register) → `riscv.sextb`/`sexth`/`sextw` →
`unrealized_conversion_cast` (back to the result type). The structural part of the proof is
shared with `zext` (`lowerExtLocal_preservesSemantics`); only the three data-level refinement
lemmas below are `sext`-specific.
-/

/-- Correctness of the `riscv.sextb` lowering of an `llvm.sext` from `i8`. -/
theorem sext_isRefinedBy_toInt_sextb {retW : Nat} (hlt : 8 < retW) (hle : retW ≤ 64)
    {x xt : Data.LLVM.Int 8} (h : x ⊒ xt) :
    Data.LLVM.Int.sext x retW hlt ⊒ RISCV.Reg.toInt (Data.RISCV.sextb (LLVM.Int.toReg xt)) retW :=
  sextLike_isRefinedBy_toInt hlt hle sextb_val h

/-- Correctness of the `riscv.sexth` lowering of an `llvm.sext` from `i16`. -/
theorem sext_isRefinedBy_toInt_sexth {retW : Nat} (hlt : 16 < retW) (hle : retW ≤ 64)
    {x xt : Data.LLVM.Int 16} (h : x ⊒ xt) :
    Data.LLVM.Int.sext x retW hlt ⊒ RISCV.Reg.toInt (Data.RISCV.sexth (LLVM.Int.toReg xt)) retW :=
  sextLike_isRefinedBy_toInt hlt hle sexth_val h

/-- Correctness of the `riscv.sextw` lowering of an `llvm.sext` from `i32`. -/
theorem sext_isRefinedBy_toInt_sextw {retW : Nat} (hlt : 32 < retW) (hle : retW ≤ 64)
    {x xt : Data.LLVM.Int 32} (h : x ⊒ xt) :
    Data.LLVM.Int.sext x retW hlt ⊒ RISCV.Reg.toInt (Data.RISCV.sextw (LLVM.Int.toReg xt)) retW :=
  sextLike_isRefinedBy_toInt hlt hle sextw_val h

/-- Interpreter computation fact for `llvm.sext` at a singleton integer result-type array. -/
theorem sext_interpretOp' (w₁ : Nat) (retTy : IntegerType) (hw : w₁ < retTy.bitwidth)
    (x : Data.LLVM.Int w₁) (props : propertiesOf (.llvm .sext)) (hIsTy)
    (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Llvm.interpretOp' .sext props #[⟨.integerType retTy, hIsTy⟩] #[.int w₁ x] blockOperands mem
      = some (.ok (#[.int retTy.bitwidth (Data.LLVM.Int.sext x retTy.bitwidth hw)], mem, none)) := by
  simp [Llvm.interpretOp', dif_neg (show ¬retTy.bitwidth ≤ w₁ by omega), pure, Interp]

theorem sext_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics sext_local h h₂ h₃ h₄ :=
  lowerExtLocal_preservesSemantics
    (srcOp := .sext)
    (srcFn := fun x hw _ => Data.LLVM.Int.sext x _ hw)
    (f8 := Data.RISCV.sextb) (f16 := Data.RISCV.sexth) (f32 := Data.RISCV.sextw)
    matchSext_implies
    OperationPtr.Verified.llvm_sext
    sext_interpretOp'
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ hw hle _ _ _ h => sext_isRefinedBy_toInt_sextb hw hle h)
    (fun _ hw hle _ _ _ h => sext_isRefinedBy_toInt_sexth hw hle h)
    (fun _ hw hle _ _ _ h => sext_isRefinedBy_toInt_sextw hw hle h)

/-!
## RISC-V lowering of `llvm.zext`

`llvm.zext` from an `i8`/`i16`/`i32` operand to a strictly wider integer of width at most 64 is
lowered to `unrealized_conversion_cast` (to a register) → `riscv.zextb`/`zexth`/`zextw` →
`unrealized_conversion_cast` (back to the result type). The structural part of the proof is
shared with `sext` (`lowerExtLocal_preservesSemantics`); only the three data-level refinement
lemmas below are `zext`-specific.
-/

/-- Correctness of the `riscv.zextb` lowering of an `llvm.zext` from `i8`. -/
theorem zext_isRefinedBy_toInt_zextb {retW : Nat} (hlt : 8 < retW) (hle : retW ≤ 64) {nneg : Bool}
    {x xt : Data.LLVM.Int 8} (h : x ⊒ xt) :
    Data.LLVM.Int.zext x retW nneg hlt
      ⊒ RISCV.Reg.toInt (Data.RISCV.zextb (LLVM.Int.toReg xt)) retW :=
  zextLike_isRefinedBy_toInt hlt hle zextb_val h

/-- Correctness of the `riscv.zexth` lowering of an `llvm.zext` from `i16`. -/
theorem zext_isRefinedBy_toInt_zexth {retW : Nat} (hlt : 16 < retW) (hle : retW ≤ 64) {nneg : Bool}
    {x xt : Data.LLVM.Int 16} (h : x ⊒ xt) :
    Data.LLVM.Int.zext x retW nneg hlt
      ⊒ RISCV.Reg.toInt (Data.RISCV.zexth (LLVM.Int.toReg xt)) retW :=
  zextLike_isRefinedBy_toInt hlt hle zexth_val h

/-- Correctness of the `riscv.zextw` lowering of an `llvm.zext` from `i32`. -/
theorem zext_isRefinedBy_toInt_zextw {retW : Nat} (hlt : 32 < retW) (hle : retW ≤ 64) {nneg : Bool}
    {x xt : Data.LLVM.Int 32} (h : x ⊒ xt) :
    Data.LLVM.Int.zext x retW nneg hlt
      ⊒ RISCV.Reg.toInt (Data.RISCV.zextw (LLVM.Int.toReg xt)) retW :=
  zextLike_isRefinedBy_toInt hlt hle zextw_val h

/-- Interpreter computation fact for `llvm.zext` at a singleton integer result-type array. -/
theorem zext_interpretOp' (w₁ : Nat) (retTy : IntegerType) (hw : w₁ < retTy.bitwidth)
    (x : Data.LLVM.Int w₁) (props : propertiesOf (.llvm .zext)) (hIsTy)
    (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Llvm.interpretOp' .zext props #[⟨.integerType retTy, hIsTy⟩] #[.int w₁ x] blockOperands mem
      = some (.ok (#[.int retTy.bitwidth (Data.LLVM.Int.zext x retTy.bitwidth props.nneg hw)],
          mem, none)) := by
  simp [Llvm.interpretOp', dif_neg (show ¬retTy.bitwidth ≤ w₁ by omega), pure, Interp]

theorem zext_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics zext_local h h₂ h₃ h₄ :=
  lowerExtLocal_preservesSemantics
    (srcOp := .zext)
    (srcFn := fun x hw props => Data.LLVM.Int.zext x _ props.nneg hw)
    (f8 := Data.RISCV.zextb) (f16 := Data.RISCV.zexth) (f32 := Data.RISCV.zextw)
    matchZext_implies
    OperationPtr.Verified.llvm_zext
    zext_interpretOp'
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ hw hle _ _ _ h => zext_isRefinedBy_toInt_zextb hw hle h)
    (fun _ hw hle _ _ _ h => zext_isRefinedBy_toInt_zexth hw hle h)
    (fun _ hw hle _ _ _ h => zext_isRefinedBy_toInt_zextw hw hle h)


/-! ## Layer-3 graph lemma for a defining `llvm.zext`

  Moved here from `LowerSlliuw.lean` so that consumers can reach it without importing that
  file (which cannot coexist with `LowerBexti` in one environment). It lives next to
  `matchExtOp_interpretOp_unfold`, its only non-trivial dependency. -/

/-- `llvm.zext` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_zext {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .zext) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

set_option maxHeartbeats 1000000 in
/-- Graph lemma for the `shl`'s base operand `base`, which is defined by a `zext`: in a source state
    satisfying `EquationLemmaAt` before `op`, `base`'s runtime value is `zext xv`, and the extended
    value `x`'s facts are recovered. The `zext` (unary, width-crossing) analogue of the `lshr` graph
    lemma; uses `matchExtOp_interpretOp_unfold`. -/
theorem zext_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x : ValuePtr} {zextOp : OperationPtr} {zProps : propertiesOf (.llvm .zext)}
    {retType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some zextOp)
    (hZext : matchZext zextOp ctx.raw = some (x, zProps))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType retType) :
    ∃ (opType : IntegerType) (hw : opType.bitwidth < retType.bitwidth)
      (xv : Data.LLVM.Int opType.bitwidth),
      state.variables.getVar? x = some (RuntimeValue.int opType.bitwidth xv) ∧
      state.variables.getVar? base = some (RuntimeValue.int retType.bitwidth
        (Data.LLVM.Int.zext xv retType.bitwidth zProps.nneg hw)) ∧
      (x.getType! ctx.raw).val = Attribute.integerType opType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
  obtain ⟨basePtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hZextType, hZextNumResults, hZextOperands, hZProps⟩ := matchZext_implies hZext
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hZextOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hbaseIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hbaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hZextVerified : basePtr.op.Verified ctx hZextOpIn := by grind
  obtain ⟨-, -, -, -, opType, retType', hxTypeV, hBaseResTypeV, hwV⟩ :=
    OperationPtr.Verified.llvm_zext hZextVerified hZextType
  -- `base`'s type (`retType`) is the `zext`'s result type (`retType'`).
  have hVTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hbaseEq]; rfl
  have hRetEq : retType = retType' := by
    have h := hBaseResTypeV
    rw [← hVTypeEq] at h
    rw [hbaseEq] at hBaseType
    grind
  subst hRetEq
  have hxIdxEq : x = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hZextOperands]; rfl
  have hZextOperand0 : basePtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType opType := by
    have := hxTypeV; rw [hZextOperand0] at this; rw [this]
  have hResTypes : basePtr.op.getResultTypes! ctx.raw
      = #[⟨Attribute.integerType retType, by grind⟩] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hZextNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hZextNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := basePtr.op) (ctx := ctx.raw)
        (index := 0) (by omega)
      grind
  -- Dominance and interpretation of the `zext`.
  have hZextDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hZextOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hZextSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hZextDefines hOperand
  have hZextDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hZextPure : basePtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_zext hZextType
  obtain ⟨cfZ, hInterpZext⟩ := stateWf basePtr.op hZextOpIn hZextPure hZextDomIp
  obtain ⟨xv, hxVal, -, hBaseResVal, -⟩ :=
    matchExtOp_interpretOp_unfold (srcOp := .zext)
      (srcFn := fun a hw props => Data.LLVM.Int.zext a _ props.nneg hw)
      (props := basePtr.op.getProperties! ctx.raw (.llvm .zext))
      hZextOpIn hZextType hZextNumResults hZextOperands rfl hResTypes hwV zext_interpretOp'
      hInterpZext hxType
  refine ⟨opType, hwV, xv, hxVal, ?_, hxType, ?_, ?_, ?_⟩
  · rw [hbaseEq, hBaseResVal, ← hZProps]
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hZextOpIn (by grind [OperationPtr.getOperands!])) hZextSDom
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hZextSDom) x
      (by grind [OperationPtr.getOperands!])

/-- `llvm.trunc` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_trunc {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .trunc) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

/-- Narrowing analog of `matchExtOp_interpretOp_unfold` for `llvm.trunc` on an integer operand:
    reads the operand's `i{opType}` value and binds the result to `Int.trunc`. -/
theorem matchTruncOp_interpretOp_unfold {ctx : WfIRContext OpCode}
    {op : OperationPtr} {operand : ValuePtr} {props : propertiesOf (.llvm .trunc)}
    {opType resType : IntegerType} {hIsTy}
    {state : InterpreterState ctx} {newState cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm .trunc)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[operand])
    (hProps : props = op.getProperties! ctx.raw (.llvm .trunc))
    (hResTypes : op.getResultTypes! ctx.raw = #[⟨.integerType resType, hIsTy⟩])
    (hw : resType.bitwidth < opType.bitwidth)
    (hSemSrc : ∀ (w₁ : Nat) (resTy : IntegerType) (hw : resTy.bitwidth < w₁)
        (x : Data.LLVM.Int w₁) (props : propertiesOf (.llvm .trunc)) (hIsTy)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' .trunc props #[⟨.integerType resTy, hIsTy⟩] #[.int w₁ x] blockOperands mem
          = some (.ok (#[.int resTy.bitwidth
              (Data.LLVM.Int.trunc x resTy.bitwidth props.nsw props.nuw hw)], mem, none)))
    (hinterp : interpretOp op state opInBounds = some (newState, cf))
    (hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType opType) :
    ∃ xv, state.variables.getVar? operand = some (RuntimeValue.int opType.bitwidth xv) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int resType.bitwidth
          (Data.LLVM.Int.trunc xv resType.bitwidth props.nsw props.nuw hw)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 1 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  simp only [liftM, monadLift, MonadLift.monadLift] at hinterp
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
  rw [show operand.getType! ctx.raw
        = ⟨.integerType opType, hOperandType ▸ (operand.getType! ctx.raw).2⟩
      from Subtype.ext hOperandType] at hconf
  obtain ⟨xv, rfl⟩ := RuntimeValue.Conforms.integerType hconf
  refine ⟨xv, hgetVar, ?_⟩
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.int opType.bitwidth xv] := by
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
  rw [hResTypes] at hInterp'
  rw [hSemSrc _ _ hw] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ : resValues = #[RuntimeValue.int resType.bitwidth
      (Data.LLVM.Int.trunc xv resType.bitwidth props.nsw props.nuw hw)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

set_option maxHeartbeats 1000000 in
/-- The narrowing (`trunc`) analogue of `zext_getVar?_of_EquationLemmaAt`: for a value `base` defined
    by an `llvm.trunc` reached through an operand of `op`, in a source state satisfying
    `EquationLemmaAt` before `op`, `base`'s runtime value is `Int.trunc xv` and the truncated value
    `x`'s facts are recovered. Since `llvm.trunc` has no `Verified` bundle, `x`'s (integer) type and
    the width relation are recovered from `base`'s (integer, given) type and the interpretation. -/
theorem trunc_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (_ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x : ValuePtr} {truncOp : OperationPtr} {tProps : propertiesOf (.llvm .trunc)}
    {retType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some truncOp)
    (hTrunc : matchTrunc truncOp ctx.raw = some (x, tProps))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType retType) :
    ∃ (opType : IntegerType) (hw : retType.bitwidth < opType.bitwidth)
      (xv : Data.LLVM.Int opType.bitwidth),
      state.variables.getVar? x = some (RuntimeValue.int opType.bitwidth xv) ∧
      state.variables.getVar? base = some (RuntimeValue.int retType.bitwidth
        (Data.LLVM.Int.trunc xv retType.bitwidth tProps.nsw tProps.nuw hw)) ∧
      (x.getType! ctx.raw).val = Attribute.integerType opType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
  obtain ⟨basePtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hTruncType, hTruncNumResults, hTruncOperands, hTProps⟩ := matchTrunc_implies hTrunc
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hTruncOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hbaseIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hbaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  -- `base`'s (integer) type, transported to the `getResult 0` reading.
  have hBaseTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hbaseEq]; rfl
  have hResTypeVal : ((basePtr.op.getResult 0).get! ctx.raw).type.val
      = Attribute.integerType retType := by
    have := hBaseType; rw [hbaseEq] at this
    rw [← hBaseTypeEq]; rw [hbaseEq]; exact this
  have hResTypeAttr : ((basePtr.op.getResult 0).get! ctx.raw).type
      = ⟨Attribute.integerType retType, hResTypeVal ▸ ((basePtr.op.getResult 0).get! ctx.raw).type.2⟩ :=
    Subtype.ext hResTypeVal
  have hResTypes : basePtr.op.getResultTypes! ctx.raw
      = #[⟨Attribute.integerType retType, hResTypeVal ▸ ((basePtr.op.getResult 0).get! ctx.raw).type.2⟩] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hTruncNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hTruncNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := basePtr.op) (ctx := ctx.raw)
        (index := 0) (by omega)
      grind
  have hxIdxEq : x = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hTruncOperands]; rfl
  have hTruncOperand0 : basePtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- Dominance and interpretation of the `trunc`.
  have hTruncDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hTruncOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hTruncSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hTruncDefines hOperand
  have hTruncDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hTruncPure : basePtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_trunc hTruncType
  obtain ⟨cfT, hInterpTrunc⟩ := stateWf basePtr.op hTruncOpIn hTruncPure hTruncDomIp
  -- Recover `x`'s value & (integer) type from the interpretation.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hInterpTrunc
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize : 0 < (basePtr.op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!,
      ← OperationPtr.getOperands!.size_eq_getNumOperands!]; simp [hTruncOperands]
  obtain ⟨val, hval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize
  have hxGetVar : state.variables.getVar? x = some val := by
    rw [hxIdxEq, show (basePtr.op.getOperands! ctx.raw)[0]! = (basePtr.op.getOperands! ctx.raw)[0]
        from by grind]
    exact hval
  -- The `trunc`'s success forces `val` to be an `.int` whose width `> retType`.
  have hOpVals : state.variables.getOperandValues basePtr.op = some #[val] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hTruncOperands], fun i hi => ?_⟩
    rw [show basePtr.op.getNumOperands! ctx.raw = 1 from by
      simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hTruncOperands]] at hi
    obtain rfl : i = 0 := by omega
    simpa [hTruncOperand0] using hxGetVar
  rw [interpretOp_some_iff] at hInterpTrunc
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hInterpTrunc
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hTruncType] at hInterp'
  simp only [← hTProps, interpretOp', Llvm.interpretOp', hResTypes] at hInterp'
  -- Case on `val`; only `.int` of a wider width survives with an integer result type.
  match val with
  | .int opBw xv =>
    rw [show (#[⟨Attribute.integerType retType,
          hResTypeVal ▸ ((basePtr.op.getResult 0).get! ctx.raw).type.2⟩] : Array TypeAttr)[0]?
        = some ⟨Attribute.integerType retType,
          hResTypeVal ▸ ((basePtr.op.getResult 0).get! ctx.raw).type.2⟩ from rfl] at hInterp'
    simp only [] at hInterp'
    split at hInterp'
    · exact absurd hInterp' (by simp)
    rename_i hlt
    have hw : retType.bitwidth < opBw := by omega
    obtain ⟨rfl, -, -⟩ : resValues = #[RuntimeValue.int retType.bitwidth
        (Data.LLVM.Int.trunc xv retType.bitwidth tProps.nsw tProps.nuw hw)] ∧
        mem' = state.memory ∧ cfT = none := by
      simp only [pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hInterp'; grind
    have hxTypeVal : (x.getType! ctx.raw).val = Attribute.integerType ⟨opBw⟩ := by
      have hconf := VariableState.getVar?_conforms hxGetVar
      rcases hxty : (x.getType! ctx.raw) with ⟨tyval, hIsTy⟩
      rw [hxty] at hconf
      cases tyval with
      | integerType t => cases t; simp only [RuntimeValue.Conforms] at hconf; subst hconf; rfl
      | _ => simp only [RuntimeValue.Conforms] at hconf
    refine ⟨⟨opBw⟩, hw, xv, hxGetVar, ?_, hxTypeVal, ?_, ?_, ?_⟩
    · rw [hbaseEq, hNew,
        VariableState.getVar?_getResult_of_setResultValues? (by rw [hTruncNumResults]; omega) hSet]
      simp
    · exact ValuePtr.dominatesIp_before_of_strictlyDominates
        (ctxDom.operand_dominates_op hTruncOpIn (by grind [OperationPtr.getOperands!])) hTruncSDom
    · grind [OperationPtr.getOperands!]
    · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
        (OperationPtr.dominates_of_strictlyDominates hTruncSDom) x
        (by grind [OperationPtr.getOperands!])
  | .byte opBw xv =>
    exfalso
    rw [show (#[⟨Attribute.integerType retType,
          hResTypeVal ▸ ((basePtr.op.getResult 0).get! ctx.raw).type.2⟩] : Array TypeAttr)[0]?
        = some ⟨Attribute.integerType retType,
          hResTypeVal ▸ ((basePtr.op.getResult 0).get! ctx.raw).type.2⟩ from rfl] at hInterp'
    simp [] at hInterp'
  | .float opBw xv => simp at hInterp'
  | .addr xv => simp at hInterp'
  | .reg xv => simp at hInterp'

/-- `llvm.sext` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_sext {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .sext) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

set_option maxHeartbeats 1000000 in
/-- The `sext` analogue of `zext_getVar?_of_EquationLemmaAt`: recovers a defining `sext`'s value
    `sext xv` and the extended value `x`'s facts. -/
theorem sext_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x : ValuePtr} {sextOp : OperationPtr} {sProps : propertiesOf (.llvm .sext)}
    {retType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some sextOp)
    (hSext : matchSext sextOp ctx.raw = some (x, sProps))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType retType) :
    ∃ (opType : IntegerType) (hw : opType.bitwidth < retType.bitwidth)
      (xv : Data.LLVM.Int opType.bitwidth),
      state.variables.getVar? x = some (RuntimeValue.int opType.bitwidth xv) ∧
      state.variables.getVar? base = some (RuntimeValue.int retType.bitwidth
        (Data.LLVM.Int.sext xv retType.bitwidth hw)) ∧
      (x.getType! ctx.raw).val = Attribute.integerType opType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
  obtain ⟨basePtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hSextType, hSextNumResults, hSextOperands, hSProps⟩ := matchSext_implies hSext
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hSextOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hbaseIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hbaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hSextVerified : basePtr.op.Verified ctx hSextOpIn := by grind
  obtain ⟨-, -, -, -, opType, retType', hxTypeV, hBaseResTypeV, hwV⟩ :=
    OperationPtr.Verified.llvm_sext hSextVerified hSextType
  have hVTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hbaseEq]; rfl
  have hRetEq : retType = retType' := by
    have h := hBaseResTypeV
    rw [← hVTypeEq] at h
    rw [hbaseEq] at hBaseType
    grind
  subst hRetEq
  have hxIdxEq : x = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hSextOperands]; rfl
  have hSextOperand0 : basePtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType opType := by
    have := hxTypeV; rw [hSextOperand0] at this; rw [this]
  have hResTypes : basePtr.op.getResultTypes! ctx.raw
      = #[⟨Attribute.integerType retType, by grind⟩] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hSextNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hSextNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := basePtr.op) (ctx := ctx.raw)
        (index := 0) (by omega)
      grind
  have hSextDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hSextOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hSextSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hSextDefines hOperand
  have hSextDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hSextPure : basePtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_sext hSextType
  obtain ⟨cfS, hInterpSext⟩ := stateWf basePtr.op hSextOpIn hSextPure hSextDomIp
  obtain ⟨xv, hxVal, -, hBaseResVal, -⟩ :=
    matchExtOp_interpretOp_unfold (srcOp := .sext)
      (srcFn := fun a hw _ => Data.LLVM.Int.sext a _ hw)
      (props := basePtr.op.getProperties! ctx.raw (.llvm .sext))
      hSextOpIn hSextType hSextNumResults hSextOperands rfl hResTypes hwV sext_interpretOp'
      hInterpSext hxType
  refine ⟨opType, hwV, xv, hxVal, ?_, hxType, ?_, ?_, ?_⟩
  · rw [hbaseEq, hBaseResVal]
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hSextOpIn (by grind [OperationPtr.getOperands!])) hSextSDom
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hSextSDom) x
      (by grind [OperationPtr.getOperands!])

end Veir
