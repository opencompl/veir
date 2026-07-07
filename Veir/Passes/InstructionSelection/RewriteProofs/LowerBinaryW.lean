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

namespace Veir

/-!
## Generic correctness of `lowerBinaryWLocal`

`lowerBinaryWLocal match? op64 op32` lowers a two-operand LLVM integer op to
`unrealized_conversion_cast` (each operand to a register) → `riscv` op (`op64`, or its `W` variant
`op32` for `i32`) → `unrealized_conversion_cast` (back to the integer type). Its
`PreservesSemantics` proof is shared: instantiating it for a concrete lowering (`add_local`,
`xor_local`, …) only requires the matcher facts, the interpreter computation facts, and the two
data-level refinement lemmas.
-/

/-- Interpreting a matched two-operand LLVM op (of opcode `srcOp`, interpreted by `srcFn` per
    `hSemSrc`) whose operands both have integer type `intType` reads the operands' `i{bw}` values
    `x` and `y` and stores `srcFn x y props` in the result variable, leaving memory and control
    flow untouched. The operand values are derived internally (from the successful interpretation
    and the operands' types), so they are exposed as existential outputs rather than required as
    inputs. -/
theorem matchBinaryOp_interpretOp_unfold {srcOp : Llvm} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {lhs rhs : ValuePtr} {props : propertiesOf (.llvm srcOp)} {intType}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {state : InterpreterState ctx} {newState cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm srcOp)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[lhs, rhs])
    (hProps : props = op.getProperties! ctx.raw (.llvm srcOp))
    (hSemSrc : ∀ (bw : Nat) (x y : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw y] blockOperands mem
          = some (.ok (#[.int bw (srcFn x y props)], mem, none)))
    (hinterp : interpretOp op state opInBounds = some (newState, cf))
    (hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType)
    (hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ x y, state.variables.getVar? lhs = some (RuntimeValue.int intType.bitwidth x) ∧
      state.variables.getVar? rhs = some (RuntimeValue.int intType.bitwidth y) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int intType.bitwidth (srcFn x y props)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 2 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by
    rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by
    rw [hOperands]; rfl
  simp only [liftM, monadLift, MonadLift.monadLift] at hinterp
  -- Derive the operands' `i{bw}` values from the successful interpretation and their types.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize0 : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize1 : 1 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨lval, hlval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize0
  obtain ⟨rval, hrval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 1 hsize1
  have hlGetVar : state.variables.getVar? lhs = some lval := by
    rw [hLhsEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hlval
  have hrGetVar : state.variables.getVar? rhs = some rval := by
    rw [hRhsEq, show (op.getOperands! ctx.raw)[1]! = (op.getOperands! ctx.raw)[1] from by grind]
    exact hrval
  have hlconf := VariableState.getVar?_conforms hlGetVar
  rw [show lhs.getType! ctx.raw = ⟨.integerType intType, hLhsType ▸ (lhs.getType! ctx.raw).2⟩
        from Subtype.ext hLhsType] at hlconf
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType hlconf
  have hrconf := VariableState.getVar?_conforms hrGetVar
  rw [show rhs.getType! ctx.raw = ⟨.integerType intType, hRhsType ▸ (rhs.getType! ctx.raw).2⟩
        from Subtype.ext hRhsType] at hrconf
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType hrconf
  refine ⟨x, y, hlGetVar, hrGetVar, ?_⟩
  -- With the values in hand, unfold the interpretation of the matched op.
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.int intType.bitwidth x, RuntimeValue.int intType.bitwidth y] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · simpa [hOperand0] using hlGetVar
    · simpa [hOperand1] using hrGetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [← hProps, interpretOp'] at hInterp'
  rw [hSemSrc] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ : resValues = #[RuntimeValue.int intType.bitwidth (srcFn x y props)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for every `lowerBinaryWLocal` lowering: the round trip
    `int × int → reg × reg → op64/op32 → int` refines `srcFn`.

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier facts
    (`hVerified`), the interpreter computation facts for the source op and the two riscv ops
    (`hSemSrc`/`hSemR64`/`hSemR32`, discharged by `simp`/`rfl` at concrete opcodes), and the two
    data-level refinement lemmas (`hRefine64`/`hRefine32`). -/
theorem lowerBinaryWLocal_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode →
      Option (ValuePtr × ValuePtr × propertiesOf (.llvm srcOp))}
    {op64 op32 : Riscv}
    {props64 : propertiesOf (.riscv op64)} {props32 : propertiesOf (.riscv op32)}
    {f64 f32 : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
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
    (hSemR64 : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op64)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op64 props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f64 r₁ r₂)], mem, none)))
    (hSemR32 : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op32)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op32 props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f32 r₁ r₂)], mem, none)))
    (hRefine64 : ∀ (x y xt yt : Data.LLVM.Int 64) (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcFn x y props ⊒ RISCV.Reg.toInt (f64 (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 64)
    (hRefine32 : ∀ (x y xt yt : Data.LLVM.Int 32) (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcFn x y props ⊒ RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 32)
    {h : LocalRewritePattern.ReturnOps (lowerBinaryWLocal match? op64 op32 props64 props32)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (lowerBinaryWLocal match? op64 op32 props64 props32)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (lowerBinaryWLocal match? op64 op32 props64 props32)}
    {h₄ : LocalRewritePattern.ReturnValues (lowerBinaryWLocal match? op64 op32 props64 props32)} :
    LocalRewritePattern.PreservesSemantics
      (lowerBinaryWLocal match? op64 op32 props64 props32) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lowerBinaryWLocal]
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
  obtain ⟨⟨lhs, rhs, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := hMatchImplies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by
    rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by
    rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    hVerified opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- Both operand types are the integer type `intType`; resolve the type-destructuring matches.
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  rw [hLhsType, hRhsType] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand values and their `srcFn`.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps hSemSrc
      hinterp hLhsType hRhsType
  subst hCf
  -- The matched operands dominate the rewrite point in the source context.
  have hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guards must be false (otherwise the RHS would be `some (ctx, none)`); both
  -- guards check the same condition (`lhs`/`rhs` share `intType`), so one split resolves both.
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
  -- Peel the two `castToRegLocal` creations (`builtin.unrealized_conversion_cast`s), transporting
  -- both operand dominance facts into `ctx₁` and then `ctx₂`.
  peelCastToRegLocal₂ hpattern ctx₁ lcastOp hLCast hDomCtxL hDomL₁ hDomCtxR hDomR₁
  peelCastToRegLocal₂ hpattern ctx₂ rcastOp hRCast hDomL₁ hDomL₂ hDomR₁ hDomR₂
  -- Freshness facts, used to keep values of earlier ops alive across later interpretation steps:
  -- `rhs` (in bounds in the original context) is not a result of the fresh `lcastOp`, and the two
  -- cast ops are distinct.
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
  have hBwCases : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  rcases hBwCases with hbw | hbw
  · -- 64-bit case: lowered to `op64`
    rw [if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    simp only [] at hpattern
    -- Peel the `op64` creation and the `replaceWithRegLocal` cast-back, converting each
    -- from the `createOp!`/helper form to plain `createOp`.
    peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
    peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
    cleanupHpattern hpattern
    -- Read the refined values `xt`/`yt` of `lhs`/`rhs` in the target state `state'`.
    obtain ⟨xt, hLVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtxL hDomL₄ lNotOp
    obtain ⟨yt, hRVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
        hDomCtxR hDomR₄ rNotOp
    -- Normalise the bitwidth to the literal `64`.
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Structural facts about the four created ops.
    have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hRetType : retOp.getOpType! ctx₄.raw = .riscv op64 := by grind
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
    -- The cast-back op's result type is `i64`.
    have hCBType : ((op.getResult 0).get! ctx₃.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
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
        = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
    -- Interpretation tail: execute `interpretOpList [lcastOp, rcastOp, retOp, castBackOp]` in
    -- `state'`: one cast-forward lemma per cast, the binary forward lemma for the riscv op. The
    -- frame clauses carry earlier bindings across later steps.
    -- `lcastOp` reads `lhs = .int 64 xt` and casts it to `.reg (toReg xt)`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hLCastType hLCastOperands hLCastResTypes hLVal'
    -- `rhs`'s value survives `lcastOp`'s interpretation: `rhs` (in bounds in the original
    -- context) cannot be a result of the freshly created `lcastOp`.
    have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw rhs lcastOp
        with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (hRhsNeLCastRes i)
    have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 64 yt) := by
      rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
    -- `rcastOp` reads `rhs = .int 64 yt` and casts it to `.reg (toReg yt)`.
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
        hRCastType hRCastOperands hRCastResTypes hRVal₁
    -- `lcastOp`'s result survives `rcastOp`'s interpretation: the two cast ops are distinct.
    have hLCastNotRCastRes :
        ValuePtr.opResult (lcastOp.getResult 0) ∉ rcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw
          (ValuePtr.opResult (lcastOp.getResult 0)) rcastOp with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (by grind [OperationPtr.getResult])
    have hLRes₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
    -- `retOp` (`op64`) maps `.reg r₁`, `.reg r₂` to `.reg (f64 r₁ r₂)`.
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
        (f := f64) (hSemR64 _ _) hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
    -- `castBackOp` casts `.reg (f64 (toReg xt) (toReg yt))` back to the `i64` result.
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · -- The list interpretation is the chain of the four op interpretations.
      simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.int 64
          (RISCV.Reg.toInt (f64 (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 64)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine64 xVal yVal xt yt props hxtRef hytRef⟩
  · -- 32-bit case: lowered to `op32`
    rw [if_pos hbw] at hpattern
    simp only [] at hpattern
    -- Peel the `op32` creation and the `replaceWithRegLocal` cast-back, converting each
    -- from the `createOp!`/helper form to plain `createOp`.
    peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
    peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
    cleanupHpattern hpattern
    -- Read the refined values `xt`/`yt` of `lhs`/`rhs` in the target state `state'`.
    obtain ⟨xt, hLVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtxL hDomL₄ lNotOp
    obtain ⟨yt, hRVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
        hDomCtxR hDomR₄ rNotOp
    -- Normalise the bitwidth to the literal `32`.
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Structural facts about the four created ops.
    have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hRetType : retOp.getOpType! ctx₄.raw = .riscv op32 := by grind
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
    -- The cast-back op's result type is `i32`.
    have hCBType : ((op.getResult 0).get! ctx₃.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, by grind⟩ : TypeAttr) := by
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
        = #[⟨Attribute.integerType { bitwidth := 32 }, by grind⟩] := by grind
    -- Interpretation tail: execute `interpretOpList [lcastOp, rcastOp, retOp, castBackOp]` in
    -- `state'`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hLCastType hLCastOperands hLCastResTypes hLVal'
    have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw rhs lcastOp
        with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (hRhsNeLCastRes i)
    have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 32 yt) := by
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
        (f := f32) (hSemR32 _ _) hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · -- The list interpretation is the chain of the four op interpretations.
      simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.int 32
          (RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 32)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine32 xVal yVal xt yt props hxtRef hytRef⟩

/-!
## RISC-V lowering of `llvm.add`

`llvm.add` on 64- or 32-bit integers is lowered to two `unrealized_conversion_cast`s (operands to
registers) → `riscv.add`/`riscv.addw` → `unrealized_conversion_cast` (back to the integer type).
This is the actual `Veir.add_local` pattern from `Veir.Passes.InstructionSelection.RISCV64`.

The structural part of the proof is shared with the other binary lowerings
(`lowerBinaryWLocal_preservesSemantics`); only the two data-level refinement lemmas below are
`add`-specific. Note the operand swap in the RISC-V ops: the interpreter applies
`RISCV.add op2 op1`, so the lemmas take `(toReg yt)` first.
-/

/-- Correctness of the `riscv.add` lowering of a 64-bit `llvm.add`: the round trip
    `int × int → reg × reg → add → int` refines `add` (with any `nsw`/`nuw` flags — if the source
    overflows into poison, refinement is trivial). -/
theorem add_isRefinedBy_toInt_add {x y xt yt : Data.LLVM.Int 64} (nsw nuw : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.add x y nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.add (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_add] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_add] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.add]
  veir_bv_decide

/-- Correctness of the `riscv.addw` lowering of a 32-bit `llvm.add`. -/
theorem add_isRefinedBy_toInt_addw {x y xt yt : Data.LLVM.Int 32} (nsw nuw : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.add x y nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.addw (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_add] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_add] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.addw]
  veir_bv_decide

theorem add_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics add_local h h₂ h₃ h₄ :=
  lowerBinaryWLocal_preservesSemantics
    (srcOp := .add)
    (srcFn := fun x y props => Data.LLVM.Int.add x y props.nsw props.nuw)
    (f64 := fun r₁ r₂ => Data.RISCV.add r₂ r₁)
    (f32 := fun r₁ r₂ => Data.RISCV.addw r₂ r₁)
    matchAdd_implies
    OperationPtr.Verified.llvm_add
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ props h₁ h₂ => add_isRefinedBy_toInt_add props.nsw props.nuw h₁ h₂)
    (fun _ _ _ _ props h₁ h₂ => add_isRefinedBy_toInt_addw props.nsw props.nuw h₁ h₂)

/-!
## RISC-V lowering of `llvm.xor`

`llvm.xor` is bitwise, so both bitwidths lower to plain `riscv.xor` (no `W` variant needed). The
structural part of the proof is shared with the other binary lowerings; only the two data-level
refinement lemmas below are `xor`-specific.
-/

/-- Correctness of the `riscv.xor` lowering of a 64-bit `llvm.xor`. -/
theorem xor_isRefinedBy_toInt_xor {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.xor x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.xor (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_xor] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_xor] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.xor]
  veir_bv_decide

/-- Correctness of the `riscv.xor` lowering of a 32-bit `llvm.xor`. -/
theorem xor_isRefinedBy_toInt_xor_32 {x y xt yt : Data.LLVM.Int 32}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.xor x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.xor (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_xor] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_xor] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.xor]
  veir_bv_decide

theorem xor_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics xor_local h h₂ h₃ h₄ :=
  lowerBinaryWLocal_preservesSemantics
    (srcOp := .xor)
    (srcFn := fun x y _ => Data.LLVM.Int.xor x y)
    (f64 := fun r₁ r₂ => Data.RISCV.xor r₂ r₁)
    (f32 := fun r₁ r₂ => Data.RISCV.xor r₂ r₁)
    matchXor_implies
    OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ h₁ h₂ => xor_isRefinedBy_toInt_xor h₁ h₂)
    (fun _ _ _ _ _ h₁ h₂ => xor_isRefinedBy_toInt_xor_32 h₁ h₂)

/-!
## RISC-V lowering of `llvm.sub`

`llvm.sub` lowers to `riscv.sub`/`riscv.subw`. Only the two data-level refinement lemmas below
are `sub`-specific.
-/

/-- Correctness of the `riscv.sub` lowering of a 64-bit `llvm.sub`. -/
theorem sub_isRefinedBy_toInt_sub {x y xt yt : Data.LLVM.Int 64} (nsw nuw : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.sub x y nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.sub (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_sub] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_sub] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.sub]
  veir_bv_decide

/-- Correctness of the `riscv.subw` lowering of a 32-bit `llvm.sub`. -/
theorem sub_isRefinedBy_toInt_subw {x y xt yt : Data.LLVM.Int 32} (nsw nuw : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.sub x y nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.subw (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_sub] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_sub] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.subw]
  veir_bv_decide

theorem sub_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics sub_local h h₂ h₃ h₄ :=
  lowerBinaryWLocal_preservesSemantics
    (srcOp := .sub)
    (srcFn := fun x y props => Data.LLVM.Int.sub x y props.nsw props.nuw)
    (f64 := fun r₁ r₂ => Data.RISCV.sub r₂ r₁)
    (f32 := fun r₁ r₂ => Data.RISCV.subw r₂ r₁)
    matchSub_implies
    OperationPtr.Verified.llvm_sub
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ props h₁ h₂ => sub_isRefinedBy_toInt_sub props.nsw props.nuw h₁ h₂)
    (fun _ _ _ _ props h₁ h₂ => sub_isRefinedBy_toInt_subw props.nsw props.nuw h₁ h₂)

/-!
## RISC-V lowering of `llvm.mul`

`llvm.mul` lowers to `riscv.mul`/`riscv.mulw`. Only the two data-level refinement lemmas below
are `mul`-specific.
-/

/-- Correctness of the `riscv.mul` lowering of a 64-bit `llvm.mul`. -/
theorem mul_isRefinedBy_toInt_mul {x y xt yt : Data.LLVM.Int 64} (nsw nuw : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.mul x y nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.mul (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_mul] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_mul] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  -- Avoid bitblasting the 64-bit multiplier: rewrite both sides to the same product instead.
  rw [Data.LLVM.Int.getValue_mul _ _ hnp, toInt_getValue]
  simp only [Data.RISCV.mul, val_toReg, Data.LLVM.Int.getValue_eq_getValueD,
    dif_neg (show ¬xt.isPoison = true by simp [hp₁ hxnp]),
    dif_neg (show ¬yt.isPoison = true by simp [hp₂ hynp]),
    BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
  rw [hvd₁, hvd₂]

/-- Correctness of the `riscv.mulw` lowering of a 32-bit `llvm.mul`. -/
theorem mul_isRefinedBy_toInt_mulw {x y xt yt : Data.LLVM.Int 32} (nsw nuw : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.mul x y nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.mulw (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_mul] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_mul] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  -- Rewrite both sides to the same 32-bit product first, so `bv_decide` sees two structurally
  -- identical multipliers instead of proving a 64-bit multiplier equivalence.
  rw [Data.LLVM.Int.getValue_mul _ _ hnp, toInt_getValue]
  simp only [Data.RISCV.mulw, val_toReg, Data.LLVM.Int.getValue_eq_getValueD,
    dif_neg (show ¬xt.isPoison = true by simp [hp₁ hxnp]),
    dif_neg (show ¬yt.isPoison = true by simp [hp₂ hynp])]
  rw [hvd₁, hvd₂]
  bv_decide

theorem mul_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics mul_local h h₂ h₃ h₄ :=
  lowerBinaryWLocal_preservesSemantics
    (srcOp := .mul)
    (srcFn := fun x y props => Data.LLVM.Int.mul x y props.nsw props.nuw)
    (f64 := fun r₁ r₂ => Data.RISCV.mul r₂ r₁)
    (f32 := fun r₁ r₂ => Data.RISCV.mulw r₂ r₁)
    matchMul_implies
    OperationPtr.Verified.llvm_mul
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ props h₁ h₂ => mul_isRefinedBy_toInt_mul props.nsw props.nuw h₁ h₂)
    (fun _ _ _ _ props h₁ h₂ => mul_isRefinedBy_toInt_mulw props.nsw props.nuw h₁ h₂)

end Veir
