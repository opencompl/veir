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
## Generic correctness of `lowerRotateLocal`

`lowerRotateLocal match? op64 op32` lowers a funnel-shift LLVM op whose two data operands are
identical (a rotate) and whose *result* has type `i64` or `i32` to `unrealized_conversion_cast`
(the value operand and the shift-amount operand to registers) → `riscv` op (`op64`, or its `W`
variant `op32` for `i32`) → `unrealized_conversion_cast` (back to the integer type). It is the
rotate cousin of `lowerBinaryWLocal`: the emitted 4-op chain and the `W`-variant bitwidth branch
are identical, but the source op is *ternary* (three operands; the middle one is discarded once
`a = b` collapses `srcFn a b c` to `srcFn a a c`) and the type guard reads the *result* type
(as in `lowerBinaryRegLocal`). Its `PreservesSemantics` proof is shared: instantiating it for a
concrete lowering (`fshl`, `fshr`) only requires the matcher facts, the interpreter computation
facts, and the two data-level refinement lemmas.
-/

/-- Interpreting a matched three-operand LLVM op (of opcode `srcOp`, interpreted by `srcFn` per
    `hSemSrc`) whose operands all have integer type `intType` reads the operands' `i{bw}` values
    `xa`, `xb`, `xc` and stores `srcFn xa xb xc` in the result variable, leaving memory and control
    flow untouched. The operand values are derived internally (from the successful interpretation
    and the operands' types), so they are exposed as existential outputs rather than required as
    inputs. This is the ternary analogue of `matchBinaryOp_interpretOp_unfold`. -/
theorem matchTernaryOp_interpretOp_unfold {srcOp : Llvm} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {a b amt : ValuePtr} {intType}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw →
      Data.LLVM.Int bw}
    {state : InterpreterState ctx} {newState cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm srcOp)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[a, b, amt])
    (hSemSrc : ∀ (bw : Nat) (x y z : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw y, .int bw z] blockOperands mem
          = some (.ok (#[.int bw (srcFn x y z)], mem, none)))
    (hinterp : interpretOp op state opInBounds = some (newState, cf))
    (hAType : (a.getType! ctx.raw).val = Attribute.integerType intType)
    (hBType : (b.getType! ctx.raw).val = Attribute.integerType intType)
    (hAmtType : (amt.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ xa xb xc, state.variables.getVar? a = some (RuntimeValue.int intType.bitwidth xa) ∧
      state.variables.getVar? b = some (RuntimeValue.int intType.bitwidth xb) ∧
      state.variables.getVar? amt = some (RuntimeValue.int intType.bitwidth xc) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int intType.bitwidth (srcFn xa xb xc)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 3 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hAEq : a = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hBEq : b = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hAmtEq : amt = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  simp only [liftM, monadLift, MonadLift.monadLift] at hinterp
  -- Derive the operands' `i{bw}` values from the successful interpretation and their types.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize0 : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize1 : 1 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize2 : 2 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨aval, haval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize0
  obtain ⟨bval, hbval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 1 hsize1
  obtain ⟨cval, hcval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 2 hsize2
  have haGetVar : state.variables.getVar? a = some aval := by
    rw [hAEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact haval
  have hbGetVar : state.variables.getVar? b = some bval := by
    rw [hBEq, show (op.getOperands! ctx.raw)[1]! = (op.getOperands! ctx.raw)[1] from by grind]
    exact hbval
  have hcGetVar : state.variables.getVar? amt = some cval := by
    rw [hAmtEq, show (op.getOperands! ctx.raw)[2]! = (op.getOperands! ctx.raw)[2] from by grind]
    exact hcval
  have haconf := VariableState.getVar?_conforms haGetVar
  rw [show a.getType! ctx.raw = ⟨.integerType intType, hAType ▸ (a.getType! ctx.raw).2⟩
        from Subtype.ext hAType] at haconf
  obtain ⟨xa, rfl⟩ := RuntimeValue.Conforms.integerType haconf
  have hbconf := VariableState.getVar?_conforms hbGetVar
  rw [show b.getType! ctx.raw = ⟨.integerType intType, hBType ▸ (b.getType! ctx.raw).2⟩
        from Subtype.ext hBType] at hbconf
  obtain ⟨xb, rfl⟩ := RuntimeValue.Conforms.integerType hbconf
  have hcconf := VariableState.getVar?_conforms hcGetVar
  rw [show amt.getType! ctx.raw = ⟨.integerType intType, hAmtType ▸ (amt.getType! ctx.raw).2⟩
        from Subtype.ext hAmtType] at hcconf
  obtain ⟨xc, rfl⟩ := RuntimeValue.Conforms.integerType hcconf
  refine ⟨xa, xb, xc, haGetVar, hbGetVar, hcGetVar, ?_⟩
  -- With the values in hand, unfold the interpretation of the matched op.
  have hOperand0 : op.getOperand! ctx.raw 0 = a := by
    rw [hAEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = b := by
    rw [hBEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = amt := by
    rw [hAmtEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.int intType.bitwidth xa, RuntimeValue.int intType.bitwidth xb,
          RuntimeValue.int intType.bitwidth xc] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simpa [hOperand0] using haGetVar
    · simpa [hOperand1] using hbGetVar
    · simpa [hOperand2] using hcGetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp'] at hInterp'
  rw [hSemSrc] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ : resValues = #[RuntimeValue.int intType.bitwidth (srcFn xa xb xc)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for every `lowerRotateLocal` lowering: the round trip
    `int × int → reg × reg → op64/op32 → int` refines `srcFn a a c` (the rotate).

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier facts
    (`hVerified`), the interpreter computation facts for the source op and the two riscv ops
    (`hSemSrc`/`hSemR64`/`hSemR32`, discharged by `simp`/`rfl` at concrete opcodes), and the two
    data-level refinement lemmas (`hRefine64`/`hRefine32`). -/
theorem lowerRotateLocal_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × ValuePtr)}
    {op64 op32 : Riscv}
    {props64 : propertiesOf (.riscv op64)} {props32 : propertiesOf (.riscv op32)}
    {f64 f32 : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw →
      Data.LLVM.Int bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {a b amt},
        match? op ctx = some (a, b, amt) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[a, b, amt])
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedIntegerTernop ctx)
    (hSemSrc : ∀ (bw : Nat) (x y z : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw y, .int bw z] blockOperands mem
          = some (.ok (#[.int bw (srcFn x y z)], mem, none)))
    (hSemR64 : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op64)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op64 props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f64 r₁ r₂)], mem, none)))
    (hSemR32 : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op32)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op32 props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f32 r₁ r₂)], mem, none)))
    (hRefine64 : ∀ (x c xt ct : Data.LLVM.Int 64),
        x ⊒ xt → c ⊒ ct →
        srcFn x x c ⊒ RISCV.Reg.toInt (f64 (LLVM.Int.toReg xt) (LLVM.Int.toReg ct)) 64)
    (hRefine32 : ∀ (x c xt ct : Data.LLVM.Int 32),
        x ⊒ xt → c ⊒ ct →
        srcFn x x c ⊒ RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt) (LLVM.Int.toReg ct)) 32)
    {h : LocalRewritePattern.ReturnOps (lowerRotateLocal match? op64 op32 props64 props32)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (lowerRotateLocal match? op64 op32 props64 props32)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (lowerRotateLocal match? op64 op32 props64 props32)}
    {h₄ : LocalRewritePattern.ReturnValues (lowerRotateLocal match? op64 op32 props64 props32)} :
    LocalRewritePattern.PreservesSemantics
      (lowerRotateLocal match? op64 op32 props64 props32) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lowerRotateLocal]
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
  obtain ⟨⟨a, b, amt⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hAEq : a = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hBEq : b = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hAmtEq : amt = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type, hOp2Type⟩ :=
    hVerified opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = a := by
    rw [hAEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = b := by
    rw [hBEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = amt := by
    rw [hAmtEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- All operand types and the result type are the integer type `intType`.
  have hAType : (a.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hBType : (b.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hAmtType : (amt.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, hOp2Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  -- The `a = b` guard: the `simp` above flipped `if a ≠ b then none` to `if a = b then _ else none`.
  -- Derive `a = b` in a side proof (leaving `hpattern` untouched so dependent hypotheses like
  -- `state'Wf` are not reverted), then resolve the guard with `if_pos`.
  have hAeqB : a = b := by
    rcases Decidable.em (a = b) with h | hne
    · exact h
    · rw [if_neg hne] at hpattern; simp at hpattern
  rw [if_pos hAeqB] at hpattern
  -- Resolve the result-type-destructuring match on `intType`.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand values and their `srcFn`.
  obtain ⟨xa, xb, xc, haVal, hbVal, hcVal, hMem, hRes, hCf⟩ :=
    matchTernaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hSemSrc
      hinterp hAType hBType hAmtType
  subst hCf
  -- The value operand `a` and the amount operand `amt` share their value with `b`: since `a = b`,
  -- `xa = xb`, so the source result `srcFn xa xb xc` is `srcFn xa xa xc`.
  have hxab : xa = xb := by
    have := haVal; rw [hAeqB] at this; rw [hbVal] at this; grind
  subst hxab
  -- The matched operands `a`, `amt` dominate the rewrite point in the source context.
  have hDomCtxA : a.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxC : amt.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  peelSplittableCondition [hBw] hpattern
  -- Source value: `op`'s single result is `srcFn` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `a`/`amt` are not among `op`'s results.
  have aNotOp : ¬ a ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have cNotOp : ¬ amt ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the two `castToRegLocal` creations (value operand, then amount operand).
  peelCastToRegLocal₂ hpattern ctx₁ lcastOp hLCast hDomCtxA hDomA₁ hDomCtxC hDomC₁
  peelCastToRegLocal₂ hpattern ctx₂ rcastOp hRCast hDomA₁ hDomA₂ hDomC₁ hDomC₂
  -- Freshness facts, used to keep earlier values alive across later interpretation steps.
  have hLCastFresh : ¬ lcastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds lcastOp hLCast
  have hCIn : amt.InBounds ctx.raw := by clear hpattern; grind
  have hCNeLCastRes : ∀ i, amt ≠ ValuePtr.opResult (lcastOp.getResult i) := by
    intro i heq
    rw [heq] at hCIn
    rw [ValuePtr.inBounds_opResult] at hCIn
    obtain ⟨hIn, -⟩ := hCIn
    exact hLCastFresh hIn
  have hLCastNeRCast : lcastOp ≠ rcastOp := by clear hpattern; grind
  have hBwCases : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  rcases hBwCases with hbw | hbw
  · -- 64-bit case: lowered to `op64`
    rw [if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    simp only [] at hpattern
    peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomA₂ hDomA₃ hDomC₂ hDomC₃
    peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomA₃ hDomA₄ hDomC₃ hDomC₄
    cleanupHpattern hpattern
    -- Read the refined values `xt`/`ct` of `a`/`amt` in the target state `state'`.
    obtain ⟨xt, hLVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) haVal
        hDomCtxA hDomA₄ aNotOp
    obtain ⟨ct, hRVal', hctRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hcVal
        hDomCtxC hDomC₄ cNotOp
    -- Normalise the bitwidth to the literal `64`.
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Pairwise distinctness of the four created ops, built as inline terms so no `op.InBounds`
    -- hypothesis is left in context (those break the surrounding `grind`s by non-monotonicity). With
    -- these `≠` facts available, the transport `grind`s below close by e-matching without wandering
    -- into the frozen (unpeeled) copy of the source pattern.
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLCast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRCast hOpIn₁
    have hLCastIn₂ : lcastOp.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRCast
        (WfRewriter.createOp_new_inBounds lcastOp hLCast)
    have hLCastIn₃ : lcastOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRet hLCastIn₂
    have hRCastIn₂ : rcastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds rcastOp hRCast
    have hRCastIn₃ : rcastOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hRet hRCastIn₂
    have hRetIn₃ : retOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds retOp hRet
    have hOpNeLCast : op ≠ lcastOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds lcastOp hLCast (heq ▸ opInBounds)
    have hOpNeRCast : op ≠ rcastOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds rcastOp hRCast (heq ▸ hOpIn₁)
    have hOpNeRet : op ≠ retOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds retOp hRet (heq ▸ hOpIn₂)
    have hLCastNeRet : lcastOp ≠ retOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds retOp hRet (heq ▸ hLCastIn₂)
    have hLCastNeCB : lcastOp ≠ castBackOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds castBackOp hCastBack (heq ▸ hLCastIn₃)
    have hRCastNeRet : rcastOp ≠ retOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds retOp hRet (heq ▸ hRCastIn₂)
    have hRCastNeCB : rcastOp ≠ castBackOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds castBackOp hCastBack (heq ▸ hRCastIn₃)
    have hRetNeCB : retOp ≠ castBackOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds castBackOp hCastBack (heq ▸ hRetIn₃)
    clear hOpIn₁ hOpIn₂ hLCastIn₂ hLCastIn₃ hRCastIn₂ hRCastIn₃ hRetIn₃
    -- Structural facts about the four created ops.
    have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hRetType : retOp.getOpType! ctx₄.raw = .riscv op64 := by grind
    have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hLCastOperands : lcastOp.getOperands! ctx₄.raw = #[a] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastOperands : rcastOp.getOperands! ctx₄.raw = #[amt] := by
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
    -- In-bounds witnesses for the four created ops in the final context `ctx₄`, built inline (the
    -- `grind` chaining of `createOp_new_inBounds`/`inBounds_mono` is unreliable this deep).
    have hLCastIn₄ : lcastOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hCastBack
        (WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRet
          (WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRCast
            (WfRewriter.createOp_new_inBounds lcastOp hLCast)))
    have hRCastIn₄ : rcastOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hCastBack
        (WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hRet
          (WfRewriter.createOp_new_inBounds rcastOp hRCast))
    have hRetIn₄ : retOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation retOp) hCastBack
        (WfRewriter.createOp_new_inBounds retOp hRet)
    have hCastBackIn₄ : castBackOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_new_inBounds castBackOp hCastBack
    -- Interpretation tail: `interpretOpList [lcastOp, rcastOp, retOp, castBackOp]` in `state'`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := hLCastIn₄)
        hLCastType hLCastOperands hLCastResTypes hLVal'
    have hCNotLCastRes : amt ∉ lcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw amt lcastOp
        with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (hCNeLCastRes i)
    have hRVal₁ : s₁.variables.getVar? amt = some (RuntimeValue.int 64 ct) := by
      rw [hFrame₁ amt hCNotLCastRes]; exact hRVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := hRCastIn₄)
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
      interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := hRetIn₄)
        (f := f64) (hSemR64 _ _) hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := hCastBackIn₄)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.int 64
          (RISCV.Reg.toInt (f64 (LLVM.Int.toReg xt) (LLVM.Int.toReg ct)) 64)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine64 xa xc xt ct hxtRef hctRef⟩
  · -- 32-bit case: lowered to `op32`
    rw [if_pos hbw] at hpattern
    simp only [] at hpattern
    peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomA₂ hDomA₃ hDomC₂ hDomC₃
    peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomA₃ hDomA₄ hDomC₃ hDomC₄
    cleanupHpattern hpattern
    obtain ⟨xt, hLVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) haVal
        hDomCtxA hDomA₄ aNotOp
    obtain ⟨ct, hRVal', hctRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hcVal
        hDomCtxC hDomC₄ cNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Pairwise distinctness of the four created ops (and of `op` from each), as inline terms; see the
    -- 64-bit branch for the rationale.
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLCast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRCast hOpIn₁
    have hLCastIn₂ : lcastOp.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRCast
        (WfRewriter.createOp_new_inBounds lcastOp hLCast)
    have hLCastIn₃ : lcastOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRet hLCastIn₂
    have hRCastIn₂ : rcastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds rcastOp hRCast
    have hRCastIn₃ : rcastOp.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hRet hRCastIn₂
    have hRetIn₃ : retOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds retOp hRet
    have hOpNeLCast : op ≠ lcastOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds lcastOp hLCast (heq ▸ opInBounds)
    have hOpNeRCast : op ≠ rcastOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds rcastOp hRCast (heq ▸ hOpIn₁)
    have hOpNeRet : op ≠ retOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds retOp hRet (heq ▸ hOpIn₂)
    have hLCastNeRet : lcastOp ≠ retOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds retOp hRet (heq ▸ hLCastIn₂)
    have hLCastNeCB : lcastOp ≠ castBackOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds castBackOp hCastBack (heq ▸ hLCastIn₃)
    have hRCastNeRet : rcastOp ≠ retOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds retOp hRet (heq ▸ hRCastIn₂)
    have hRCastNeCB : rcastOp ≠ castBackOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds castBackOp hCastBack (heq ▸ hRCastIn₃)
    have hRetNeCB : retOp ≠ castBackOp := fun heq =>
      WfRewriter.createOp_new_not_inBounds castBackOp hCastBack (heq ▸ hRetIn₃)
    clear hOpIn₁ hOpIn₂ hLCastIn₂ hLCastIn₃ hRCastIn₂ hRCastIn₃ hRetIn₃
    have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hRetType : retOp.getOpType! ctx₄.raw = .riscv op32 := by grind
    have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hLCastOperands : lcastOp.getOperands! ctx₄.raw = #[a] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastOperands : rcastOp.getOperands! ctx₄.raw = #[amt] := by
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
    have hLCastIn₄ : lcastOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hCastBack
        (WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRet
          (WfRewriter.createOp_inBounds_mono (ptr := .operation lcastOp) hRCast
            (WfRewriter.createOp_new_inBounds lcastOp hLCast)))
    have hRCastIn₄ : rcastOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hCastBack
        (WfRewriter.createOp_inBounds_mono (ptr := .operation rcastOp) hRet
          (WfRewriter.createOp_new_inBounds rcastOp hRCast))
    have hRetIn₄ : retOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation retOp) hCastBack
        (WfRewriter.createOp_new_inBounds retOp hRet)
    have hCastBackIn₄ : castBackOp.InBounds ctx₄.raw :=
      WfRewriter.createOp_new_inBounds castBackOp hCastBack
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := hLCastIn₄)
        hLCastType hLCastOperands hLCastResTypes hLVal'
    have hCNotLCastRes : amt ∉ lcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw amt lcastOp
        with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (hCNeLCastRes i)
    have hRVal₁ : s₁.variables.getVar? amt = some (RuntimeValue.int 32 ct) := by
      rw [hFrame₁ amt hCNotLCastRes]; exact hRVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := hRCastIn₄)
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
      interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := hRetIn₄)
        (f := f32) (hSemR32 _ _) hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := hCastBackIn₄)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.int 32
          (RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt) (LLVM.Int.toReg ct)) 32)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine32 xa xc xt ct hxtRef hctRef⟩

/-!
## RISC-V lowering of `llvm.intr.fshl`/`fshr` (rotate)

`llvm.intr.fshl`/`fshr` with identical data operands is a rotate; on 64- or 32-bit integers it is
lowered to two `unrealized_conversion_cast`s (value + amount to registers) → `riscv.rol`/`rolw`
(`ror`/`rorw` for `fshr`) → `unrealized_conversion_cast` (back to the integer type). The structural
part of the proof is shared (`lowerRotateLocal_preservesSemantics`); only the two data-level
refinement lemmas per op are rotate-specific. As with the other binary lowerings, the interpreter
applies the data-level op as `RISCV.op op2 op1`, so the lemmas take `(toReg ct)` (the amount) first.
-/

/-- Correctness of the `riscv.rol` lowering of a 64-bit rotate-left (`fshl x x c`). -/
theorem fshl_isRefinedBy_toInt_rol {x c xt ct : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : c ⊒ ct) :
    Data.LLVM.Int.fshl x x c
      ⊒ RISCV.Reg.toInt (Data.RISCV.rol (LLVM.Int.toReg ct) (LLVM.Int.toReg xt)) 64 := by
  revert h₁ h₂
  veir_bv_decide

/-- Correctness of the `riscv.rolw` lowering of a 32-bit rotate-left (`fshl x x c`). -/
theorem fshl_isRefinedBy_toInt_rolw {x c xt ct : Data.LLVM.Int 32}
    (h₁ : x ⊒ xt) (h₂ : c ⊒ ct) :
    Data.LLVM.Int.fshl x x c
      ⊒ RISCV.Reg.toInt (Data.RISCV.rolw (LLVM.Int.toReg ct) (LLVM.Int.toReg xt)) 32 := by
  revert h₁ h₂
  veir_bv_decide

theorem fshl_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics fshl_local h h₂ h₃ h₄ :=
  lowerRotateLocal_preservesSemantics
    (srcOp := .intr__fshl)
    (srcFn := fun x y z => Data.LLVM.Int.fshl x y z)
    (f64 := fun r₁ r₂ => Data.RISCV.rol r₂ r₁)
    (f32 := fun r₁ r₂ => Data.RISCV.rolw r₂ r₁)
    matchFshl_implies
    OperationPtr.Verified.llvm_intr__fshl
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ h₁ h₂ => fshl_isRefinedBy_toInt_rol h₁ h₂)
    (fun _ _ _ _ h₁ h₂ => fshl_isRefinedBy_toInt_rolw h₁ h₂)

/-- Correctness of the `riscv.ror` lowering of a 64-bit rotate-right (`fshr x x c`). -/
theorem fshr_isRefinedBy_toInt_ror {x c xt ct : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : c ⊒ ct) :
    Data.LLVM.Int.fshr x x c
      ⊒ RISCV.Reg.toInt (Data.RISCV.ror (LLVM.Int.toReg ct) (LLVM.Int.toReg xt)) 64 := by
  revert h₁ h₂
  veir_bv_decide

/-- Correctness of the `riscv.rorw` lowering of a 32-bit rotate-right (`fshr x x c`). -/
theorem fshr_isRefinedBy_toInt_rorw {x c xt ct : Data.LLVM.Int 32}
    (h₁ : x ⊒ xt) (h₂ : c ⊒ ct) :
    Data.LLVM.Int.fshr x x c
      ⊒ RISCV.Reg.toInt (Data.RISCV.rorw (LLVM.Int.toReg ct) (LLVM.Int.toReg xt)) 32 := by
  revert h₁ h₂
  veir_bv_decide

theorem fshr_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics fshr_local h h₂ h₃ h₄ :=
  lowerRotateLocal_preservesSemantics
    (srcOp := .intr__fshr)
    (srcFn := fun x y z => Data.LLVM.Int.fshr x y z)
    (f64 := fun r₁ r₂ => Data.RISCV.ror r₂ r₁)
    (f32 := fun r₁ r₂ => Data.RISCV.rorw r₂ r₁)
    matchFshr_implies
    OperationPtr.Verified.llvm_intr__fshr
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ h₁ h₂ => fshr_isRefinedBy_toInt_ror h₁ h₂)
    (fun _ _ _ _ h₁ h₂ => fshr_isRefinedBy_toInt_rorw h₁ h₂)

end Veir
