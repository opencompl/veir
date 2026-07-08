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
## Generic correctness of `lowerBinaryRegLocal`

`lowerBinaryRegLocal match? rop props` lowers a two-operand LLVM integer op whose result has type
`i64` or `i32` to `unrealized_conversion_cast` (each operand to a register) → a *single* `riscv` op
`rop` (the same instruction at both bitwidths) → `unrealized_conversion_cast` (back to the source
type). It is the width-agnostic cousin of `lowerBinaryWLocal`: no `W` variant is emitted because the
register already holds the correctly-represented value (as for the `Zbb` `maxu`/`minu`). Its
`PreservesSemantics` proof is shared: instantiating it for a concrete lowering (`umax`, `umin`) only
requires the matcher facts, the interpreter computation facts, and the two data-level refinement
lemmas.

Because the emitted op is the same instruction for both bitwidths, the structural part of the
proof is done *once* (no bitwidth branch); the widths only differ at the very end, where the
matching `hRefine64`/`hRefine32` lemma is selected.
-/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for every `lowerBinaryRegLocal` lowering: the round trip
    `int × int → reg × reg → rop → int` refines `srcFn`.

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier facts
    (`hVerified`), the interpreter computation facts for the source op and the riscv op
    (`hSemSrc`/`hSemR`, discharged by `simp`/`rfl` at concrete opcodes), and the two data-level
    refinement lemmas (`hRefine64`/`hRefine32`). -/
theorem lowerBinaryRegLocal_preservesSemantics {srcOp : Llvm}
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
        srcFn x y props ⊒ RISCV.Reg.toInt (f (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 32)
    {h : LocalRewritePattern.ReturnOps (lowerBinaryRegLocal match? rop props)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (lowerBinaryRegLocal match? rop props)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (lowerBinaryRegLocal match? rop props)}
    {h₄ : LocalRewritePattern.ReturnValues (lowerBinaryRegLocal match? rop props)} :
    LocalRewritePattern.PreservesSemantics
      (lowerBinaryRegLocal match? rop props) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lowerBinaryRegLocal]
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
  -- Peel the two `castToRegLocal` creations, transporting both operand dominance facts through.
  peelCastToRegLocal₂ hpattern ctx₁ lcastOp hLCast hDomCtxL hDomL₁ hDomCtxR hDomR₁
  peelCastToRegLocal₂ hpattern ctx₂ rcastOp hRCast hDomL₁ hDomL₂ hDomR₁ hDomR₂
  -- Freshness facts, used to keep earlier values alive across later interpretation steps.
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
  -- Peel the single `rop` creation and the `replaceWithRegLocal` cast-back. Because `rop` is the
  -- same instruction at both bitwidths, there is no bitwidth branch here.
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
  -- Structural facts about the four created ops (bitwidth left generic).
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
  -- The cast-back op's result type is the integer type `intType`.
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
  -- Interpretation tail: execute `interpretOpList [lcastOp, rcastOp, retOp, castBackOp]` in
  -- `state'`. The frame clauses carry earlier bindings across later steps.
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
  · -- The list interpretation is the chain of the four op interpretations.
    simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
      Interp]
  · refine ⟨#[RuntimeValue.int intType.bitwidth
        (RISCV.Reg.toInt (f (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) intType.bitwidth)], ?_, ?_⟩
    · simp [hRes₄, Option.bind, Option.map]
    · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
      -- Only here do the two bitwidths diverge: pick the matching refinement lemma.
      rcases (show intType.bitwidth = 64 ∨ intType.bitwidth = 32 by omega) with hbw | hbw
      · obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
        simpa using hRefine64 xVal yVal xt yt _ hxtRef hytRef
      · obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
        simpa using hRefine32 xVal yVal xt yt _ hxtRef hytRef

/-!
## RISC-V lowering of `llvm.intr.umax` and `llvm.intr.umin`

`llvm.intr.umax`/`umin` on 64- or 32-bit integers is lowered to two `unrealized_conversion_cast`s
(operands to registers) → `riscv.maxu`/`riscv.minu` → `unrealized_conversion_cast` (back to the
integer type). These are the actual `Veir.umax_local`/`Veir.umin_local` patterns.

The structural part of the proof is shared with `lowerBinaryRegLocal_preservesSemantics`; only the
two data-level refinement lemmas per op are `umax`/`umin`-specific. As with the other binary
lowerings, the interpreter applies the data-level op as `RISCV.op op2 op1`, so the lemmas take
`(toReg yt)` first.
-/

/-- Correctness of the `riscv.maxu` lowering of a 64-bit `llvm.intr.umax`. -/
theorem umax_isRefinedBy_toInt_maxu {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.umax x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.maxu (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_umax] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_umax] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.maxu]
  veir_bv_decide

/-- Correctness of the `riscv.maxu` lowering of a 32-bit `llvm.intr.umax`. -/
theorem umax_isRefinedBy_toInt_maxu_32 {x y xt yt : Data.LLVM.Int 32}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.umax x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.maxu (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_umax] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_umax] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.maxu]
  veir_bv_decide

theorem umax_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics umax_local h h₂ h₃ h₄ :=
  lowerBinaryRegLocal_preservesSemantics
    (srcOp := .intr__umax)
    (srcFn := fun x y _ => Data.LLVM.Int.umax x y)
    (f := fun r₁ r₂ => Data.RISCV.maxu r₂ r₁)
    matchUmax_implies
    OperationPtr.Verified.llvm_intr__umax
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ h₁ h₂ => umax_isRefinedBy_toInt_maxu h₁ h₂)
    (fun _ _ _ _ _ h₁ h₂ => umax_isRefinedBy_toInt_maxu_32 h₁ h₂)

/-- Correctness of the `riscv.minu` lowering of a 64-bit `llvm.intr.umin`. -/
theorem umin_isRefinedBy_toInt_minu {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.umin x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.minu (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_umin] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_umin] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.minu]
  veir_bv_decide

/-- Correctness of the `riscv.minu` lowering of a 32-bit `llvm.intr.umin`. -/
theorem umin_isRefinedBy_toInt_minu_32 {x y xt yt : Data.LLVM.Int 32}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.umin x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.minu (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_umin] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_umin] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.minu]
  veir_bv_decide

theorem umin_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics umin_local h h₂ h₃ h₄ :=
  lowerBinaryRegLocal_preservesSemantics
    (srcOp := .intr__umin)
    (srcFn := fun x y _ => Data.LLVM.Int.umin x y)
    (f := fun r₁ r₂ => Data.RISCV.minu r₂ r₁)
    matchUmin_implies
    OperationPtr.Verified.llvm_intr__umin
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ h₁ h₂ => umin_isRefinedBy_toInt_minu h₁ h₂)
    (fun _ _ _ _ _ h₁ h₂ => umin_isRefinedBy_toInt_minu_32 h₁ h₂)

end Veir
