import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBinaryW

namespace Veir

/-!
## Generic correctness of `lowerBitwiseRegLocal`

`lowerBitwiseRegLocal match? rop props` lowers a two-operand LLVM *bitwise* integer op whose result
has type `i64`, `i32`, `i8`, or `i1` to `unrealized_conversion_cast` (each operand to a register) →
a *single* bitwise `riscv` op `rop` → `unrealized_conversion_cast` (back to the source type). It is
the bitwise cousin of `lowerBinaryRegLocal`.

The distinguishing feature is that `rop` is correct at *every* legal bitwidth with *no* per-width
variant, because a bitwise op is bit-parallel: bit `i` of the result depends only on bit `i` of the
operands, so `zeroExtend`ing the operands to 64 bits, `and`/`or`ing, and truncating back to `bw`
bits yields exactly the `bw`-bit result — for *any* `bw ≤ 64`. Consequently the value-refinement
obligation is *width-generic*: a single `hRefine` hypothesis discharges all four widths at once
(it takes the disjunction `bw ∈ {64, 32, 8, 1}` and closes each case with `bv_decide`). This is why
arithmetic ops do *not* fit: for `add`/`sub`/`mul`/shifts a carry or shifted bit crosses the width
boundary, so the `i32` result is not a function of the low 32 bits and a sign-extending `W` variant
is required (`lowerBinaryWLocal`).

As in `lowerBinaryRegLocal`, the emitted op is the same instruction for every bitwidth, so the
structural part of the proof is done *once* (no bitwidth branch).
-/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for every `lowerBitwiseRegLocal` lowering: the round trip
    `int × int → reg × reg → rop → int` refines `srcFn`.

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier facts
    (`hVerified`), the interpreter computation facts for the source op and the riscv op
    (`hSemSrc`/`hSemR`, discharged by `simp`/`rfl` at concrete opcodes), and the single
    width-generic data-level refinement lemma (`hRefine`). -/
theorem lowerBitwiseRegLocal_preservesSemantics {P : Type} {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × P)}
    {rop : Riscv} {props : propertiesOf (.riscv rop)}
    {f : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs p},
        match? op ctx = some (lhs, rhs, p) →
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
    (hRefine : ∀ (bw : Nat) (x y xt yt : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp)),
        (bw = 64 ∨ bw = 32 ∨ bw = 8 ∨ bw = 1) → x ⊒ xt → y ⊒ yt →
        srcFn x y props ⊒ RISCV.Reg.toInt (f (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) bw)
    {h : LocalRewritePattern.ReturnOps (lowerBitwiseRegLocal match? rop props)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (lowerBitwiseRegLocal match? rop props)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (lowerBitwiseRegLocal match? rop props)}
    {h₄ : LocalRewritePattern.ReturnValues (lowerBitwiseRegLocal match? rop props)} :
    LocalRewritePattern.PreservesSemantics
      (lowerBitwiseRegLocal match? rop props) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lowerBitwiseRegLocal]
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
  obtain ⟨⟨lhs, rhs, p⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
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
    matchBinaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands rfl
      (fun bw x y props rt bo mem res h => by
        rw [hSemSrc bw x y props rt bo mem] at h
        injection h with h; injection h with h; exact h.symm)
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
      -- One width-generic refinement lemma covers all four legal widths at once.
      simpa using hRefine intType.bitwidth xVal yVal xt yt _ (by omega) hxtRef hytRef

/-!
## RISC-V lowering of `llvm.and` and `llvm.or`

`llvm.and`/`llvm.or` on `i64`/`i32`/`i8`/`i1` integers is lowered to two `unrealized_conversion_cast`s
(operands to registers) → `riscv.and`/`riscv.or` → `unrealized_conversion_cast` (back to the integer
type). These are the actual `Veir.and_local`/`Veir.or_local` patterns.

The structural part of the proof is shared with `lowerBitwiseRegLocal_preservesSemantics`; only the
single width-generic data-level refinement lemma per op is `and`/`or`-specific. As with the other
binary lowerings, the interpreter applies the data-level op as `RISCV.op op2 op1`, so the lemmas
take `(toReg yt)` first.
-/

/-- Correctness of the `riscv.and` lowering of `llvm.and`, for every legal width `bw ∈ {64,32,8,1}`.
    Bitwise `and` commutes with truncation, so a single lemma (one `bv_decide` per width) suffices. -/
theorem and_isRefinedBy_toInt_and {bw : Nat}
    (hbw : bw = 64 ∨ bw = 32 ∨ bw = 8 ∨ bw = 1) {x y xt yt : Data.LLVM.Int bw}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.and x y
      ⊒ RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) bw := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_and] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_and] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.and]
  rcases hbw with h | h | h | h <;> subst h <;> veir_bv_decide

theorem and_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics and_local h h₂ h₃ h₄ :=
  lowerBitwiseRegLocal_preservesSemantics
    (srcOp := .and)
    (srcFn := fun x y _ => Data.LLVM.Int.and x y)
    (f := fun r₁ r₂ => Data.RISCV.and r₂ r₁)
    (fun hMatch => have h := matchAnd_implies hMatch; ⟨h.1, h.2.1, h.2.2.1⟩)
    OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ hbw h₁ h₂ => and_isRefinedBy_toInt_and hbw h₁ h₂)

/-- Correctness of the `riscv.or` lowering of `llvm.or`, for every legal width `bw ∈ {64,32,8,1}` and
    any `disjoint` flag. When `disjoint` holds but the operands overlap the source is poison, which
    refines any target; otherwise the value is the ordinary `|||`, which commutes with truncation. -/
theorem or_isRefinedBy_toInt_or {bw : Nat}
    (hbw : bw = 64 ∨ bw = 32 ∨ bw = 8 ∨ bw = 1) (disjoint : Bool) {x y xt yt : Data.LLVM.Int bw}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.or x y disjoint
      ⊒ RISCV.Reg.toInt (Data.RISCV.or (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) bw := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_or] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_or] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.or]
  rcases hbw with h | h | h | h <;> subst h <;> veir_bv_decide

theorem or_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics or_local h h₂ h₃ h₄ :=
  lowerBitwiseRegLocal_preservesSemantics
    (srcOp := .or)
    (srcFn := fun x y props => Data.LLVM.Int.or x y props.disjoint)
    (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁)
    (fun hMatch => have h := matchOr_implies hMatch; ⟨h.1, h.2.1, h.2.2.1⟩)
    OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ props hbw h₁ h₂ => or_isRefinedBy_toInt_or hbw props.disjoint h₁ h₂)

end Veir
