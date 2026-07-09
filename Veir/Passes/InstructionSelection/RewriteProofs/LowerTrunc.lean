import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.LLVM.Byte.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.Casting
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.LowerConst
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret

namespace Veir

/-!
## Correctness of `trunc_local`

`llvm.trunc` narrows an `i{opBw}` / `byte{opBw}` value to a strictly smaller width (both widths in
`{8, 16, 32, 64}`), lowering to `unrealized_conversion_cast` (operand → register) →
`unrealized_conversion_cast` (register → the narrower result type). Truncation is free on the
register side: the operand is held zero-extended in the 64-bit register, so casting the register back
to the narrower type reads its low bits.

The two data-level refinement lemmas below (integer and byte) close by `veir_bv_decide` after
`fin_cases` fixes the concrete operand/result widths and the refinement hypothesis is reverted into
the goal.
-/

/-- Correctness of the integer `llvm.trunc` round trip: `i{opBw} → reg → i{resBw}` refines
    `Int.trunc`, for widths in `{8, 16, 32, 64}`. -/
theorem trunc_isRefinedBy_toInt {opBw resBw : Nat}
    (hop : opBw ∈ [8, 16, 32, 64]) (hres : resBw ∈ [8, 16, 32, 64]) (hlt : opBw > resBw)
    (nsw nuw : Bool) {x xt : Data.LLVM.Int opBw} (h : x ⊒ xt) :
    Data.LLVM.Int.trunc x resBw nsw nuw hlt ⊒ RISCV.Reg.toInt (LLVM.Int.toReg xt) resBw := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop hres
  rcases hop with rfl | rfl | rfl | rfl <;> rcases hres with rfl | rfl | rfl | rfl <;>
    first | omega | (revert h; veir_bv_decide)

/-- Correctness of the byte `llvm.trunc` round trip: `byte{opBw} → reg → byte{resBw}` refines
    `Byte.trunc`, for widths in `{8, 16, 32, 64}`. -/
theorem trunc_isRefinedBy_toByte {opBw resBw : Nat}
    (hop : opBw ∈ [8, 16, 32, 64]) (hres : resBw ∈ [8, 16, 32, 64])
    {x xt : Data.LLVM.Byte opBw} (h : x ⊒ xt) :
    Data.LLVM.Byte.trunc x resBw ⊒ RISCV.Reg.toByte (LLVM.Byte.toReg xt) resBw := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop hres
  rcases hop with rfl | rfl | rfl | rfl <;> rcases hres with rfl | rfl | rfl | rfl <;>
    (revert h; simp only [RISCV.Reg.toByte, LLVM.Byte.toReg]; veir_bv_decide)

set_option maxHeartbeats 1000000 in
theorem trunc_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps trunc_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges trunc_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds trunc_local}
    {h₄ : LocalRewritePattern.ReturnValues trunc_local} :
    LocalRewritePattern.PreservesSemantics trunc_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, trunc_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchTrunc op ctx.raw).isSome := by
    cases hM : matchTrunc op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operand, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchTrunc_implies hMatch
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hNumOperands : op.getNumOperands! ctx.raw = 1 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  -- The op's single result type, as read by the interpreter.
  have hResTypes : op.getResultTypes! ctx.raw
      = #[((op.getResult 0).get! ctx.raw).type] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctx.raw) (index := 0)
        (by omega)
      grind
  -- Read the operand value from the interpretation.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨val, hval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize
  have hgetVar : state.variables.getVar? operand = some val := by
    rw [hOperandEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hval
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op = some #[val] := by
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
  simp only [interpretOp', Llvm.interpretOp', hResTypes] at hInterp'
  -- `operand` dominates and is not a result of `op`.
  have hDomCtx : operand.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have vNotOp : ¬ operand ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Case on the operand runtime value: integer or byte (other kinds make the interpreter `none`).
  match val with
  | .int opBw x =>
    -- The operand's declared type is `i{opBw}`.
    have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType ⟨opBw⟩ :=
      conforms_int_type (VariableState.getVar?_conforms hgetVar)
    -- Reduce the interpreter's array index and the integer-value match.
    rw [show (#[((op.getResult 0).get! ctx.raw).type] : Array TypeAttr)[0]?
        = some ((op.getResult 0).get! ctx.raw).type from rfl] at hInterp'
    simp only [] at hInterp'
    -- The result type must be an integer type; case on it.
    split at hInterp'
    case _ resInt hResInt =>
      -- The width guard: `resInt.bitwidth < opBw`.
      split at hInterp'
      · exact absurd hInterp' (by simp)
      rename_i hle
      obtain ⟨rfl, rfl, rfl⟩ :
          resValues = #[RuntimeValue.int resInt.bitwidth
            (Data.LLVM.Int.trunc x resInt.bitwidth props.nsw props.nuw (by omega))] ∧
          mem' = state.memory ∧ cf = none := by
        simp only [pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hInterp'; grind
      -- Source value: `op`'s result is `Int.trunc`.
      have hResVal : newState.variables.getVar? (op.getResult 0)
          = some (RuntimeValue.int resInt.bitwidth
            (Data.LLVM.Int.trunc x resInt.bitwidth props.nsw props.nuw (by omega))) := by
        rw [hNew]
        rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
        simp
      rw [show op.getResults ctx.raw (by grind)
          = #[ValuePtr.opResult (op.getResult 0)] from by grind] at hsourceValues
      simp [hResVal] at hsourceValues
      subst sourceValues
      -- Resolve the lowering's type/width guards.
      simp only [getIntByteTypeBitwidth, hOperandType, hResInt] at hpattern
      split at hpattern
      · exact absurd hpattern (by simp)
      rename_i hBwGuard
      split at hpattern
      · exact absurd hpattern (by simp)
      rename_i hMem
      -- Peel the two casts (raw `createOp!`).
      peelOpCreation! hpattern ctx₁ opCastOp hCast hDomCtx hDom₁
      peelOpCreation! hpattern ctx₂ castBackOp hCastBack hDom₁ hDom₂
      cleanupHpattern hpattern
      obtain ⟨xt, hOpVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hgetVar
          hDomCtx hDom₂ vNotOp
      -- Structural facts.
      have hCastType : opCastOp.getOpType! ctx₂.raw = .builtin .unrealized_conversion_cast := by grind
      have hCastBackType : castBackOp.getOpType! ctx₂.raw = .builtin .unrealized_conversion_cast := by
        grind
      have hCastOperands : opCastOp.getOperands! ctx₂.raw = #[operand] := by grind
      have hCastBackOperands :
          castBackOp.getOperands! ctx₂.raw = #[ValuePtr.opResult (opCastOp.getResult 0)] := by grind
      have hCastResTypes : opCastOp.getResultTypes! ctx₂.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := opCastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := opCastOp)]
      have hResTypeAttr : ((op.getResult 0).get! ctx.raw).type = ⟨Attribute.integerType resInt, by grind⟩ :=
        by apply Subtype.ext; exact hResInt
      have hCastBackResTypes : castBackOp.getResultTypes! ctx₂.raw
          = #[⟨Attribute.integerType resInt, by grind⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
      -- Interpretation tail: `castToReg → castBack`.
      obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
        interpretOp_castToReg_forward (state := state') (inBounds := by grind)
          hCastType hCastOperands hCastResTypes hOpVal'
      obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
        interpretOp_castBack_forward (state := s₁) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₁
      have hmemOp : opBw ∈ [8, 16, 32, 64] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem ⊢; grind
      have hmemRes : resInt.bitwidth ∈ [8, 16, 32, 64] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem ⊢; grind
      have hrefine := trunc_isRefinedBy_toInt hmemOp hmemRes (by omega) props.nsw props.nuw hxtRef
      refine ⟨s₂, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
      · refine ⟨#[RuntimeValue.int resInt.bitwidth
            (RISCV.Reg.toInt (LLVM.Int.toReg xt) resInt.bitwidth)], ?_, ?_⟩
        · simp [hRes₂, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, by simpa using hrefine⟩
    all_goals simp at hInterp'
  | .byte opBw x =>
    -- The operand's declared type is a `byte` of width `opBw`.
    have hOperandType : (operand.getType! ctx.raw).val = Attribute.byteType ⟨opBw⟩ :=
      conforms_byte_type (VariableState.getVar?_conforms hgetVar)
    -- Reduce the interpreter's array index and the byte-value match.
    rw [show (#[((op.getResult 0).get! ctx.raw).type] : Array TypeAttr)[0]?
        = some ((op.getResult 0).get! ctx.raw).type from rfl] at hInterp'
    simp only [] at hInterp'
    -- The result type must be a byte type; case on it.
    split at hInterp'
    case _ resByte hResByte =>
      -- The width guard: `resByte.bitwidth < opBw`.
      split at hInterp'
      · exact absurd hInterp' (by simp)
      rename_i hle
      obtain ⟨rfl, rfl, rfl⟩ :
          resValues = #[RuntimeValue.byte resByte.bitwidth
            (Data.LLVM.Byte.trunc x resByte.bitwidth)] ∧
          mem' = state.memory ∧ cf = none := by
        simp only [pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hInterp'; grind
      -- Source value: `op`'s result is `Byte.trunc`.
      have hResVal : newState.variables.getVar? (op.getResult 0)
          = some (RuntimeValue.byte resByte.bitwidth
            (Data.LLVM.Byte.trunc x resByte.bitwidth)) := by
        rw [hNew]
        rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
        simp
      rw [show op.getResults ctx.raw (by grind)
          = #[ValuePtr.opResult (op.getResult 0)] from by grind] at hsourceValues
      simp [hResVal] at hsourceValues
      subst sourceValues
      -- Resolve the lowering's type/width guards.
      simp only [getIntByteTypeBitwidth, hOperandType, hResByte] at hpattern
      split at hpattern
      · exact absurd hpattern (by simp)
      rename_i hBwGuard
      split at hpattern
      · exact absurd hpattern (by simp)
      rename_i hMem
      -- Peel the two casts (raw `createOp!`).
      peelOpCreation! hpattern ctx₁ opCastOp hCast hDomCtx hDom₁
      peelOpCreation! hpattern ctx₂ castBackOp hCastBack hDom₁ hDom₂
      cleanupHpattern hpattern
      obtain ⟨xt, hOpVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_byte_getVar? valueRefinement state'Dom (by grind) hgetVar
          hDomCtx hDom₂ vNotOp
      -- Structural facts.
      have hCastType : opCastOp.getOpType! ctx₂.raw = .builtin .unrealized_conversion_cast := by grind
      have hCastBackType : castBackOp.getOpType! ctx₂.raw = .builtin .unrealized_conversion_cast := by
        grind
      have hCastOperands : opCastOp.getOperands! ctx₂.raw = #[operand] := by grind
      have hCastBackOperands :
          castBackOp.getOperands! ctx₂.raw = #[ValuePtr.opResult (opCastOp.getResult 0)] := by grind
      have hCastResTypes : opCastOp.getResultTypes! ctx₂.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := opCastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := opCastOp)]
      have hResTypeAttr : ((op.getResult 0).get! ctx.raw).type = ⟨Attribute.byteType resByte, by grind⟩ :=
        by apply Subtype.ext; exact hResByte
      have hCastBackResTypes : castBackOp.getResultTypes! ctx₂.raw
          = #[⟨Attribute.byteType resByte, by grind⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
      -- Interpretation tail: `castToReg → castBack`.
      obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
        interpretOp_castToReg_byte_forward (state := state') (inBounds := by grind)
          hCastType hCastOperands hCastResTypes hOpVal'
      obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
        interpretOp_castBack_byte_forward (state := s₁) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₁
      have hmemOp : opBw ∈ [8, 16, 32, 64] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem ⊢; grind
      have hmemRes : resByte.bitwidth ∈ [8, 16, 32, 64] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem ⊢; grind
      have hrefine := trunc_isRefinedBy_toByte hmemOp hmemRes hxtRef
      refine ⟨s₂, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
      · refine ⟨#[RuntimeValue.byte resByte.bitwidth
            (RISCV.Reg.toByte (LLVM.Byte.toReg xt) resByte.bitwidth)], ?_, ?_⟩
        · simp [hRes₂, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, by simpa using hrefine⟩
    all_goals simp at hInterp'
  | .float _ _ | .addr _ | .reg _ => simp at hInterp'

/--
info: 'Veir.trunc_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominates_refl,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_14,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_19,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_24,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_29,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_34,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_39,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_44,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_49,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_54,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_59,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_64,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_69,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_74,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_79,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_84,
 trunc_isRefinedBy_toByte._native.bv_decide.ax_1_9,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms trunc_local_preservesSemantics

end Veir
