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
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm
import Veir.Passes.InstructionSelection.RewriteProofs.LowerTrunc

namespace Veir

/-!
## Correctness of `lshr_local`

`llvm.lshr` on an `i64`/`i32` integer *or* a `byte64`/`byte32` value lowers to two
`unrealized_conversion_cast`s (the value and the shift amount to registers) → a logical-shift-right
riscv op → `unrealized_conversion_cast` (back to the source type). The riscv op depends on the width:
`riscv.srl` for a 64-bit value, `riscv.srlw` for a 32-bit value (word logical shift, sign-extending
the 32-bit result). Unlike `ashr_local`, the lowering goes through the byte-aware
`lowerByteBinaryWLocal` combinator, so the operand may be integer- *or* byte-typed; the proof runs
the two kinds symmetrically (as in `trunc_local`).

The shift amount (operand 1) is always an integer whose width the verifier does *not* pin to the
value's width; the equality is recovered dynamically from a successful interpretation (as in
`selectBinopImmLocal_shift`).

The four data-level refinement lemmas below are the arithmetic core; they close by `veir_bv_decide`:
the register op masks the shift amount to the low 5/6 bits while `llvm.lshr` is poison for a shift
`≥ w`, exactly the range where the register op's masked amount would diverge.
-/

/-- Correctness of the `riscv.srl` lowering of a 64-bit integer `llvm.lshr`. -/
theorem lshr_isRefinedBy_toInt_srl {x y xt yt : Data.LLVM.Int 64} (exact : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.lshr x y exact
      ⊒ RISCV.Reg.toInt (Data.RISCV.srl (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  revert h₁ h₂
  veir_bv_decide

/-- Correctness of the `riscv.srlw` lowering of a 32-bit integer `llvm.lshr`. -/
theorem lshr_isRefinedBy_toInt_srlw {x y xt yt : Data.LLVM.Int 32} (exact : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.lshr x y exact
      ⊒ RISCV.Reg.toInt (Data.RISCV.srlw (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32 := by
  revert h₁ h₂
  veir_bv_decide

/-- Correctness of the `riscv.srl` lowering of a 64-bit byte `llvm.lshr`. -/
theorem lshr_isRefinedBy_toByte_srl {x xt : Data.LLVM.Byte 64} {y yt : Data.LLVM.Int 64}
    (exact : Bool) (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Byte.lshr x y exact
      ⊒ RISCV.Reg.toByte (Data.RISCV.srl (LLVM.Int.toReg yt) (LLVM.Byte.toReg xt)) 64 := by
  revert h₁ h₂
  simp only [RISCV.Reg.toByte, LLVM.Byte.toReg]
  veir_bv_decide

/-- Correctness of the `riscv.srlw` lowering of a 32-bit byte `llvm.lshr`. -/
theorem lshr_isRefinedBy_toByte_srlw {x xt : Data.LLVM.Byte 32} {y yt : Data.LLVM.Int 32}
    (exact : Bool) (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Byte.lshr x y exact
      ⊒ RISCV.Reg.toByte (Data.RISCV.srlw (LLVM.Int.toReg yt) (LLVM.Byte.toReg xt)) 32 := by
  revert h₁ h₂
  simp only [RISCV.Reg.toByte, LLVM.Byte.toReg]
  veir_bv_decide

/-- Byte analogue of `matchShiftOp_interpretOp_unfold`: for `llvm.shl`/`llvm.lshr` whose *value*
    operand (operand 0) is `byte`-typed. As in the integer case, the verifier does not pin the shift
    amount's width statically, so a *successful* interpretation forces the two widths equal; the
    `hSemSrc` hypothesis captures the interpreter's own width guard. -/
theorem matchByteShiftOp_interpretOp_unfold {srcOp : Llvm} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {lhs rhs : ValuePtr} {props : propertiesOf (.llvm srcOp)}
    {byteType : LLVM.ByteType} {intType2}
    {shiftFn : ∀ {bw : Nat},
      Data.LLVM.Byte bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) → Data.LLVM.Byte bw}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm srcOp)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[lhs, rhs])
    (hProps : props = op.getProperties! ctx.raw (.llvm srcOp))
    (hSemSrc : ∀ (bw bw' : Nat) (x : Data.LLVM.Byte bw) (y : Data.LLVM.Int bw')
        (props : propertiesOf (.llvm srcOp)) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Llvm.interpretOp' srcOp props resultTypes #[.byte bw x, .int bw' y] blockOperands mem
          = some (.ok res) →
        ∃ (h' : bw' = bw), res = (#[.byte bw (shiftFn x (h' ▸ y) props)], mem, none))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf)))
    (hLhsType : (lhs.getType! ctx.raw).val = Attribute.byteType byteType)
    (hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType2) :
    ∃ (x : Data.LLVM.Byte byteType.bitwidth) (y : Data.LLVM.Int intType2.bitwidth)
      (h' : intType2.bitwidth = byteType.bitwidth),
      state.variables.getVar? lhs = some (RuntimeValue.byte byteType.bitwidth x) ∧
      state.variables.getVar? rhs = some (RuntimeValue.int intType2.bitwidth y) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.byte byteType.bitwidth (shiftFn x (h' ▸ y) props)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 2 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
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
  rw [show lhs.getType! ctx.raw = ⟨.byteType byteType, hLhsType ▸ (lhs.getType! ctx.raw).2⟩
        from Subtype.ext hLhsType] at hlconf
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.byteType hlconf
  have hrconf := VariableState.getVar?_conforms hrGetVar
  rw [show rhs.getType! ctx.raw = ⟨.integerType intType2, hRhsType ▸ (rhs.getType! ctx.raw).2⟩
        from Subtype.ext hRhsType] at hrconf
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType hrconf
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.byte byteType.bitwidth x, RuntimeValue.int intType2.bitwidth y] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    match i, hi with
    | 0, _ => simpa [hOperand0] using hlGetVar
    | 1, _ => simpa [hOperand1] using hrGetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [← hProps, interpretOp'] at hInterp'
  obtain ⟨h', hres⟩ := hSemSrc _ _ _ _ _ _ _ _ _ hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.byte byteType.bitwidth (shiftFn x (h' ▸ y) props)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨x, y, h', hlGetVar, hrGetVar, rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-- Interpreter computation fact for the *integer* `llvm.lshr` arm (the `hSemSrc` argument of
    `matchShiftOp_interpretOp_unfold`): a successful interpretation forces the two operand widths
    equal and produces `Int.lshr`. -/
theorem lshr_int_shiftSem (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
    (props : propertiesOf (.llvm .lshr)) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (h : Llvm.interpretOp' .lshr props resultTypes #[.int bw x, .int bw' y] blockOperands mem
      = some (.ok res)) :
    ∃ (h' : bw' = bw),
      res = (#[.int bw (Data.LLVM.Int.lshr x (h' ▸ y) props.exact)], mem, none) := by
  simp only [Llvm.interpretOp'] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hbw
    obtain rfl : bw' = bw := by omega
    refine ⟨rfl, ?_⟩
    simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at h
    grind

/-- Interpreter computation fact for the *byte* `llvm.lshr` arm (the `hSemSrc` argument of
    `matchByteShiftOp_interpretOp_unfold`). -/
theorem lshr_byte_shiftSem (bw bw' : Nat) (x : Data.LLVM.Byte bw) (y : Data.LLVM.Int bw')
    (props : propertiesOf (.llvm .lshr)) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (h : Llvm.interpretOp' .lshr props resultTypes #[.byte bw x, .int bw' y] blockOperands mem
      = some (.ok res)) :
    ∃ (h' : bw' = bw),
      res = (#[.byte bw (Data.LLVM.Byte.lshr x (h' ▸ y) props.exact)], mem, none) := by
  simp only [Llvm.interpretOp'] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hbw
    obtain rfl : bw' = bw := by omega
    refine ⟨rfl, ?_⟩
    simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at h
    grind

set_option maxHeartbeats 4000000 in
theorem lshr_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps lshr_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges lshr_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds lshr_local}
    {h₄ : LocalRewritePattern.ReturnValues lshr_local} :
    LocalRewritePattern.PreservesSemantics lshr_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lshr_local, lowerByteBinaryWLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchLshr op ctx.raw).isSome := by
    cases hM : matchLshr op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchLshr_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hResEqOp0, intType2, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_lshr opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType2 := by
    rw [← hOperand1, hOp1Type]
  have hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Read the value operand's runtime value to determine int vs byte.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize0 : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!,
      ← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]; simp
  obtain ⟨val0, hval0⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize0
  have hlGetVar : state.variables.getVar? lhs = some val0 := by
    rw [hLhsEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hval0
  match val0 with
  | .int opBw x0 =>
    have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType ⟨opBw⟩ :=
      conforms_int_type (VariableState.getVar?_conforms hlGetVar)
    have hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨opBw⟩ := by
      rw [hResEqOp0, hOperand0, hLhsType]
    -- Unfold the source interpretation.
    obtain ⟨x, y, h', hlVal, hrVal, hMem, hRes, hCf⟩ :=
      matchShiftOp_interpretOp_unfold (srcOp := .lshr)
        (shiftFn := fun x y props => Data.LLVM.Int.lshr x y props.exact)
        opInBounds hOpType hNumResults hOperands hProps
        (fun _ _ x y props rt bo mem res hh => lshr_int_shiftSem _ _ x y props rt bo mem res hh)
        hinterp hLhsType hRhsType
    obtain ⟨bw2⟩ := intType2
    simp only at h' hrVal hRes ⊢
    subst bw2
    subst hCf
    rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
      at hsourceValues
    simp at hsourceValues
    simp [hRes] at hsourceValues
    subst sourceValues
    -- Resolve the lowering's type/width guard.
    simp only [getIntByteTypeBitwidth, hLhsType] at hpattern
    peelSplittableCondition [hBw] hpattern
    -- Peel the two `castToRegLocal` creations.
    peelCastToRegLocal₂ hpattern ctx₁ lcastOp hLCast hDomCtxL hDomL₁ hDomCtxR hDomR₁
    peelCastToRegLocal₂ hpattern ctx₂ rcastOp hRCast hDomL₁ hDomL₂ hDomR₁ hDomR₂
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
    have hBwCases : opBw = 64 ∨ opBw = 32 := by omega
    rcases hBwCases with hbw | hbw
    · -- i64: srl
      rw [if_neg (show ¬opBw = 32 by omega)] at hpattern
      simp only [] at hpattern
      peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
      peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
      cleanupHpattern hpattern
      obtain ⟨xt, hLVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hlVal
          hDomCtxL hDomL₄ lNotOp
      obtain ⟨yt, hRVal', hytRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hrVal
          hDomCtxR hDomR₄ rNotOp
      subst hbw
      have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
      have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := rcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
      have hRetType : retOp.getOpType! ctx₄.raw = .riscv .srl := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := retOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := retOp)]
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
          = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
        have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
            = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
          grind [ValuePtr.getType!_WfRewriter_createOp hRet
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hRCast
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hLCast
              (value := ValuePtr.opResult (op.getResult 0))]
        simp only [ValuePtr.getType!_opResult] at h1
        apply Subtype.ext
        rw [h1]; exact hResType
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
      obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
        interpretOp_castToReg_forward (state := state') (inBounds := by grind)
          hLCastType hLCastOperands hLCastResTypes hLVal'
      have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₄.raw := by
        rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw rhs lcastOp
          with hres | ⟨i, hi, heq⟩
        · exact hres
        · exact absurd heq (hRhsNeLCastRes i)
      have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 64 yt) := by
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
          (f := fun r₁ r₂ => Data.RISCV.srl r₂ r₁) (fun _ _ _ _ => rfl)
          hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
        interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₃
      refine ⟨s₄, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
      · refine ⟨#[RuntimeValue.int 64
            (RISCV.Reg.toInt (Data.RISCV.srl (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64)], ?_, ?_⟩
        · simp [hRes₄, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            ⟨rfl, by simpa using lshr_isRefinedBy_toInt_srl props.exact hxtRef hytRef⟩
    · -- i32: srlw
      rw [if_pos hbw] at hpattern
      simp only [] at hpattern
      peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
      peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
      cleanupHpattern hpattern
      obtain ⟨xt, hLVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hlVal
          hDomCtxL hDomL₄ lNotOp
      obtain ⟨yt, hRVal', hytRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hrVal
          hDomCtxR hDomR₄ rNotOp
      subst hbw
      have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
      have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := rcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
      have hRetType : retOp.getOpType! ctx₄.raw = .riscv .srlw := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := retOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := retOp)]
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
          = (⟨Attribute.integerType { bitwidth := 32 }, by grind⟩ : TypeAttr) := by
        have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
            = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
          grind [ValuePtr.getType!_WfRewriter_createOp hRet
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hRCast
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hLCast
              (value := ValuePtr.opResult (op.getResult 0))]
        simp only [ValuePtr.getType!_opResult] at h1
        apply Subtype.ext
        rw [h1]; exact hResType
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
          (f := fun r₁ r₂ => Data.RISCV.srlw r₂ r₁) (fun _ _ _ _ => rfl)
          hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
        interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₃
      refine ⟨s₄, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
      · refine ⟨#[RuntimeValue.int 32
            (RISCV.Reg.toInt (Data.RISCV.srlw (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32)], ?_, ?_⟩
        · simp [hRes₄, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            ⟨rfl, by simpa using lshr_isRefinedBy_toInt_srlw props.exact hxtRef hytRef⟩
  | .byte opBw x0 =>
    have hLhsType : (lhs.getType! ctx.raw).val = Attribute.byteType ⟨opBw⟩ :=
      conforms_byte_type (VariableState.getVar?_conforms hlGetVar)
    have hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.byteType ⟨opBw⟩ := by
      rw [hResEqOp0, hOperand0, hLhsType]
    -- Unfold the source interpretation.
    obtain ⟨x, y, h', hlVal, hrVal, hMem, hRes, hCf⟩ :=
      matchByteShiftOp_interpretOp_unfold (srcOp := .lshr)
        (shiftFn := fun x y props => Data.LLVM.Byte.lshr x y props.exact)
        opInBounds hOpType hNumResults hOperands hProps
        (fun _ _ x y props rt bo mem res hh => lshr_byte_shiftSem _ _ x y props rt bo mem res hh)
        hinterp hLhsType hRhsType
    obtain ⟨bw2⟩ := intType2
    simp only at h' hrVal hRes ⊢
    subst bw2
    subst hCf
    rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
      at hsourceValues
    simp at hsourceValues
    simp [hRes] at hsourceValues
    subst sourceValues
    -- Resolve the lowering's type/width guard.
    simp only [getIntByteTypeBitwidth, hLhsType] at hpattern
    peelSplittableCondition [hBw] hpattern
    -- Peel the two `castToRegLocal` creations.
    peelCastToRegLocal₂ hpattern ctx₁ lcastOp hLCast hDomCtxL hDomL₁ hDomCtxR hDomR₁
    peelCastToRegLocal₂ hpattern ctx₂ rcastOp hRCast hDomL₁ hDomL₂ hDomR₁ hDomR₂
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
    have hBwCases : opBw = 64 ∨ opBw = 32 := by omega
    rcases hBwCases with hbw | hbw
    · -- byte64: srl
      rw [if_neg (show ¬opBw = 32 by omega)] at hpattern
      simp only [] at hpattern
      peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
      peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
      cleanupHpattern hpattern
      obtain ⟨xt, hLVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_byte_getVar? valueRefinement state'Dom (by grind) hlVal
          hDomCtxL hDomL₄ lNotOp
      obtain ⟨yt, hRVal', hytRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hrVal
          hDomCtxR hDomR₄ rNotOp
      subst hbw
      have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
      have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := rcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
      have hRetType : retOp.getOpType! ctx₄.raw = .riscv .srl := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := retOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := retOp)]
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
          = (⟨Attribute.byteType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
        have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
            = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
          grind [ValuePtr.getType!_WfRewriter_createOp hRet
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hRCast
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hLCast
              (value := ValuePtr.opResult (op.getResult 0))]
        simp only [ValuePtr.getType!_opResult] at h1
        apply Subtype.ext
        rw [h1]; exact hResType
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
          = #[⟨Attribute.byteType { bitwidth := 64 }, by grind⟩] := by grind
      obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
        interpretOp_castToReg_byte_forward (state := state') (inBounds := by grind)
          hLCastType hLCastOperands hLCastResTypes hLVal'
      have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₄.raw := by
        rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw rhs lcastOp
          with hres | ⟨i, hi, heq⟩
        · exact hres
        · exact absurd heq (hRhsNeLCastRes i)
      have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 64 yt) := by
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
          = some (RuntimeValue.reg (LLVM.Byte.toReg xt)) := by
        rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
      obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
        interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
          (f := fun r₁ r₂ => Data.RISCV.srl r₂ r₁) (fun _ _ _ _ => rfl)
          hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
        interpretOp_castBack_byte_forward (state := s₃) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₃
      refine ⟨s₄, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
      · refine ⟨#[RuntimeValue.byte 64
            (RISCV.Reg.toByte (Data.RISCV.srl (LLVM.Int.toReg yt) (LLVM.Byte.toReg xt)) 64)], ?_, ?_⟩
        · simp [hRes₄, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            ⟨rfl, by simpa using lshr_isRefinedBy_toByte_srl props.exact hxtRef hytRef⟩
    · -- byte32: srlw
      rw [if_pos hbw] at hpattern
      simp only [] at hpattern
      peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
      peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
      cleanupHpattern hpattern
      obtain ⟨xt, hLVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_byte_getVar? valueRefinement state'Dom (by grind) hlVal
          hDomCtxL hDomL₄ lNotOp
      obtain ⟨yt, hRVal', hytRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hrVal
          hDomCtxR hDomR₄ rNotOp
      subst hbw
      have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := lcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
      have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := rcastOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
      have hRetType : retOp.getOpType! ctx₄.raw = .riscv .srlw := by
        grind [OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := retOp),
          OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := retOp)]
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
          = (⟨Attribute.byteType { bitwidth := 32 }, by grind⟩ : TypeAttr) := by
        have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
            = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
          grind [ValuePtr.getType!_WfRewriter_createOp hRet
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hRCast
              (value := ValuePtr.opResult (op.getResult 0)),
            ValuePtr.getType!_WfRewriter_createOp hLCast
              (value := ValuePtr.opResult (op.getResult 0))]
        simp only [ValuePtr.getType!_opResult] at h1
        apply Subtype.ext
        rw [h1]; exact hResType
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
          = #[⟨Attribute.byteType { bitwidth := 32 }, by grind⟩] := by grind
      obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
        interpretOp_castToReg_byte_forward (state := state') (inBounds := by grind)
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
          = some (RuntimeValue.reg (LLVM.Byte.toReg xt)) := by
        rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
      obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
        interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
          (f := fun r₁ r₂ => Data.RISCV.srlw r₂ r₁) (fun _ _ _ _ => rfl)
          hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
        interpretOp_castBack_byte_forward (state := s₃) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₃
      refine ⟨s₄, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
      · refine ⟨#[RuntimeValue.byte 32
            (RISCV.Reg.toByte (Data.RISCV.srlw (LLVM.Int.toReg yt) (LLVM.Byte.toReg xt)) 32)], ?_, ?_⟩
        · simp [hRes₄, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            ⟨rfl, by simpa using lshr_isRefinedBy_toByte_srlw props.exact hxtRef hytRef⟩
  | .float _ _ | .addr _ | .reg _ =>
    exfalso
    have hconf := VariableState.getVar?_conforms hlGetVar
    have hnone : getIntByteTypeBitwidth (lhs.getType! ctx.raw) = none := by
      unfold getIntByteTypeBitwidth
      rcases htv : (lhs.getType! ctx.raw) with ⟨tv, hIsTy⟩
      rw [htv] at hconf
      cases tv <;> first | rfl | (exact absurd hconf (by simp [RuntimeValue.Conforms]))
    rw [hnone] at hpattern
    simp at hpattern

/--
info: 'Veir.lshr_local_preservesSemantics' depends on axioms: [propext,
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
 lshr_isRefinedBy_toByte_srl._native.bv_decide.ax_1_5,
 lshr_isRefinedBy_toByte_srlw._native.bv_decide.ax_1_5,
 lshr_isRefinedBy_toInt_srl._native.bv_decide.ax_1_5,
 lshr_isRefinedBy_toInt_srlw._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms lshr_local_preservesSemantics

end Veir
