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
## Generic correctness of `lowerByteBinaryWLocal`

`lowerByteBinaryWLocal match? op64 op32` lowers the two-operand LLVM shifts (`llvm.shl`,
`llvm.lshr`) to `unrealized_conversion_cast` (each operand to a register) → `riscv` op (`op64`, or
its `W` variant `op32` when the shifted value is 32 bits wide) → `unrealized_conversion_cast` (back
to the source type).

It differs from `lowerBinaryWLocal` in two ways, both stemming from `llvm.shl`/`llvm.lshr` being
verified by `verifyLLVMShift` rather than `verifyIntegerBinop`:

* the shifted operand (operand 0) may have *integer* **or** *byte* type — hence the two symmetric
  branches below, and the two families of data-level refinement lemmas;
* the shift amount (operand 1) is only known to be *some* integer; that its width agrees with
  operand 0's is a *dynamic* fact, recovered from the successful source interpretation by
  `matchShiftOp_interpretOp_unfold` (integer case) and `matchShiftOp_byteLhs_interpretOp_unfold`
  (byte case), then `subst`ed.

The RISC-V shift ops mask the shift amount to its low 5/6 bits while LLVM's shifts are poison for
shift amounts `≥ w`, so the data-level refinement lemmas are trivial exactly on the branch where
the source is poison.
-/

/-- The byte-operand analogue of `matchShiftOp_interpretOp_unfold`: unfold the interpretation of a
    shift whose shifted operand (operand 0) has *byte* type and whose shift amount (operand 1) has
    integer type. As in the integer case, the equality of the two operand widths is read out of the
    successful interpretation via `hSemSrc` rather than assumed. -/
theorem matchShiftOp_byteLhs_interpretOp_unfold {srcOp : Llvm} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {lhs rhs : ValuePtr} {props : propertiesOf (.llvm srcOp)}
    {byteTy : LLVM.ByteType} {intType2 : IntegerType}
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
    (hLhsType : (lhs.getType! ctx.raw).val = Attribute.byteType byteTy)
    (hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType2) :
    ∃ (x : Data.LLVM.Byte byteTy.bitwidth) (y : Data.LLVM.Int intType2.bitwidth)
      (h' : intType2.bitwidth = byteTy.bitwidth),
      state.variables.getVar? lhs = some (RuntimeValue.byte byteTy.bitwidth x) ∧
      state.variables.getVar? rhs = some (RuntimeValue.int intType2.bitwidth y) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.byte byteTy.bitwidth (shiftFn x (h' ▸ y) props)) ∧
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
  rw [show lhs.getType! ctx.raw = ⟨.byteType byteTy, hLhsType ▸ (lhs.getType! ctx.raw).2⟩
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
      = some #[RuntimeValue.byte byteTy.bitwidth x, RuntimeValue.int intType2.bitwidth y] := by
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
      resValues = #[RuntimeValue.byte byteTy.bitwidth (shiftFn x (h' ▸ y) props)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨x, y, h', hlGetVar, hrGetVar, rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

set_option maxHeartbeats 4000000 in
/-- Shared correctness proof for every `lowerByteBinaryWLocal` lowering.

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier fact
    (`hVerified`, yielding the weak `IsVerifiedLLVMShift`), the interpreter computation facts for
    the source op on integer and byte operands (`hSemSrcInt`/`hSemSrcByte`) and for the two riscv
    ops (`hSemR64`/`hSemR32`), and the four data-level refinement lemmas. -/
theorem lowerByteBinaryWLocal_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode →
      Option (ValuePtr × ValuePtr × propertiesOf (.llvm srcOp))}
    {op64 op32 : Riscv}
    {props64 : propertiesOf (.riscv op64)} {props32 : propertiesOf (.riscv op32)}
    {f64 f32 : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcIntFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {srcByteFn : ∀ {bw : Nat}, Data.LLVM.Byte bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Byte bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props},
        match? op ctx = some (lhs, rhs, props) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[lhs, rhs] ∧
        props = op.getProperties! ctx (.llvm srcOp))
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedLLVMShift ctx)
    (hSemSrcInt : ∀ (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
        (props : propertiesOf (.llvm srcOp)) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw' y] blockOperands mem
          = some (.ok res) →
        ∃ (h' : bw' = bw), res = (#[.int bw (srcIntFn x (h' ▸ y) props)], mem, none))
    (hSemSrcByte : ∀ (bw bw' : Nat) (x : Data.LLVM.Byte bw) (y : Data.LLVM.Int bw')
        (props : propertiesOf (.llvm srcOp)) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Llvm.interpretOp' srcOp props resultTypes #[.byte bw x, .int bw' y] blockOperands mem
          = some (.ok res) →
        ∃ (h' : bw' = bw), res = (#[.byte bw (srcByteFn x (h' ▸ y) props)], mem, none))
    (hSemR64 : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op64)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op64 props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f64 r₁ r₂)], mem, none)))
    (hSemR32 : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf op32)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' op32 props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f32 r₁ r₂)], mem, none)))
    (hRefineInt64 : ∀ (x y xt yt : Data.LLVM.Int 64) (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcIntFn x y props ⊒ RISCV.Reg.toInt (f64 (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 64)
    (hRefineInt32 : ∀ (x y xt yt : Data.LLVM.Int 32) (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcIntFn x y props ⊒ RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 32)
    (hRefineByte64 : ∀ (x xt : Data.LLVM.Byte 64) (y yt : Data.LLVM.Int 64)
        (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcByteFn x y props ⊒ RISCV.Reg.toByte (f64 (LLVM.Byte.toReg xt) (LLVM.Int.toReg yt)) 64)
    (hRefineByte32 : ∀ (x xt : Data.LLVM.Byte 32) (y yt : Data.LLVM.Int 32)
        (props : propertiesOf (.llvm srcOp)),
        x ⊒ xt → y ⊒ yt →
        srcByteFn x y props ⊒ RISCV.Reg.toByte (f32 (LLVM.Byte.toReg xt) (LLVM.Int.toReg yt)) 32)
    {h : LocalRewritePattern.ReturnOps (lowerByteBinaryWLocal match? op64 op32 props64 props32)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges
      (lowerByteBinaryWLocal match? op64 op32 props64 props32)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (lowerByteBinaryWLocal match? op64 op32 props64 props32)}
    {h₄ : LocalRewritePattern.ReturnValues
      (lowerByteBinaryWLocal match? op64 op32 props64 props32)} :
    LocalRewritePattern.PreservesSemantics
      (lowerByteBinaryWLocal match? op64 op32 props64 props32) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, lowerByteBinaryWLocal]
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
  -- Syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := hMatchImplies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨hNRes, hNOper, hResEqOp0, intType2, hOp1Type⟩ := hVerified opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The shift amount is *some* integer; its width is not yet pinned to `lhs`'s.
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType2 := by
    rw [← hOperand1, hOp1Type]
  -- The lowering only fires when `lhs` has integer or byte type; extract its width `bw`.
  obtain ⟨bw, hbwEq⟩ : ∃ bw, getIntByteTypeBitwidth (lhs.getType! ctx.raw) = some bw := by
    cases hg : getIntByteTypeBitwidth (lhs.getType! ctx.raw) with
    | some b => exact ⟨b, rfl⟩
    | none => rw [hg] at hpattern; simp at hpattern
  rw [hbwEq] at hpattern
  simp only [] at hpattern
  -- The width guard must be false: `bw ∈ {64, 32}`.
  peelSplittableCondition [hBw] hpattern
  have hBwCases : bw = 64 ∨ bw = 32 := by omega
  -- The matched operands dominate the rewrite point, and are not `op`'s results.
  have hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- `lhs`'s declared type is either `i{bw}` or `byte{bw}`.
  have hLhsTypeCases : (lhs.getType! ctx.raw).val = Attribute.integerType ⟨bw⟩ ∨
      (lhs.getType! ctx.raw).val = Attribute.byteType ⟨bw⟩ := by
    unfold getIntByteTypeBitwidth at hbwEq
    split at hbwEq
    · rename_i it hit; left; grind
    · rename_i bt hbt; right; grind
    · simp at hbwEq
  rcases hLhsTypeCases with hLhsType | hLhsType
  · -- Integer-typed shifted operand.
    have hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨bw⟩ := by
      rw [hResEqOp0, hOperand0, hLhsType]
    obtain ⟨xVal, yVal, hWEq, hxVal, hyVal, hMem, hRes, hCf⟩ :=
      matchShiftOp_interpretOp_unfold (shiftFn := srcIntFn) opInBounds hOpType hNumResults hOperands
        hProps hSemSrcInt hinterp hLhsType hRhsType
    subst hCf
    -- The shift amount's width equals `bw`: normalise it away.
    obtain ⟨w2⟩ := intType2
    simp only at hWEq hyVal hRhsType
    subst hWEq
    rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
      at hsourceValues
    simp at hsourceValues
    simp [hRes] at hsourceValues
    subst sourceValues
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
    rcases hBwCases with hbw | hbw
    · -- `i64`, lowered to `op64`.
      rw [if_neg (show ¬w2 = 32 by omega)] at hpattern
      simp only [] at hpattern
      peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
      peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
      cleanupHpattern hpattern
      obtain ⟨xt, hLVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
          hDomCtxL hDomL₄ lNotOp
      obtain ⟨yt, hRVal', hytRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
          hDomCtxR hDomR₄ rNotOp
      subst hbw
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
        rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
        rw [h1]; exact Subtype.ext hResType
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
          (f := f64) (hSemR64 _ _) hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
        interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₃
      refine ⟨s₄, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
          Interp]
      · refine ⟨#[RuntimeValue.int 64
            (RISCV.Reg.toInt (f64 (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 64)], ?_, ?_⟩
        · simp [hRes₄, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            ⟨rfl, by simpa using hRefineInt64 xVal yVal xt yt props hxtRef hytRef⟩
    · -- `i32`, lowered to `op32`.
      rw [if_pos hbw] at hpattern
      simp only [] at hpattern
      peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
      peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
      cleanupHpattern hpattern
      obtain ⟨xt, hLVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
          hDomCtxL hDomL₄ lNotOp
      obtain ⟨yt, hRVal', hytRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
          hDomCtxR hDomR₄ rNotOp
      subst hbw
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
        rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
        rw [h1]; exact Subtype.ext hResType
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
          (f := f32) (hSemR32 _ _) hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
        interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₃
      refine ⟨s₄, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
          Interp]
      · refine ⟨#[RuntimeValue.int 32
            (RISCV.Reg.toInt (f32 (LLVM.Int.toReg xt) (LLVM.Int.toReg yt)) 32)], ?_, ?_⟩
        · simp [hRes₄, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            ⟨rfl, by simpa using hRefineInt32 xVal yVal xt yt props hxtRef hytRef⟩
  · -- Byte-typed shifted operand: same chain, but the outer casts go through `Byte.toReg` /
    -- `Reg.toByte`, and the cast-back's result type is a `byteType`.
    have hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.byteType ⟨bw⟩ := by
      rw [hResEqOp0, hOperand0, hLhsType]
    obtain ⟨xVal, yVal, hWEq, hxVal, hyVal, hMem, hRes, hCf⟩ :=
      matchShiftOp_byteLhs_interpretOp_unfold (shiftFn := srcByteFn) opInBounds hOpType hNumResults
        hOperands hProps hSemSrcByte hinterp hLhsType hRhsType
    subst hCf
    obtain ⟨w2⟩ := intType2
    simp only at hWEq hyVal hRhsType
    subst hWEq
    rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
      at hsourceValues
    simp at hsourceValues
    simp [hRes] at hsourceValues
    subst sourceValues
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
    rcases hBwCases with hbw | hbw
    · -- `byte 64`, lowered to `op64`.
      rw [if_neg (show ¬w2 = 32 by omega)] at hpattern
      simp only [] at hpattern
      peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
      peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
      cleanupHpattern hpattern
      obtain ⟨xt, hLVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_byte_getVar? valueRefinement state'Dom (by grind) hxVal
          hDomCtxL hDomL₄ lNotOp
      obtain ⟨yt, hRVal', hytRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
          hDomCtxR hDomR₄ rNotOp
      subst hbw
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
        rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
        rw [h1]; exact Subtype.ext hResType
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
          = #[⟨Attribute.byteType { bitwidth := 64 }, by grind⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack
          (operation := castBackOp)]
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
          (f := f64) (hSemR64 _ _) hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
        interpretOp_castBack_byte_forward (state := s₃) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₃
      refine ⟨s₄, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
          Interp]
      · refine ⟨#[RuntimeValue.byte 64
            (RISCV.Reg.toByte (f64 (LLVM.Byte.toReg xt) (LLVM.Int.toReg yt)) 64)], ?_, ?_⟩
        · simp [hRes₄, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            ⟨rfl, by simpa using hRefineByte64 xVal xt yVal yt props hxtRef hytRef⟩
    · -- `byte 32`, lowered to `op32`.
      rw [if_pos hbw] at hpattern
      simp only [] at hpattern
      peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
      peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
      cleanupHpattern hpattern
      obtain ⟨xt, hLVal', hxtRef⟩ :=
        LocalRewritePattern.exists_refined_byte_getVar? valueRefinement state'Dom (by grind) hxVal
          hDomCtxL hDomL₄ lNotOp
      obtain ⟨yt, hRVal', hytRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
          hDomCtxR hDomR₄ rNotOp
      subst hbw
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
        rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
        rw [h1]; exact Subtype.ext hResType
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
          = #[⟨Attribute.byteType { bitwidth := 32 }, by grind⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack
          (operation := castBackOp)]
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
          (f := f32) (hSemR32 _ _) hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
        interpretOp_castBack_byte_forward (state := s₃) (inBounds := by grind)
          hCastBackType hCastBackOperands hCastBackResTypes hRes₃
      refine ⟨s₄, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
          Interp]
      · refine ⟨#[RuntimeValue.byte 32
            (RISCV.Reg.toByte (f32 (LLVM.Byte.toReg xt) (LLVM.Int.toReg yt)) 32)], ?_, ?_⟩
        · simp [hRes₄, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            ⟨rfl, by simpa using hRefineByte32 xVal xt yVal yt props hxtRef hytRef⟩

/-!
## RISC-V lowering of `llvm.shl`

`llvm.shl` on 64- or 32-bit integers *or bytes* is lowered to `riscv.sll`/`riscv.sllw`. The RISC-V
shift masks the shift amount to its low 6 (resp. 5) bits while `llvm.shl` is poison as soon as the
shift amount reaches the bitwidth, so the two agree exactly on the branch where the source is not
poison. The byte lowering additionally *drops* the operand's per-bit poison mask when the byte is
moved into a register; this is sound because the source's own result mask only ever marks bits the
refinement ignores, and the value bits agree wherever the source is not poison.
-/

/-- The `shl` source-interpretation fact on *integer* operands: a successful interpretation forces
    the two operand widths to agree, and computes `Int.shl`. -/
private theorem shl_shiftSemInt (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
    (props : propertiesOf (.llvm .shl)) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (h : Llvm.interpretOp' .shl props resultTypes #[.int bw x, .int bw' y] blockOperands mem
      = some (.ok res)) :
    ∃ (h' : bw' = bw),
      res = (#[.int bw (Data.LLVM.Int.shl x (h' ▸ y) props.nsw props.nuw)], mem, none) := by
  simp only [Llvm.interpretOp'] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hbw
    obtain rfl : bw' = bw := by omega
    refine ⟨rfl, ?_⟩
    simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at h
    grind

/-- The `shl` source-interpretation fact on *byte* operands. Besides the width guard, the byte arm of
    the interpreter refuses to run when `nsw` is set, which makes the hypothesis vacuous there. -/
private theorem shl_shiftSemByte (bw bw' : Nat) (x : Data.LLVM.Byte bw) (y : Data.LLVM.Int bw')
    (props : propertiesOf (.llvm .shl)) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (h : Llvm.interpretOp' .shl props resultTypes #[.byte bw x, .int bw' y] blockOperands mem
      = some (.ok res)) :
    ∃ (h' : bw' = bw),
      res = (#[.byte bw (Data.LLVM.Byte.shl x (h' ▸ y) props.nuw)], mem, none) := by
  simp only [Llvm.interpretOp'] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hbw
    obtain rfl : bw' = bw := by omega
    split at h
    · exact absurd h (by simp)
    refine ⟨rfl, ?_⟩
    simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at h
    grind

/-- Correctness of the `riscv.sll` lowering of a 64-bit integer `llvm.shl`. -/
theorem shl_isRefinedBy_toInt_sll {x y xt yt : Data.LLVM.Int 64} (nsw nuw : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.shl x y nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  revert h₁ h₂
  veir_bv_decide

/-- Correctness of the `riscv.sllw` lowering of a 32-bit integer `llvm.shl`. -/
theorem shl_isRefinedBy_toInt_sllw {x y xt yt : Data.LLVM.Int 32} (nsw nuw : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.shl x y nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.sllw (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32 := by
  revert h₁ h₂
  veir_bv_decide

/-- Correctness of the `riscv.sll` lowering of a 64-bit byte `llvm.shl`. -/
theorem shl_isRefinedBy_toByte_sll {x xt : Data.LLVM.Byte 64} {y yt : Data.LLVM.Int 64}
    (nuw : Bool) (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Byte.shl x y nuw
      ⊒ RISCV.Reg.toByte (Data.RISCV.sll (LLVM.Int.toReg yt) (LLVM.Byte.toReg xt)) 64 := by
  revert h₁ h₂
  simp only [RISCV.Reg.toByte, LLVM.Byte.toReg]
  veir_bv_decide

/-- Correctness of the `riscv.sllw` lowering of a 32-bit byte `llvm.shl`. -/
theorem shl_isRefinedBy_toByte_sllw {x xt : Data.LLVM.Byte 32} {y yt : Data.LLVM.Int 32}
    (nuw : Bool) (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Byte.shl x y nuw
      ⊒ RISCV.Reg.toByte (Data.RISCV.sllw (LLVM.Int.toReg yt) (LLVM.Byte.toReg xt)) 32 := by
  revert h₁ h₂
  simp only [RISCV.Reg.toByte, LLVM.Byte.toReg]
  veir_bv_decide

theorem shl_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics shl_local h h₂ h₃ h₄ :=
  lowerByteBinaryWLocal_preservesSemantics
    (srcOp := .shl)
    (srcIntFn := fun x y props => Data.LLVM.Int.shl x y props.nsw props.nuw)
    (srcByteFn := fun x y props => Data.LLVM.Byte.shl x y props.nuw)
    (f64 := fun r₁ r₂ => Data.RISCV.sll r₂ r₁)
    (f32 := fun r₁ r₂ => Data.RISCV.sllw r₂ r₁)
    matchShl_implies
    OperationPtr.Verified.llvm_shl
    shl_shiftSemInt
    shl_shiftSemByte
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ props h₁ h₂ => shl_isRefinedBy_toInt_sll props.nsw props.nuw h₁ h₂)
    (fun _ _ _ _ props h₁ h₂ => shl_isRefinedBy_toInt_sllw props.nsw props.nuw h₁ h₂)
    (fun _ _ _ _ props h₁ h₂ => shl_isRefinedBy_toByte_sll props.nuw h₁ h₂)
    (fun _ _ _ _ props h₁ h₂ => shl_isRefinedBy_toByte_sllw props.nuw h₁ h₂)

/-!
## RISC-V lowering of `llvm.lshr`

`llvm.lshr` lowers to `riscv.srl`/`riscv.srlw`. `castToRegLocal` holds the operand *zero*-extended
in the 64-bit register, so the low bits already carry the value and the word variant `srlw` reads
exactly those in the 32-bit case.
-/

/-- The `lshr` source-interpretation fact on *integer* operands. -/
private theorem lshr_shiftSemInt (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
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

/-- The `lshr` source-interpretation fact on *byte* operands. -/
private theorem lshr_shiftSemByte (bw bw' : Nat) (x : Data.LLVM.Byte bw) (y : Data.LLVM.Int bw')
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

theorem lshr_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics lshr_local h h₂ h₃ h₄ :=
  lowerByteBinaryWLocal_preservesSemantics
    (srcOp := .lshr)
    (srcIntFn := fun x y props => Data.LLVM.Int.lshr x y props.exact)
    (srcByteFn := fun x y props => Data.LLVM.Byte.lshr x y props.exact)
    (f64 := fun r₁ r₂ => Data.RISCV.srl r₂ r₁)
    (f32 := fun r₁ r₂ => Data.RISCV.srlw r₂ r₁)
    matchLshr_implies
    OperationPtr.Verified.llvm_lshr
    lshr_shiftSemInt
    lshr_shiftSemByte
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ props h₁ h₂ => lshr_isRefinedBy_toInt_srl props.exact h₁ h₂)
    (fun _ _ _ _ props h₁ h₂ => lshr_isRefinedBy_toInt_srlw props.exact h₁ h₂)
    (fun _ _ _ _ props h₁ h₂ => lshr_isRefinedBy_toByte_srl props.exact h₁ h₂)
    (fun _ _ _ _ props h₁ h₂ => lshr_isRefinedBy_toByte_srlw props.exact h₁ h₂)

/--
info: 'Veir.shl_local_preservesSemantics' depends on axioms: [propext,
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
 shl_isRefinedBy_toByte_sll._native.bv_decide.ax_1_5,
 shl_isRefinedBy_toByte_sllw._native.bv_decide.ax_1_5,
 shl_isRefinedBy_toInt_sll._native.bv_decide.ax_1_5,
 shl_isRefinedBy_toInt_sllw._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms shl_local_preservesSemantics

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
