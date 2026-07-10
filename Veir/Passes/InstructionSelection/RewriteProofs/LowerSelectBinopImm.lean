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
## Generic correctness of `selectBinopImmLocal`

`selectBinopImmLocal matchPair dst h width lo hi` lowers a two-operand LLVM integer op whose
right-hand operand is a constant in `[lo, hi]` (`OP x (const imm)`) to
`unrealized_conversion_cast` (the *left* operand to a register) → an immediate-form `riscv` op
`dst` carrying `imm` → `unrealized_conversion_cast` (back to the integer type). Its
`PreservesSemantics` proof is shared: it fuses the binary-source, match-through-a-defining-op shape
of `lowerBinopNotLocal` with the single-operand immediate-emit chain of `zext_1_local`. The
constant right-hand operand is *folded* into the emitted op's immediate rather than cast, so only
the left operand is cast, and the matched constant's value is pinned with the graph lemma
`matchConstantIntVal_getVar?_of_EquationLemmaAt`.

Instantiating it for a concrete lowering (`addi`, `slli`, …) only requires the matcher facts, the
verifier facts, the interpreter computation facts for the source op and the immediate `riscv` op,
and one data-level refinement lemma.
-/

/-- Shift analogue of `matchBinaryOp_interpretOp_unfold`: for `llvm.shl`/`llvm.lshr`, whose verifier
    (`verifyLLVMShift`) permits the shift amount (operand 1) to have a *different* integer width
    `intType2` from operand 0 (`intType`), a *successful* interpretation forces the two widths equal.
    The `hSemSrc` hypothesis captures the interpreter's own width guard: it takes the mismatched
    operands `#[.int bw x, .int bw' y]` and returns the width-equality proof `h'` together with the
    result value. -/
theorem matchShiftOp_interpretOp_unfold {srcOp : Llvm} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {lhs rhs : ValuePtr} {props : propertiesOf (.llvm srcOp)} {intType intType2}
    {shiftFn : ∀ {bw : Nat},
      Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) → Data.LLVM.Int bw}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm srcOp)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[lhs, rhs])
    (hProps : props = op.getProperties! ctx.raw (.llvm srcOp))
    (hSemSrc : ∀ (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
        (props : propertiesOf (.llvm srcOp)) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw' y] blockOperands mem
          = some (.ok res) →
        ∃ (h' : bw' = bw), res = (#[.int bw (shiftFn x (h' ▸ y) props)], mem, none))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf)))
    (hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType)
    (hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType2) :
    ∃ (x : Data.LLVM.Int intType.bitwidth) (y : Data.LLVM.Int intType2.bitwidth)
      (h' : intType2.bitwidth = intType.bitwidth),
      state.variables.getVar? lhs = some (RuntimeValue.int intType.bitwidth x) ∧
      state.variables.getVar? rhs = some (RuntimeValue.int intType2.bitwidth y) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int intType.bitwidth (shiftFn x (h' ▸ y) props)) ∧
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
  rw [show lhs.getType! ctx.raw = ⟨.integerType intType, hLhsType ▸ (lhs.getType! ctx.raw).2⟩
        from Subtype.ext hLhsType] at hlconf
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType hlconf
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
      = some #[RuntimeValue.int intType.bitwidth x, RuntimeValue.int intType2.bitwidth y] := by
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
      resValues = #[RuntimeValue.int intType.bitwidth (shiftFn x (h' ▸ y) props)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨x, y, h', hlGetVar, hrGetVar, rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for every `selectBinopImmLocal` lowering: the round trip
    `int → reg → dst(imm) → int` refines `srcFn _ (constant imm)`.

    Per-lowering inputs: the matcher's syntactic facts (`hMatchImplies`), the verifier facts
    (`hVerified`), the interpreter computation facts for the source op and the immediate `riscv` op
    (`hSemSrc`/`hSemR`, discharged by `simp`/`rfl` at concrete opcodes), and the data-level
    refinement lemma (`hRefine`). -/
theorem selectBinopImmLocal_preservesSemantics {α : Type} {srcOp : Llvm}
    {matchPair : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × α)}
    {dst : Riscv} {hdst : Riscv.propertiesOf dst = RISCVImmediateProperties}
    {width : Nat} {lo hi : Int}
    {rFn : Int → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs a},
        matchPair op ctx = some (lhs, rhs, a) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[lhs, rhs])
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedIntegerBinop ctx)
    (hSemSrc : ∀ (bw : Nat) (x y : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw y] blockOperands mem
          = some (.ok res) →
        res = (#[.int bw (srcFn x y props)], mem, none))
    (hSemR : ∀ (c : Int) (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' dst
            (cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk c (IntegerType.mk 64))))
            resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (rFn c r)], mem, none)))
    (hRefine : ∀ (x xt : Data.LLVM.Int width) (c : Int) (props : propertiesOf (.llvm srcOp)),
        lo ≤ c → c ≤ hi → x ⊒ xt →
        srcFn x (Data.LLVM.Int.constant width c) props
          ⊒ RISCV.Reg.toInt (rFn c (LLVM.Int.toReg xt)) width)
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchPair dst hdst width lo hi)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectBinopImmLocal matchPair dst hdst width lo hi)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (selectBinopImmLocal matchPair dst hdst width lo hi)}
    {h₄ : LocalRewritePattern.ReturnValues (selectBinopImmLocal matchPair dst hdst width lo hi)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchPair dst hdst width lo hi) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectBinopImmLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchPair op ctx.raw).isSome := by
    cases hM : matchPair op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, a⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
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
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  -- Resolve the result-type destructuring match in the pattern.
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- The width guard fixes `intType.bitwidth = width`.
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hWidth
  -- Pin the matched constant's value.
  have hCstSome : (matchConstantIntVal rhs ctx.raw).isSome := by
    cases hM : matchConstantIntVal rhs ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨imm, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  -- The immediate-range guard.
  split at hpattern
  case isTrue hrange => simp at hpattern
  rename_i hRange
  obtain ⟨hLo, hHi⟩ : lo ≤ imm.value ∧ imm.value ≤ hi := by omega
  -- Unfold the interpretation of the matched op: exposes both operand values and `srcFn`.
  obtain ⟨xlv, xrv, hlVal, hrVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl hSemSrc hinterp hLhsType hRhsType
  subst hCf
  -- The matched left operand dominates the rewrite point in the source context.
  have hDomLhs : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Graph semantics of the matched constant: pins `rhs`'s runtime value to `constant imm`.
  have hrhsVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hRhsType
  obtain rfl : xrv = Data.LLVM.Int.constant intType.bitwidth imm.value := by
    have := hrVal.symm.trans hrhsVal
    simpa using this
  -- Source value: `op`'s single result is `srcFn` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `lhs` is not among `op`'s results.
  have vNotOpLhs : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the three op creations (cast lhs, immediate `dst` op, cast back).
  peelCastToRegLocal hpattern ctx₁ xCastOp hCastX hDomLhs hDomLhs₁
  peelOpCreation! hpattern ctx₂ retOp hRet hDomLhs₁ hDomLhs₂
  peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDomLhs₂ hDomLhs₃
  cleanupHpattern hpattern
  -- Read the refined value `xt` of `lhs` in the target state `state'`.
  obtain ⟨xt, hXVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hlVal
      hDomLhs hDomLhs₃ vNotOpLhs
  -- Normalise the bitwidth to `width`.
  obtain ⟨bw⟩ := intType; simp only at hWidth hlVal hRes ⊢; subst bw
  -- Structural facts about the three created ops.
  have hCastXType : xCastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hRetType : retOp.getOpType! ctx₃.raw = .riscv dst := by grind
  have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastXOperands : xCastOp.getOperands! ctx₃.raw = #[lhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCastX (operation := xCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := xCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xCastOp)]
  have hRetOperands : retOp.getOperands! ctx₃.raw
      = #[ValuePtr.opResult (xCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := retOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := retOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
  have hRetProps : retOp.getProperties! ctx₃.raw (.riscv dst)
      = cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk imm.value (IntegerType.mk 64))) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hRet (operation := retOp)]
  -- The cast-back op's result type is `i{width}`.
  have hCBType : ((op.getResult 0).get! ctx₂.raw).type
      = (⟨Attribute.integerType { bitwidth := width }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hRet
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCastX
          (value := ValuePtr.opResult (op.getResult 0))]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hCastXResTypes : xCastOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastX (operation := xCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := xCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xCastOp)]
  have hRetResTypes : retOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := retOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := retOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.integerType { bitwidth := width }, by grind⟩] := by grind
  -- Interpretation tail: execute `interpretOpList [xCastOp, retOp, castBackOp]` in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hCastXType hCastXOperands hCastXResTypes hXVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := rFn imm.value (LLVM.Int.toReg xt))
      (fun rt bo mem => hSemR imm.value _ rt bo mem)
      hRetType hRetProps hRetOperands hRetResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int width
        (RISCV.Reg.toInt (rFn imm.value (LLVM.Int.toReg xt)) width)], ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using hRefine xlv xt imm.value _ hLo hHi hxtRef⟩

set_option maxHeartbeats 1000000 in
/-- Correctness proof for the `shl`/`lshr` `selectBinopImmLocal` lowerings. Identical in shape to
    `selectBinopImmLocal_preservesSemantics`, but the source op verifies via `verifyLLVMShift`
    (`IsVerifiedLLVMShift`) rather than `IsVerifiedIntegerBinop`: the shift amount's width is not
    pinned statically, so the operand-width equality is recovered from the successful interpretation
    (`matchShiftOp_interpretOp_unfold`) and then substituted, collapsing the proof to the binop
    shape. -/
theorem selectBinopImmLocal_shift_preservesSemantics {α : Type} {srcOp : Llvm}
    {matchPair : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × α)}
    {dst : Riscv} {hdst : Riscv.propertiesOf dst = RISCVImmediateProperties}
    {width : Nat} {lo hi : Int}
    {rFn : Int → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs a},
        matchPair op ctx = some (lhs, rhs, a) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[lhs, rhs])
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedLLVMShift ctx)
    (hSemSrc : ∀ (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
        (props : propertiesOf (.llvm srcOp)) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw' y] blockOperands mem
          = some (.ok res) →
        ∃ (h' : bw' = bw), res = (#[.int bw (srcFn x (h' ▸ y) props)], mem, none))
    (hSemR : ∀ (c : Int) (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' dst
            (cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk c (IntegerType.mk 64))))
            resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (rFn c r)], mem, none)))
    (hRefine : ∀ (x xt : Data.LLVM.Int width) (c : Int) (props : propertiesOf (.llvm srcOp)),
        lo ≤ c → c ≤ hi → x ⊒ xt →
        srcFn x (Data.LLVM.Int.constant width c) props
          ⊒ RISCV.Reg.toInt (rFn c (LLVM.Int.toReg xt)) width)
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchPair dst hdst width lo hi)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectBinopImmLocal matchPair dst hdst width lo hi)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (selectBinopImmLocal matchPair dst hdst width lo hi)}
    {h₄ : LocalRewritePattern.ReturnValues (selectBinopImmLocal matchPair dst hdst width lo hi)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchPair dst hdst width lo hi) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectBinopImmLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  have hMatchSome : (matchPair op ctx.raw).isSome := by
    cases hM : matchPair op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, a⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hResEqOp0, intType2, hOp1Type⟩ := hVerified opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The result type must be an integer for the pattern to fire; derive it and hence `lhs`'s type.
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, ← hResEqOp0, hResType]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType2 := by
    rw [← hOperand1, hOp1Type]
  rw [hResType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hWidth
  have hCstSome : (matchConstantIntVal rhs ctx.raw).isSome := by
    cases hM : matchConstantIntVal rhs ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨imm, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue hrange => simp at hpattern
  rename_i hRange
  obtain ⟨hLo, hHi⟩ : lo ≤ imm.value ∧ imm.value ≤ hi := by omega
  -- Unfold the shift interpretation: recovers the width equality `h'` between the two operands.
  obtain ⟨xlv, xrv, h', hlVal, hrVal, hMem, hRes, hCf⟩ :=
    matchShiftOp_interpretOp_unfold (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl hSemSrc hinterp hLhsType hRhsType
  subst hCf
  -- Both operand widths equal `width`; substitute so the shift collapses to the binop shape.
  obtain ⟨bw⟩ := intType; obtain ⟨bw2⟩ := intType2
  simp only at hWidth h' hlVal hRes ⊢
  subst bw; subst bw2
  have hDomLhs : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hrhsVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hRhsType
  obtain rfl : xrv = Data.LLVM.Int.constant width imm.value := by
    have := hrVal.symm.trans hrhsVal
    simpa using this
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have vNotOpLhs : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  peelCastToRegLocal hpattern ctx₁ xCastOp hCastX hDomLhs hDomLhs₁
  peelOpCreation! hpattern ctx₂ retOp hRet hDomLhs₁ hDomLhs₂
  peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDomLhs₂ hDomLhs₃
  cleanupHpattern hpattern
  obtain ⟨xt, hXVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hlVal
      hDomLhs hDomLhs₃ vNotOpLhs
  have hCastXType : xCastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hRetType : retOp.getOpType! ctx₃.raw = .riscv dst := by grind
  have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastXOperands : xCastOp.getOperands! ctx₃.raw = #[lhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCastX (operation := xCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := xCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xCastOp)]
  have hRetOperands : retOp.getOperands! ctx₃.raw
      = #[ValuePtr.opResult (xCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := retOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := retOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
  have hRetProps : retOp.getProperties! ctx₃.raw (.riscv dst)
      = cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk imm.value (IntegerType.mk 64))) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hRet (operation := retOp)]
  have hCBType : ((op.getResult 0).get! ctx₂.raw).type
      = (⟨Attribute.integerType { bitwidth := width }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hRet
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCastX
          (value := ValuePtr.opResult (op.getResult 0))]
    rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
    rw [h1]; exact Subtype.ext hResType
  have hCastXResTypes : xCastOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastX (operation := xCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := xCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xCastOp)]
  have hRetResTypes : retOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := retOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := retOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.integerType { bitwidth := width }, by grind⟩] := by grind
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hCastXType hCastXOperands hCastXResTypes hXVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := rFn imm.value (LLVM.Int.toReg xt))
      (fun rt bo mem => hSemR imm.value _ rt bo mem)
      hRetType hRetProps hRetOperands hRetResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int width
        (RISCV.Reg.toInt (rFn imm.value (LLVM.Int.toReg xt)) width)], ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using hRefine xlv xt imm.value _ hLo hHi hxtRef⟩

/-- For a 12-bit-representable immediate `c`, sign-extending its 12-bit encoding to 64 bits gives
    the 64-bit encoding of `c`. This bridges the RISC-V immediate ops (which sign-extend a 12-bit
    field) to the LLVM constant (a full-width value), letting the refinement lemmas abstract the
    shared `BitVec.ofInt 64 c` and discharge the rest with `veir_bv_decide`. -/
theorem signExtend_ofInt_12_64 (c : Int) (hlo : -2048 ≤ c) (hhi : c ≤ 2047) :
    BitVec.signExtend 64 (BitVec.ofInt 12 c) = BitVec.ofInt 64 c := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt, BitVec.toInt_ofInt,
    show (2 ^ 12 : Nat) = 4096 from rfl, show (2 ^ 64 : Nat) = 18446744073709551616 from rfl]
  simp only [Int.bmod]
  omega

/-- Truncating the 64-bit encoding of `c` to 6 bits gives its 6-bit encoding (used to bridge the
    6-bit shift-amount field of the RV64 immediate shifts to the LLVM shift's full-width operand). -/
theorem setWidth_ofInt_6_64 (c : Int) :
    BitVec.setWidth 6 (BitVec.ofInt 64 c) = BitVec.ofInt 6 c := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]
  omega

/-- Truncating the 64-bit encoding of `c` to 5 bits gives its 5-bit encoding (for the `*w`
    immediate shifts, whose shift-amount field is 5 bits). -/
theorem setWidth_ofInt_5_64 (c : Int) :
    BitVec.setWidth 5 (BitVec.ofInt 64 c) = BitVec.ofInt 5 c := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]
  omega

/-- Correctness of the `riscv.addi` lowering of a 64-bit `llvm.add` with a constant `imm12`
    right-hand operand. -/
theorem addi_isRefinedBy {nsw nuw : Bool} {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.add x (Data.LLVM.Int.constant 64 c) nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.addi (BitVec.ofInt 12 c) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.addi, signExtend_ofInt_12_64 c hlo hhi]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

theorem addi_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchAdd .addi rfl 64 (-2048) 2047)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges
      (selectBinopImmLocal matchAdd .addi rfl 64 (-2048) 2047)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (selectBinopImmLocal matchAdd .addi rfl 64 (-2048) 2047)}
    {h₄ : LocalRewritePattern.ReturnValues
      (selectBinopImmLocal matchAdd .addi rfl 64 (-2048) 2047)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchAdd .addi rfl 64 (-2048) 2047) h h₂ h₃ h₄ :=
  selectBinopImmLocal_preservesSemantics
    (srcOp := .add) (dst := .addi) (hdst := rfl) (width := 64) (lo := -2048) (hi := 2047)
    (srcFn := fun x y props => Data.LLVM.Int.add x y props.nsw props.nuw)
    (rFn := fun c r => Data.RISCV.addi (BitVec.ofInt 12 c) r)
    (fun hm => ⟨(matchAdd_implies hm).1, (matchAdd_implies hm).2.1, (matchAdd_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_add
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun x xt c props hlo hhi h => addi_isRefinedBy (nsw := props.nsw) (nuw := props.nuw) c hlo hhi h)

/-- Correctness of the `riscv.ori` lowering of a 64-bit `llvm.or` with a constant `imm12`. -/
theorem ori_isRefinedBy {disjoint : Bool} {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.or x (Data.LLVM.Int.constant 64 c) disjoint
      ⊒ RISCV.Reg.toInt (Data.RISCV.ori (BitVec.ofInt 12 c) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.ori, signExtend_ofInt_12_64 c hlo hhi]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

theorem ori_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchOr .ori rfl 64 (-2048) 2047)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges
      (selectBinopImmLocal matchOr .ori rfl 64 (-2048) 2047)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (selectBinopImmLocal matchOr .ori rfl 64 (-2048) 2047)}
    {h₄ : LocalRewritePattern.ReturnValues
      (selectBinopImmLocal matchOr .ori rfl 64 (-2048) 2047)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchOr .ori rfl 64 (-2048) 2047) h h₂ h₃ h₄ :=
  selectBinopImmLocal_preservesSemantics
    (srcOp := .or) (dst := .ori) (hdst := rfl) (width := 64) (lo := -2048) (hi := 2047)
    (srcFn := fun x y props => Data.LLVM.Int.or x y props.disjoint)
    (rFn := fun c r => Data.RISCV.ori (BitVec.ofInt 12 c) r)
    (fun hm => ⟨(matchOr_implies hm).1, (matchOr_implies hm).2.1, (matchOr_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun x xt c props hlo hhi h => ori_isRefinedBy (disjoint := props.disjoint) c hlo hhi h)

/-- Correctness of the `riscv.andi` lowering of a 64-bit `llvm.and` with a constant `imm12`. -/
theorem andi_isRefinedBy {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.and x (Data.LLVM.Int.constant 64 c)
      ⊒ RISCV.Reg.toInt (Data.RISCV.andi (BitVec.ofInt 12 c) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.andi, signExtend_ofInt_12_64 c hlo hhi]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

theorem andi_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchAnd .andi rfl 64 (-2048) 2047)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges
      (selectBinopImmLocal matchAnd .andi rfl 64 (-2048) 2047)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (selectBinopImmLocal matchAnd .andi rfl 64 (-2048) 2047)}
    {h₄ : LocalRewritePattern.ReturnValues
      (selectBinopImmLocal matchAnd .andi rfl 64 (-2048) 2047)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchAnd .andi rfl 64 (-2048) 2047) h h₂ h₃ h₄ :=
  selectBinopImmLocal_preservesSemantics
    (srcOp := .and) (dst := .andi) (hdst := rfl) (width := 64) (lo := -2048) (hi := 2047)
    (srcFn := fun x y _ => Data.LLVM.Int.and x y)
    (rFn := fun c r => Data.RISCV.andi (BitVec.ofInt 12 c) r)
    (fun hm => ⟨(matchAnd_implies hm).1, (matchAnd_implies hm).2.1, (matchAnd_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun x xt c _ hlo hhi h => andi_isRefinedBy c hlo hhi h)

/-- Correctness of the `riscv.xori` lowering of a 64-bit `llvm.xor` with a constant `imm12`. -/
theorem xori_isRefinedBy {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.xor x (Data.LLVM.Int.constant 64 c)
      ⊒ RISCV.Reg.toInt (Data.RISCV.xori (BitVec.ofInt 12 c) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.xori, signExtend_ofInt_12_64 c hlo hhi]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

theorem xori_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchXor .xori rfl 64 (-2048) 2047)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges
      (selectBinopImmLocal matchXor .xori rfl 64 (-2048) 2047)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (selectBinopImmLocal matchXor .xori rfl 64 (-2048) 2047)}
    {h₄ : LocalRewritePattern.ReturnValues
      (selectBinopImmLocal matchXor .xori rfl 64 (-2048) 2047)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchXor .xori rfl 64 (-2048) 2047) h h₂ h₃ h₄ :=
  selectBinopImmLocal_preservesSemantics
    (srcOp := .xor) (dst := .xori) (hdst := rfl) (width := 64) (lo := -2048) (hi := 2047)
    (srcFn := fun x y _ => Data.LLVM.Int.xor x y)
    (rFn := fun c r => Data.RISCV.xori (BitVec.ofInt 12 c) r)
    (fun hm => ⟨(matchXor_implies hm).1, (matchXor_implies hm).2.1, (matchXor_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun x xt c _ hlo hhi h => xori_isRefinedBy c hlo hhi h)

/-- Correctness of the `riscv.srai` lowering of a 64-bit `llvm.ashr` by a constant `uimm6`. -/
theorem srai_isRefinedBy {exact : Bool} {x xt : Data.LLVM.Int 64} (c : Int)
    (_hlo : 0 ≤ c) (_hhi : c ≤ 63) (h : x ⊒ xt) :
    Data.LLVM.Int.ashr x (Data.LLVM.Int.constant 64 c) exact
      ⊒ RISCV.Reg.toInt (Data.RISCV.srai (BitVec.ofInt 6 c) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.srai, ← setWidth_ofInt_6_64 c]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

theorem srai_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchAshr .srai rfl 64 0 63)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectBinopImmLocal matchAshr .srai rfl 64 0 63)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (selectBinopImmLocal matchAshr .srai rfl 64 0 63)}
    {h₄ : LocalRewritePattern.ReturnValues (selectBinopImmLocal matchAshr .srai rfl 64 0 63)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchAshr .srai rfl 64 0 63) h h₂ h₃ h₄ :=
  selectBinopImmLocal_preservesSemantics
    (srcOp := .ashr) (dst := .srai) (hdst := rfl) (width := 64) (lo := 0) (hi := 63)
    (srcFn := fun x y props => Data.LLVM.Int.ashr x y props.exact)
    (rFn := fun c r => Data.RISCV.srai (BitVec.ofInt 6 c) r)
    (fun hm => ⟨(matchAshr_implies hm).1, (matchAshr_implies hm).2.1, (matchAshr_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_ashr
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun x xt c props hlo hhi h => srai_isRefinedBy (exact := props.exact) c hlo hhi h)

/-- Correctness of the `riscv.addiw` lowering of a 32-bit `llvm.add` with a constant `imm12`. -/
theorem addiw_isRefinedBy {nsw nuw : Bool} {x xt : Data.LLVM.Int 32} (c : Int)
    (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.add x (Data.LLVM.Int.constant 32 c) nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.addiw (BitVec.ofInt 12 c) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.RISCV.addiw, signExtend_ofInt_12_64 c hlo hhi]
  simp only [Data.LLVM.Int.constant]
  rw [← BitVec.setWidth_ofInt_32_64 c]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

theorem addiw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchAdd .addiw rfl 32 (-2048) 2047)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges
      (selectBinopImmLocal matchAdd .addiw rfl 32 (-2048) 2047)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds
      (selectBinopImmLocal matchAdd .addiw rfl 32 (-2048) 2047)}
    {h₄ : LocalRewritePattern.ReturnValues
      (selectBinopImmLocal matchAdd .addiw rfl 32 (-2048) 2047)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchAdd .addiw rfl 32 (-2048) 2047) h h₂ h₃ h₄ :=
  selectBinopImmLocal_preservesSemantics
    (srcOp := .add) (dst := .addiw) (hdst := rfl) (width := 32) (lo := -2048) (hi := 2047)
    (srcFn := fun x y props => Data.LLVM.Int.add x y props.nsw props.nuw)
    (rFn := fun c r => Data.RISCV.addiw (BitVec.ofInt 12 c) r)
    (fun hm => ⟨(matchAdd_implies hm).1, (matchAdd_implies hm).2.1, (matchAdd_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_add
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun x xt c props hlo hhi h => addiw_isRefinedBy (nsw := props.nsw) (nuw := props.nuw) c hlo hhi h)

/-- Correctness of the `riscv.sraiw` lowering of a 32-bit `llvm.ashr` by a constant `uimm5`. -/
theorem sraiw_isRefinedBy {exact : Bool} {x xt : Data.LLVM.Int 32} (c : Int)
    (_hlo : 0 ≤ c) (_hhi : c ≤ 31) (h : x ⊒ xt) :
    Data.LLVM.Int.ashr x (Data.LLVM.Int.constant 32 c) exact
      ⊒ RISCV.Reg.toInt (Data.RISCV.sraiw (BitVec.ofInt 5 c) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.RISCV.sraiw, ← setWidth_ofInt_5_64 c]
  simp only [Data.LLVM.Int.constant]
  rw [← BitVec.setWidth_ofInt_32_64 c]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

theorem sraiw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchAshr .sraiw rfl 32 0 31)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectBinopImmLocal matchAshr .sraiw rfl 32 0 31)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (selectBinopImmLocal matchAshr .sraiw rfl 32 0 31)}
    {h₄ : LocalRewritePattern.ReturnValues (selectBinopImmLocal matchAshr .sraiw rfl 32 0 31)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchAshr .sraiw rfl 32 0 31) h h₂ h₃ h₄ :=
  selectBinopImmLocal_preservesSemantics
    (srcOp := .ashr) (dst := .sraiw) (hdst := rfl) (width := 32) (lo := 0) (hi := 31)
    (srcFn := fun x y props => Data.LLVM.Int.ashr x y props.exact)
    (rFn := fun c r => Data.RISCV.sraiw (BitVec.ofInt 5 c) r)
    (fun hm => ⟨(matchAshr_implies hm).1, (matchAshr_implies hm).2.1, (matchAshr_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_ashr
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun x xt c props hlo hhi h => sraiw_isRefinedBy (exact := props.exact) c hlo hhi h)

/-- Correctness of the `riscv.slli` lowering of a 64-bit `llvm.shl` by a constant `uimm6`. -/
theorem slli_isRefinedBy {nsw nuw : Bool} {x xt : Data.LLVM.Int 64} (c : Int)
    (_hlo : 0 ≤ c) (_hhi : c ≤ 63) (h : x ⊒ xt) :
    Data.LLVM.Int.shl x (Data.LLVM.Int.constant 64 c) nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.slli (BitVec.ofInt 6 c) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.slli, ← setWidth_ofInt_6_64 c]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

/-- Correctness of the `riscv.srli` lowering of a 64-bit `llvm.lshr` by a constant `uimm6`. -/
theorem srli_isRefinedBy {exact : Bool} {x xt : Data.LLVM.Int 64} (c : Int)
    (_hlo : 0 ≤ c) (_hhi : c ≤ 63) (h : x ⊒ xt) :
    Data.LLVM.Int.lshr x (Data.LLVM.Int.constant 64 c) exact
      ⊒ RISCV.Reg.toInt (Data.RISCV.srli (BitVec.ofInt 6 c) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.srli, ← setWidth_ofInt_6_64 c]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

/-- Correctness of the `riscv.slliw` lowering of a 32-bit `llvm.shl` by a constant `uimm5`. -/
theorem slliw_isRefinedBy {nsw nuw : Bool} {x xt : Data.LLVM.Int 32} (c : Int)
    (_hlo : 0 ≤ c) (_hhi : c ≤ 31) (h : x ⊒ xt) :
    Data.LLVM.Int.shl x (Data.LLVM.Int.constant 32 c) nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.slliw (BitVec.ofInt 5 c) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.RISCV.slliw, ← setWidth_ofInt_5_64 c]
  simp only [Data.LLVM.Int.constant]
  rw [← BitVec.setWidth_ofInt_32_64 c]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

/-- Correctness of the `riscv.srliw` lowering of a 32-bit `llvm.lshr` by a constant `uimm5`. -/
theorem srliw_isRefinedBy {exact : Bool} {x xt : Data.LLVM.Int 32} (c : Int)
    (_hlo : 0 ≤ c) (_hhi : c ≤ 31) (h : x ⊒ xt) :
    Data.LLVM.Int.lshr x (Data.LLVM.Int.constant 32 c) exact
      ⊒ RISCV.Reg.toInt (Data.RISCV.srliw (BitVec.ofInt 5 c) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.RISCV.srliw, ← setWidth_ofInt_5_64 c]
  simp only [Data.LLVM.Int.constant]
  rw [← BitVec.setWidth_ofInt_32_64 c]
  generalize BitVec.ofInt 64 c = v
  revert h
  veir_bv_decide

/-- Shared discharge for the shift `hSemSrc`: the interpreter's own width guard forces the shift
    amount to have the operand's width, and the result is the shift value. -/
private theorem shl_shiftSem (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
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

private theorem lshr_shiftSem (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
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

theorem slli_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchShl .slli rfl 64 0 63)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectBinopImmLocal matchShl .slli rfl 64 0 63)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (selectBinopImmLocal matchShl .slli rfl 64 0 63)}
    {h₄ : LocalRewritePattern.ReturnValues (selectBinopImmLocal matchShl .slli rfl 64 0 63)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchShl .slli rfl 64 0 63) h h₂ h₃ h₄ :=
  selectBinopImmLocal_shift_preservesSemantics
    (srcOp := .shl) (dst := .slli) (hdst := rfl) (width := 64) (lo := 0) (hi := 63)
    (srcFn := fun x y props => Data.LLVM.Int.shl x y props.nsw props.nuw)
    (rFn := fun c r => Data.RISCV.slli (BitVec.ofInt 6 c) r)
    (fun hm => ⟨(matchShl_implies hm).1, (matchShl_implies hm).2.1, (matchShl_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_shl
    shl_shiftSem
    (fun _ _ _ _ _ => rfl)
    (fun _ _ c props hlo hhi h => slli_isRefinedBy (nsw := props.nsw) (nuw := props.nuw) c hlo hhi h)

theorem srli_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchLshr .srli rfl 64 0 63)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectBinopImmLocal matchLshr .srli rfl 64 0 63)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (selectBinopImmLocal matchLshr .srli rfl 64 0 63)}
    {h₄ : LocalRewritePattern.ReturnValues (selectBinopImmLocal matchLshr .srli rfl 64 0 63)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchLshr .srli rfl 64 0 63) h h₂ h₃ h₄ :=
  selectBinopImmLocal_shift_preservesSemantics
    (srcOp := .lshr) (dst := .srli) (hdst := rfl) (width := 64) (lo := 0) (hi := 63)
    (srcFn := fun x y props => Data.LLVM.Int.lshr x y props.exact)
    (rFn := fun c r => Data.RISCV.srli (BitVec.ofInt 6 c) r)
    (fun hm => ⟨(matchLshr_implies hm).1, (matchLshr_implies hm).2.1, (matchLshr_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_lshr
    lshr_shiftSem
    (fun _ _ _ _ _ => rfl)
    (fun _ _ c props hlo hhi h => srli_isRefinedBy (exact := props.exact) c hlo hhi h)

theorem slliw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchShl .slliw rfl 32 0 31)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectBinopImmLocal matchShl .slliw rfl 32 0 31)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (selectBinopImmLocal matchShl .slliw rfl 32 0 31)}
    {h₄ : LocalRewritePattern.ReturnValues (selectBinopImmLocal matchShl .slliw rfl 32 0 31)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchShl .slliw rfl 32 0 31) h h₂ h₃ h₄ :=
  selectBinopImmLocal_shift_preservesSemantics
    (srcOp := .shl) (dst := .slliw) (hdst := rfl) (width := 32) (lo := 0) (hi := 31)
    (srcFn := fun x y props => Data.LLVM.Int.shl x y props.nsw props.nuw)
    (rFn := fun c r => Data.RISCV.slliw (BitVec.ofInt 5 c) r)
    (fun hm => ⟨(matchShl_implies hm).1, (matchShl_implies hm).2.1, (matchShl_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_shl
    shl_shiftSem
    (fun _ _ _ _ _ => rfl)
    (fun _ _ c props hlo hhi h => slliw_isRefinedBy (nsw := props.nsw) (nuw := props.nuw) c hlo hhi h)

theorem srliw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (selectBinopImmLocal matchLshr .srliw rfl 32 0 31)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectBinopImmLocal matchLshr .srliw rfl 32 0 31)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (selectBinopImmLocal matchLshr .srliw rfl 32 0 31)}
    {h₄ : LocalRewritePattern.ReturnValues (selectBinopImmLocal matchLshr .srliw rfl 32 0 31)} :
    LocalRewritePattern.PreservesSemantics
      (selectBinopImmLocal matchLshr .srliw rfl 32 0 31) h h₂ h₃ h₄ :=
  selectBinopImmLocal_shift_preservesSemantics
    (srcOp := .lshr) (dst := .srliw) (hdst := rfl) (width := 32) (lo := 0) (hi := 31)
    (srcFn := fun x y props => Data.LLVM.Int.lshr x y props.exact)
    (rFn := fun c r => Data.RISCV.srliw (BitVec.ofInt 5 c) r)
    (fun hm => ⟨(matchLshr_implies hm).1, (matchLshr_implies hm).2.1, (matchLshr_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_lshr
    lshr_shiftSem
    (fun _ _ _ _ _ => rfl)
    (fun _ _ c props hlo hhi h => srliw_isRefinedBy (exact := props.exact) c hlo hhi h)

/--
info: 'Veir.selectBinopImmLocal_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms selectBinopImmLocal_preservesSemantics

/--
info: 'Veir.addi_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms addi_local_preservesSemantics

/--
info: 'Veir.selectBinopImmLocal_shift_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms selectBinopImmLocal_shift_preservesSemantics

/--
info: 'Veir.slli_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 slli_isRefinedBy._native.bv_decide.ax_1_7,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms slli_local_preservesSemantics

end Veir
