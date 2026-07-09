import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.Casting
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas

namespace Veir

/-! ## Correctness of `same_val_zero_1_local` (`llvm.xor x x` → `llvm.mlir.constant 0`)

The MIR combine `same_val_zero_1` rewrites `llvm.xor x x` to a constant zero. This is the
`LocalRewritePattern` restatement (`same_val_zero_1_local`, `RISCV64.lean`) and its
`PreservesSemantics` proof. It reads the (equal) operands of the matched `xor` with the
binary-source unfolder, then emits a single `llvm.mlir.constant 0` — so the structure is a
binop *match* (as in `LowerBinaryW`) followed by a single constant *creation* (as in
`LowerConst`). -/

/-- Nullary `llvm.mlir.constant` specialization of `interpretOp_forward`: an `llvm.mlir.constant`
op with no operands, a single `i{bw}` result type, and integer value attribute `intAttr` binds
that result to `.int bw (LLVM.Int.constant bw intAttr.value)`, leaving memory and every other
value unchanged. Mirrors `interpretOp_riscv_li_forward` (`LowerConst.lean`). -/
theorem interpretOp_llvm_constant_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {intType : IntegerType} {hIsTy}
    {intAttr : IntegerAttr}
    (hType : theOp.getOpType! ctx.raw = .llvm .mlir__constant)
    (hProps : (theOp.getProperties! ctx.raw (.llvm .mlir__constant)).value = .integer intAttr)
    (hOperands : theOp.getOperands! ctx.raw = #[])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.integerType intType, hIsTy⟩]) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.int intType.bitwidth
            (Data.LLVM.Int.constant intType.bitwidth intAttr.value)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[])
      (results := #[.int intType.bitwidth (Data.LLVM.Int.constant intType.bitwidth intAttr.value)])
      (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp only [interpretOp', Llvm.interpretOp', hProps, hResTypes, Interp]
          rfl)
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  have hNRes : 0 < theOp.getNumResults! ctx.raw := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hResTypes]; simp
  grind

/-- The Layer-0 data refinement: `xor x x` (poison when `x` is poison, else `0`) is refined by the
constant `0`. When `x` is poison the source poison is refined by any value; otherwise both sides are
`0`. -/
theorem xor_self_isRefinedBy_constant_zero {w : Nat} (x : Data.LLVM.Int w) :
    Data.LLVM.Int.xor x x ⊒ Data.LLVM.Int.constant w 0 := by
  rw [Data.LLVM.Int.isRefinedBy_iff]
  refine ⟨fun _ => Data.LLVM.Int.isPoison_constant _, fun hnp _ => ?_⟩
  rw [Data.LLVM.Int.getValue_xor _ _ hnp, Data.LLVM.Int.getValue_constant]
  simp

set_option maxHeartbeats 1000000 in
/-- Correctness of the `same_val_zero_1_local` lowering: `llvm.xor x x` lowers to a single
`llvm.mlir.constant 0` of the (integer) result type, which refines the `xor`. -/
theorem same_val_zero_1_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics same_val_zero_1_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, same_val_zero_1_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch reaches the `some (...)` RHS.
  have hMatchSome : (matchXor op ctx.raw).isSome := by
    cases hM : matchXor op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, x1, xprops⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic + verification facts.
  have ⟨hOpType, hNRes, hOperands, hProps⟩ := matchXor_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by clear hpattern; grind
  have hVer := OperationPtr.Verified.llvm_xor opVerif hOpType
  obtain ⟨hNResV, hNOper, hNSucc, hNReg, intType, hResTy, hOp0Ty, hOp1Ty⟩ := hVer
  -- The `x != x1` guard is false, so the two operands are equal.
  have hResTyVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResTy]
  have hxx1 : x = x1 := by
    rcases Decidable.em (x = x1) with heq | hne
    · exact heq
    · rw [if_neg hne] at hpattern
      exact absurd hpattern (by simp)
  rw [if_pos hxx1] at hpattern
  -- Resolve the result-type destructuring match: the result type is `integerType intType`.
  rw [hResTyVal] at hpattern
  simp only [] at hpattern
  -- The operands have integer type `intType`, feeding the source-interpretation unfolder.
  have hx0 : op.getOperand! ctx.raw 0 = x := by
    have : (op.getOperands! ctx.raw)[0]! = x := by rw [hOperands]; rfl
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hx1 : op.getOperand! ctx.raw 1 = x1 := by
    have : (op.getOperands! ctx.raw)[1]! = x1 := by rw [hOperands]; rfl
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hLhsType : (x.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hx0, hOp0Ty]
  have hRhsType : (x1.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hx1, hOp1Ty]
  -- Source value: `op`'s single result is `xor xv x1v`.
  obtain ⟨xv, x1v, hxVal, hx1Val, hMemEq, hResVal, rfl⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .xor)
      (srcFn := fun a b _ => Data.LLVM.Int.xor a b)
      (props := xprops) opInBounds hOpType hNRes hOperands hProps
      (by intro bw a b props resultTypes blockOperands mem res hI
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hI
          grind)
      hinterp hLhsType hRhsType
  -- The two operands are the same value, so `xv = x1v`.
  have hxvEq : xv = x1v := by
    rw [hxx1] at hxVal; rw [hxVal] at hx1Val; simpa using hx1Val
  subst hxvEq
  -- Source values array: `op`'s single result value is `xor xv xv`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Peel the single created op: the `llvm.mlir.constant`.
  peelOpCreation hpattern ctx₁ cstOp hCst
  rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
    (by clear hpattern; simp)] at hCst
  cleanupHpattern hpattern
  -- Structural facts about the created constant op in the final context `ctx₁`.
  have hCstType : cstOp.getOpType! ctx₁.raw = .llvm .mlir__constant := by grind
  have hCstOperands : cstOp.getOperands! ctx₁.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCst (operation := cstOp)]
  have hCstProps : (cstOp.getProperties! ctx₁.raw (.llvm .mlir__constant)).value
      = .integer (IntegerAttr.mk 0 intType) := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hCst (operation := cstOp)]
  have hCstResTypes : cstOp.getResultTypes! ctx₁.raw
      = #[⟨Attribute.integerType intType, (by grind)⟩] := by
    have hty : ((op.getResult 0).get! ctx.raw).type = ⟨Attribute.integerType intType, by grind⟩ :=
      Subtype.ext hResTyVal
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCst (operation := cstOp)]
  -- Interpretation tail: execute `interpretOpList [cstOp]` in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hCstType hCstProps hCstOperands hCstResTypes
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.constant intType.bitwidth (IntegerAttr.mk 0 intType).value)], ?_, ?_⟩
    · simp [hRes₁, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using xor_self_isRefinedBy_constant_zero xv⟩

/-- info: 'Veir.same_val_zero_1_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominatesIp,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 ValuePtr.dominatesIp,
 MemoryState.llvmLoad._native.bv_decide.ax_8] -/
#guard_msgs in
#print axioms same_val_zero_1_local_preservesSemantics

end Veir
