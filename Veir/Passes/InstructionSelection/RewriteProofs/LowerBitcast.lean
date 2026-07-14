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

namespace Veir

/-!
## Correctness of `bitcast_local`

`llvm.bitcast` reinterprets a value as another type of the same bitwidth. Integers, bytes and
pointers all live in a `!riscv.reg` after instruction selection, so the lowering is the pair
`unrealized_conversion_cast` (operand → register) → `unrealized_conversion_cast` (register → the
result type).

Six source/result combinations reach the interpreter's `bitcast` arm and fire the pattern:
`int → int`, `int → byte`, `byte → byte`, `byte → int`, `ptr → ptr` and `ptr → byte`. `int ↔ ptr`
has no interpreter arm, so those goals are vacuous, and `byte → ptr` is excluded from the pattern
(see `isBitcastByteToPtr`).

Each combination is closed by one of the data-level lemmas below: a round trip through a register
refines the source conversion. These are refinements rather than equalities because `Int.toReg` and
`Byte.toReg` map poison to concrete register bits, and a concrete value refines a poison one.
-/

/-- The all-poison byte refines every byte, at any (symbolic) width. -/
theorem allPoison_isRefinedBy {w : Nat} (b : Data.LLVM.Byte w) :
    (⟨0, BitVec.allOnes w, by simp⟩ : Data.LLVM.Byte w) ⊒ b := by
  simp [Data.LLVM.Byte.isRefinedBy]

/-- Round trip `i{bw} → reg → i{bw}` refines the identity, for widths in `{8, 16, 32, 64}`. -/
theorem bitcast_isRefinedBy_toInt {bw : Nat} (hbw : bw ∈ [8, 16, 32, 64])
    {x xt : Data.LLVM.Int bw} (h : x ⊒ xt) :
    x ⊒ RISCV.Reg.toInt (LLVM.Int.toReg xt) bw := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbw
  rcases hbw with rfl | rfl | rfl | rfl <;> (revert h; veir_bv_decide)

/-- Round trip `i{bw} → reg → byte{bw}` refines `Byte.fromInt`, for widths in `{8, 16, 32, 64}`.
    `Byte.fromInt` branches on the source poison, so we case on it rather than bit-blast the
    dependent `if`: a poison source becomes the all-poison byte, which refines everything. -/
theorem bitcast_isRefinedBy_intToByte {bw : Nat} (hbw : bw ∈ [8, 16, 32, 64])
    {x xt : Data.LLVM.Int bw} (h : x ⊒ xt) :
    Data.LLVM.Byte.fromInt x ⊒ RISCV.Reg.toByte (LLVM.Int.toReg xt) bw := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbw
  cases x with
  | poison =>
    simpa only [Data.LLVM.Byte.fromInt, Data.LLVM.Int.isPoison_of_poison, dite_true]
      using allPoison_isRefinedBy _
  | val v =>
    obtain rfl : xt = Data.LLVM.Int.val v := by cases xt <;> simp_all [isRefinedBy]
    simp only [Data.LLVM.Byte.fromInt, Data.LLVM.Int.isPoison, LLVM.Int.toReg, RISCV.Reg.toByte,
      Data.LLVM.Int.getValue, dite_false, Bool.false_eq_true]
    rcases hbw with rfl | rfl | rfl | rfl <;> veir_bv_decide

/-- Round trip `byte{bw} → reg → byte{bw}` refines the identity, for widths in `{8, 16, 32, 64}`. -/
theorem bitcast_isRefinedBy_toByte {bw : Nat} (hbw : bw ∈ [8, 16, 32, 64])
    {x xt : Data.LLVM.Byte bw} (h : x ⊒ xt) :
    x ⊒ RISCV.Reg.toByte (LLVM.Byte.toReg xt) bw := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbw
  rcases hbw with rfl | rfl | rfl | rfl <;>
    (revert h; simp only [RISCV.Reg.toByte, LLVM.Byte.toReg]; veir_bv_decide)

/-- Round trip `byte{bw} → reg → i{bw}` refines `Byte.toInt`, for widths in `{8, 16, 32, 64}`.
    `Byte.toInt` branches on the source poison mask, so we case on it: a source with any poison bit
    is `Int.poison`, which refines everything. -/
theorem bitcast_isRefinedBy_byteToInt {bw : Nat} (hbw : bw ∈ [8, 16, 32, 64])
    {x xt : Data.LLVM.Byte bw} (h : x ⊒ xt) :
    Data.LLVM.Byte.toInt x ⊒ RISCV.Reg.toInt (LLVM.Byte.toReg xt) bw := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbw
  simp only [Data.LLVM.Byte.toInt]
  split
  · rename_i hp
    rcases hbw with rfl | rfl | rfl | rfl <;>
      (revert h; simp only [RISCV.Reg.toInt, LLVM.Byte.toReg, isRefinedBy]
       revert hp; veir_bv_decide)
  · trivial

/-- Round trip `ptr → reg → byte{64}` refines `Byte.fromUInt64`. -/
theorem bitcast_isRefinedBy_addrToByte (a : UInt64) :
    Data.LLVM.Byte.fromUInt64 a ⊒ RISCV.Reg.toByte ⟨BitVec.ofNat 64 a.toNat⟩ 64 := by
  simp only [Data.LLVM.Byte.fromUInt64, Data.LLVM.Byte.fromBitVec, RISCV.Reg.toByte,
    show BitVec.ofNat 64 a.toNat = a.toBitVec from by simp]
  veir_bv_decide

set_option maxHeartbeats 2000000 in
theorem bitcast_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps bitcast_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges bitcast_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds bitcast_local}
    {h₄ : LocalRewritePattern.ReturnValues bitcast_local} :
    LocalRewritePattern.PreservesSemantics bitcast_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, bitcast_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchBitcast op ctx.raw).isSome := by
    cases hM : matchBitcast op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operand, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchBitcast_implies hMatch
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
  -- The single source value is `op`'s result.
  have hResults : op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] := by
    -- Workaround for a `grind` internalization bug on v4.31.0: `hpattern`/`hInterp'` contain
    -- proof-carrying matchers whose dependent `isType` binders `grind` fails to internalize.
    clear hpattern hInterp'
    grind
  -- Expose the result type as a plain attribute `resTy`, both in the interpretation and in the
  -- pattern's guards.
  split at hInterp'
  case h_2 => simp at hInterp'
  case h_1 resTy resTyIsTy hTyList =>
  have hTy : ((op.getResult 0).get! ctx.raw).type = ⟨resTy, resTyIsTy⟩ := by simpa using hTyList
  rw [hTy] at hpattern
  -- Case on the interpreter's `bitcast` arm: this pins the operand value and the result type
  -- together, and the last case (no arm matches) is immediate.
  split at hInterp'
  case h_8 => simp at hInterp'
  case h_1 =>
    rename_i opBw x resBw resTyIsTy
    -- `int → int`: the result is the operand value itself.
    have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType ⟨opBw⟩ :=
      conforms_int_type (VariableState.getVar?_conforms hgetVar)
    split at hInterp'
    · exact absurd hInterp' (by simp)
    rename_i hBwNe
    obtain rfl : opBw = resBw := by grind
    obtain ⟨rfl, rfl, rfl⟩ :
        resValues = #[RuntimeValue.int opBw x] ∧ mem' = state.memory ∧ cf = none := by
      simp [Interp, pure, bind] at hInterp'; grind
    have hResVal : newState.variables.getVar? (op.getResult 0)
        = some (RuntimeValue.int opBw x) := by
      rw [hNew,
        VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
      simp
    rw [hResults] at hsourceValues
    simp [hResVal] at hsourceValues
    subst sourceValues
    simp only [checkBitcastType, isBitcastByteToPtr, Attribute.bitwidthOfType, hOperandType]
      at hpattern
    rw [if_neg (by simp), if_neg (by simp)] at hpattern
    split at hpattern
    · exact absurd hpattern (by simp)
    rename_i hMem
    peelOpCreation! hpattern ctx₁ opCastOp hCast hDomCtx hDom₁
    peelOpCreation! hpattern ctx₂ castBackOp hCastBack hDom₁ hDom₂
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hgetVar
        hDomCtx hDom₂ vNotOp
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
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₂.raw
        = #[⟨Attribute.integerType ⟨opBw⟩, resTyIsTy⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_castBack_forward (state := s₁) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₁
    have hmem : opBw ∈ [8, 16, 32, 64] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem ⊢; grind
    refine ⟨s₂, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int opBw (RISCV.Reg.toInt (LLVM.Int.toReg xt) opBw)], ?_, ?_⟩
      · simp [hRes₂, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bitcast_isRefinedBy_toInt hmem hxtRef⟩
  case h_2 =>
    rename_i opBw x resBw resTyIsTy
    -- `int → byte`.
    have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType ⟨opBw⟩ :=
      conforms_int_type (VariableState.getVar?_conforms hgetVar)
    split at hInterp'
    · exact absurd hInterp' (by simp)
    rename_i hBwNe
    obtain rfl : opBw = resBw := by grind
    obtain ⟨rfl, rfl, rfl⟩ :
        resValues = #[RuntimeValue.byte opBw (Data.LLVM.Byte.fromInt x)] ∧
          mem' = state.memory ∧ cf = none := by
      simp [Interp, pure, bind] at hInterp'; grind
    have hResVal : newState.variables.getVar? (op.getResult 0)
        = some (RuntimeValue.byte opBw (Data.LLVM.Byte.fromInt x)) := by
      rw [hNew,
        VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
      simp
    rw [hResults] at hsourceValues
    simp [hResVal] at hsourceValues
    subst sourceValues
    simp only [checkBitcastType, isBitcastByteToPtr, Attribute.bitwidthOfType, hOperandType]
      at hpattern
    rw [if_neg (by simp), if_neg (by simp)] at hpattern
    split at hpattern
    · exact absurd hpattern (by simp)
    rename_i hMem
    peelOpCreation! hpattern ctx₁ opCastOp hCast hDomCtx hDom₁
    peelOpCreation! hpattern ctx₂ castBackOp hCastBack hDom₁ hDom₂
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hgetVar
        hDomCtx hDom₂ vNotOp
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
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₂.raw
        = #[⟨Attribute.byteType ⟨opBw⟩, resTyIsTy⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_castBack_byte_forward (state := s₁) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₁
    have hmem : opBw ∈ [8, 16, 32, 64] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem ⊢; grind
    refine ⟨s₂, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.byte opBw (RISCV.Reg.toByte (LLVM.Int.toReg xt) opBw)], ?_, ?_⟩
      · simp [hRes₂, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bitcast_isRefinedBy_intToByte hmem hxtRef⟩
  case h_3 =>
    rename_i opBw x resBw resTyIsTy
    -- `byte → byte`: the result is the operand value itself.
    have hOperandType : (operand.getType! ctx.raw).val = Attribute.byteType ⟨opBw⟩ :=
      conforms_byte_type (VariableState.getVar?_conforms hgetVar)
    split at hInterp'
    · exact absurd hInterp' (by simp)
    rename_i hBwNe
    obtain rfl : opBw = resBw := by grind
    obtain ⟨rfl, rfl, rfl⟩ :
        resValues = #[RuntimeValue.byte opBw x] ∧ mem' = state.memory ∧ cf = none := by
      simp [Interp, pure, bind] at hInterp'; grind
    have hResVal : newState.variables.getVar? (op.getResult 0)
        = some (RuntimeValue.byte opBw x) := by
      rw [hNew,
        VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
      simp
    rw [hResults] at hsourceValues
    simp [hResVal] at hsourceValues
    subst sourceValues
    simp only [checkBitcastType, isBitcastByteToPtr, Attribute.bitwidthOfType, hOperandType]
      at hpattern
    rw [if_neg (by simp), if_neg (by simp)] at hpattern
    split at hpattern
    · exact absurd hpattern (by simp)
    rename_i hMem
    peelOpCreation! hpattern ctx₁ opCastOp hCast hDomCtx hDom₁
    peelOpCreation! hpattern ctx₂ castBackOp hCastBack hDom₁ hDom₂
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_byte_getVar? valueRefinement state'Dom (by grind) hgetVar
        hDomCtx hDom₂ vNotOp
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
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₂.raw
        = #[⟨Attribute.byteType ⟨opBw⟩, resTyIsTy⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_byte_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_castBack_byte_forward (state := s₁) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₁
    have hmem : opBw ∈ [8, 16, 32, 64] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem ⊢; grind
    refine ⟨s₂, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.byte opBw (RISCV.Reg.toByte (LLVM.Byte.toReg xt) opBw)], ?_, ?_⟩
      · simp [hRes₂, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bitcast_isRefinedBy_toByte hmem hxtRef⟩
  case h_4 =>
    rename_i opBw x resBw resTyIsTy
    -- `byte → int`.
    have hOperandType : (operand.getType! ctx.raw).val = Attribute.byteType ⟨opBw⟩ :=
      conforms_byte_type (VariableState.getVar?_conforms hgetVar)
    split at hInterp'
    · exact absurd hInterp' (by simp)
    rename_i hBwNe
    obtain rfl : opBw = resBw := by grind
    obtain ⟨rfl, rfl, rfl⟩ :
        resValues = #[RuntimeValue.int opBw (Data.LLVM.Byte.toInt x)] ∧
          mem' = state.memory ∧ cf = none := by
      simp [Interp, pure, bind] at hInterp'; grind
    have hResVal : newState.variables.getVar? (op.getResult 0)
        = some (RuntimeValue.int opBw (Data.LLVM.Byte.toInt x)) := by
      rw [hNew,
        VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
      simp
    rw [hResults] at hsourceValues
    simp [hResVal] at hsourceValues
    subst sourceValues
    simp only [checkBitcastType, isBitcastByteToPtr, Attribute.bitwidthOfType, hOperandType]
      at hpattern
    rw [if_neg (by simp), if_neg (by simp)] at hpattern
    split at hpattern
    · exact absurd hpattern (by simp)
    rename_i hMem
    peelOpCreation! hpattern ctx₁ opCastOp hCast hDomCtx hDom₁
    peelOpCreation! hpattern ctx₂ castBackOp hCastBack hDom₁ hDom₂
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_byte_getVar? valueRefinement state'Dom (by grind) hgetVar
        hDomCtx hDom₂ vNotOp
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
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₂.raw
        = #[⟨Attribute.integerType ⟨opBw⟩, resTyIsTy⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_byte_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_castBack_forward (state := s₁) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₁
    have hmem : opBw ∈ [8, 16, 32, 64] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem ⊢; grind
    refine ⟨s₂, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int opBw (RISCV.Reg.toInt (LLVM.Byte.toReg xt) opBw)], ?_, ?_⟩
      · simp [hRes₂, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bitcast_isRefinedBy_byteToInt hmem hxtRef⟩
  case h_5 =>
    rename_i opBw x pt resTyIsTy
    -- `byte → ptr` is excluded from the pattern, so it never fires.
    have hOperandType : (operand.getType! ctx.raw).val = Attribute.byteType ⟨opBw⟩ :=
      conforms_byte_type (VariableState.getVar?_conforms hgetVar)
    simp [checkBitcastType, isBitcastByteToPtr, hOperandType] at hpattern
  case h_6 =>
    rename_i a pt resTyIsTy
    -- `ptr → ptr`: the result is the operand value itself.
    obtain ⟨opPt, hOperandType⟩ := conforms_addr_type (VariableState.getVar?_conforms hgetVar)
    obtain ⟨rfl, rfl, rfl⟩ :
        resValues = #[RuntimeValue.addr a] ∧ mem' = state.memory ∧ cf = none := by
      simp [Interp, pure, bind] at hInterp'; grind
    have hResVal : newState.variables.getVar? (op.getResult 0)
        = some (RuntimeValue.addr a) := by
      rw [hNew,
        VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
      simp
    rw [hResults] at hsourceValues
    simp [hResVal] at hsourceValues
    subst sourceValues
    simp only [checkBitcastType, isBitcastByteToPtr, Attribute.bitwidthOfType, hOperandType]
      at hpattern
    rw [if_neg (by simp), if_neg (by simp)] at hpattern
    split at hpattern
    · exact absurd hpattern (by simp)
    rename_i hMem
    peelOpCreation! hpattern ctx₁ opCastOp hCast hDomCtx hDom₁
    peelOpCreation! hpattern ctx₂ castBackOp hCastBack hDom₁ hDom₂
    cleanupHpattern hpattern
    have hOpVal' :=
      LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom (by grind) hgetVar
        hDomCtx hDom₂ vNotOp
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
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₂.raw
        = #[⟨Attribute.llvmPointerType pt, resTyIsTy⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castAddrToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_castBack_ptr_forward (state := s₁) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₁
    refine ⟨s₂, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.addr a], ?_, ?_⟩
      · simp [hRes₂, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr (by simp [RuntimeValue.isRefinedBy])
  case h_7 =>
    rename_i a resBw resTyIsTy
    -- `ptr → byte`, only at width 64.
    obtain ⟨opPt, hOperandType⟩ := conforms_addr_type (VariableState.getVar?_conforms hgetVar)
    split at hInterp'
    case isFalse => exact absurd hInterp' (by simp)
    rename_i hBw
    subst hBw
    obtain ⟨rfl, rfl, rfl⟩ :
        resValues = #[RuntimeValue.byte 64 (Data.LLVM.Byte.fromUInt64 a)] ∧
          mem' = state.memory ∧ cf = none := by
      simp only [Interp, pure, bind, Option.some.injEq, UBOr.ok.injEq,
        Prod.mk.injEq] at hInterp'
      grind
    have hResVal : newState.variables.getVar? (op.getResult 0)
        = some (RuntimeValue.byte 64 (Data.LLVM.Byte.fromUInt64 a)) := by
      rw [hNew,
        VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
      simp
    rw [hResults] at hsourceValues
    simp [hResVal] at hsourceValues
    subst sourceValues
    simp only [checkBitcastType, isBitcastByteToPtr, Attribute.bitwidthOfType, hOperandType]
      at hpattern
    rw [if_neg (by simp), if_neg (by simp)] at hpattern
    split at hpattern
    · exact absurd hpattern (by simp)
    rename_i hMem
    peelOpCreation! hpattern ctx₁ opCastOp hCast hDomCtx hDom₁
    peelOpCreation! hpattern ctx₂ castBackOp hCastBack hDom₁ hDom₂
    cleanupHpattern hpattern
    have hOpVal' :=
      LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom (by grind) hgetVar
        hDomCtx hDom₂ vNotOp
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
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₂.raw
        = #[⟨Attribute.byteType ⟨64⟩, resTyIsTy⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castAddrToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_castBack_byte_forward (state := s₁) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₁
    refine ⟨s₂, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.byte 64 (RISCV.Reg.toByte ⟨BitVec.ofNat 64 a.toNat⟩ 64)], ?_, ?_⟩
      · simp [hRes₂, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bitcast_isRefinedBy_addrToByte a⟩

/--
info: 'Veir.bitcast_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominates_refl,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 bitcast_isRefinedBy_addrToByte._native.bv_decide.ax_1_8,
 bitcast_isRefinedBy_byteToInt._native.bv_decide.ax_1_10,
 bitcast_isRefinedBy_byteToInt._native.bv_decide.ax_1_15,
 bitcast_isRefinedBy_byteToInt._native.bv_decide.ax_1_20,
 bitcast_isRefinedBy_byteToInt._native.bv_decide.ax_1_25,
 bitcast_isRefinedBy_intToByte._native.bv_decide.ax_1_17,
 bitcast_isRefinedBy_intToByte._native.bv_decide.ax_1_22,
 bitcast_isRefinedBy_intToByte._native.bv_decide.ax_1_27,
 bitcast_isRefinedBy_intToByte._native.bv_decide.ax_1_32,
 bitcast_isRefinedBy_toByte._native.bv_decide.ax_1_14,
 bitcast_isRefinedBy_toByte._native.bv_decide.ax_1_19,
 bitcast_isRefinedBy_toByte._native.bv_decide.ax_1_24,
 bitcast_isRefinedBy_toByte._native.bv_decide.ax_1_9,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms bitcast_local_preservesSemantics

end Veir
