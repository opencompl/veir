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
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm

namespace Veir

theorem setWidth_ofInt_6_64' (c : Int) :
    BitVec.setWidth 6 (BitVec.ofInt 64 c) = BitVec.ofInt 6 c := by
  rw [← BitVec.toNat_inj]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]; omega

/-- Correctness of `riscv.bexti` for `and (lshr x sh) 1` on `i64` (single-bit extract). -/
theorem bexti_isRefinedBy {exact : Bool} {x xt : Data.LLVM.Int 64} (sh : Int)
    (_hlo : 0 ≤ sh) (_hhi : sh ≤ 63) (h : x ⊒ xt) :
    Data.LLVM.Int.and (Data.LLVM.Int.lshr x (Data.LLVM.Int.constant 64 sh) exact)
        (Data.LLVM.Int.constant 64 1)
      ⊒ RISCV.Reg.toInt (Data.RISCV.bexti (BitVec.ofInt 6 sh) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.bexti, ← setWidth_ofInt_6_64' sh]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 sh = v
  revert h
  veir_bv_decide

set_option maxHeartbeats 1000000 in
/-- Graph lemma for the `and`'s left operand `lhs`, which is defined by an `lshr` with a constant
    shift amount `sh`: in a source state satisfying `EquationLemmaAt` before `op`, `lhs`'s runtime
    value is `lshr xv (constant sh)`, and the shifted value `x`'s facts (value, type, dominance,
    in-bounds, not-a-result) are recovered. The `lshr` analogue of `matchNot_getVar?…`, but the
    inner op verifies as `LLVMShift`, so the operand-width equality is recovered dynamically via
    `matchShiftOp_interpretOp_unfold`. -/
theorem lshrConst_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {lhs x shamt : ValuePtr} {shrOp : OperationPtr}
    {shProps : propertiesOf (.llvm .lshr)} {shAttr : IntegerAttr} {intType : IntegerType}
    (hDef : getDefiningOp lhs ctx.raw = some shrOp)
    (hLshr : matchLshr shrOp ctx.raw = some (x, shamt, shProps))
    (hShConst : matchConstantIntVal shamt ctx.raw = some shAttr)
    (hOperand : lhs ∈ op.getOperands! ctx.raw)
    (hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ xv, state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? lhs = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.lshr xv (Data.LLVM.Int.constant intType.bitwidth shAttr.value) shProps.exact)) ∧
      (x.getType! ctx.raw).val = Attribute.integerType intType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
  -- Syntactic facts from the matches.
  obtain ⟨lhsPtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hShrType, hShrNumResults, hShrOperands, hShProps⟩ := matchLshr_implies hLshr
  obtain ⟨shamtPtr, rfl, hShamtOp⟩ := matchConstantIntVal_implies hShConst
  obtain ⟨hShamtType, hShamtProps⟩ := matchConstantIntOp_implies hShamtOp
  have hLhsIn : (ValuePtr.opResult lhsPtr).InBounds ctx.raw := by grind
  have hShrOpIn : lhsPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hlhsIdx : lhsPtr.index < lhsPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hlhsEq : lhsPtr = lhsPtr.op.getResult 0 := by
    have hidx : lhsPtr.index = 0 := by omega
    cases lhsPtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  -- The `lshr` verifies as `LLVMShift`.
  have hShrVerified : lhsPtr.op.Verified ctx hShrOpIn := by grind
  obtain ⟨-, -, hShrResEqOp0, intType2, hShrOp1Type⟩ :=
    OperationPtr.Verified.llvm_lshr hShrVerified hShrType
  have hVTypeEq : (ValuePtr.opResult lhsPtr).getType! ctx.raw
      = ((lhsPtr.op.getResult 0).get! ctx.raw).type := by rw [hlhsEq]; rfl
  -- `x` (operand 0) shares `lhs`'s type `intType`; `shamt` (operand 1) has type `intType2`.
  have hxIdxEq : x = (lhsPtr.op.getOperands! ctx.raw)[0]! := by rw [hShrOperands]; rfl
  have hShamtIdxEq : ValuePtr.opResult shamtPtr = (lhsPtr.op.getOperands! ctx.raw)[1]! := by
    rw [hShrOperands]; rfl
  have hShrOperand0 : lhsPtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hShrOperand1 : lhsPtr.op.getOperand! ctx.raw 1 = ValuePtr.opResult shamtPtr := by
    rw [hShamtIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType intType := by
    have : ((lhsPtr.op.getResult 0).get! ctx.raw).type.val
        = ((lhsPtr.op.getOperand! ctx.raw 0).getType! ctx.raw).val := hShrResEqOp0
    rw [hShrOperand0] at this
    rw [← this, ← hVTypeEq]; exact hLhsType
  have hShamtValType : ((ValuePtr.opResult shamtPtr).getType! ctx.raw).val
      = Attribute.integerType intType2 := by rw [← hShrOperand1, hShrOp1Type]
  -- Dominance: the `lshr` strictly dominates `op`.
  have hShrDefines : (ValuePtr.opResult lhsPtr).getDefiningOp! ctx.raw = some lhsPtr.op := by
    have hOwner := (ctx.wellFormed.operations lhsPtr.op hShrOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hShrSDom : lhsPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hShrDefines hOperand
  have hShrDomIp : lhsPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hShrPure : lhsPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_lshr hShrType
  obtain ⟨cfS, hInterpShr⟩ := stateWf lhsPtr.op hShrOpIn hShrPure hShrDomIp
  -- Unfold the `lshr`'s interpretation (recovers the width equality `h'`).
  obtain ⟨xv, sv, h', hxVal, hsVal, -, hShrResVal, -⟩ :=
    matchShiftOp_interpretOp_unfold (srcOp := .lshr)
      (shiftFn := fun a b props => Data.LLVM.Int.lshr a b props.exact)
      (props := lhsPtr.op.getProperties! ctx.raw (.llvm .lshr))
      hShrOpIn hShrType hShrNumResults hShrOperands rfl
      (by intro bw bw' a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp'] at hh
          split at hh
          · exact absurd hh (by simp)
          · rename_i hbw; obtain rfl : bw' = bw := by omega
            refine ⟨rfl, ?_⟩
            simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hh
            grind)
      hInterpShr hxType hShamtValType
  -- The `shamt` constant's structural facts.
  have hShamtIn : (ValuePtr.opResult shamtPtr).InBounds ctx.raw := by
    grind [OperationPtr.getOperands!]
  have hShamtOpIn : shamtPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hShamtVerified : shamtPtr.op.Verified ctx hShamtOpIn := by grind
  obtain ⟨hShamtNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hShamtVerified hShamtType
  have hShamtIdx : shamtPtr.index < shamtPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hShamtEq : shamtPtr = shamtPtr.op.getResult 0 := by
    have hidx : shamtPtr.index = 0 := by omega
    cases shamtPtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hShamtResType : ((shamtPtr.op.getResult 0).get! ctx.raw).type
      = ⟨.integerType intType2, by grind⟩ := by
    have heq : ((ValuePtr.opResult shamtPtr).getType! ctx.raw)
        = ((shamtPtr.op.getResult 0).get! ctx.raw).type := by rw [hShamtEq]; rfl
    apply Subtype.ext; rw [← heq]; exact hShamtValType
  have hShamtDefines : (ValuePtr.opResult shamtPtr).getDefiningOp! ctx.raw = some shamtPtr.op := by
    have hOwner := (ctx.wellFormed.operations shamtPtr.op hShamtOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hShamtSDomShr : shamtPtr.op.strictlyDominates lhsPtr.op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hShamtDefines (by grind [OperationPtr.getOperands!])
  have hShamtSDom : shamtPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hShamtSDomShr hShrSDom
  have hShamtDomIp : shamtPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hShamtPure : shamtPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hShamtType
  obtain ⟨cfC, hInterpShamt⟩ := stateWf shamtPtr.op hShamtOpIn hShamtPure hShamtDomIp
  have hShamtResVal :=
    constantOp_interpretOp_unfold hShamtOpIn hShamtType hShamtNumResults hShamtProps hShamtResType
      hInterpShamt
  have hsvEq : sv = Data.LLVM.Int.constant intType2.bitwidth shAttr.value := by
    rw [hShamtEq] at hsVal; grind
  -- Normalise the width equality: substitute `intType2.bitwidth = intType.bitwidth`.
  subst hsvEq
  obtain ⟨w⟩ := intType; obtain ⟨w2⟩ := intType2
  simp only at h' hxType hxVal ⊢; subst w2
  refine ⟨xv, hxVal, ?_, hxType, ?_, ?_, ?_⟩
  · rw [hShProps, hlhsEq]; exact hShrResVal
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hShrOpIn (by grind [OperationPtr.getOperands!])) hShrSDom
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hShrSDom) x
      (by grind [OperationPtr.getOperands!])

set_option maxHeartbeats 1000000 in
theorem bexti_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps bexti_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges bexti_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds bexti_local}
    {h₄ : LocalRewritePattern.ReturnValues bexti_local} :
    LocalRewritePattern.PreservesSemantics bexti_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, bexti_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel `matchAnd`.
  have hMatchSome : (matchAnd op ctx.raw).isSome := by
    cases hM : matchAnd op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, andProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨hOpType, hNumResults, hOperands, -⟩ := matchAnd_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_and opVerif hOpType
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Width guard `intType.bitwidth = 64`.
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hW64
  -- `rhs` is the constant `1`.
  have hOneSome : (matchConstantIntVal rhs ctx.raw).isSome := by
    cases hM : matchConstantIntVal rhs ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨one, hOneMatch⟩ := Option.isSome_iff_exists.mp hOneSome
  rw [hOneMatch] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hOneVal
  -- `lhs` is defined by an `lshr` with a constant shift.
  have hDefSome : (getDefiningOp lhs ctx.raw).isSome := by
    cases hM : getDefiningOp lhs ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨shrOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hLshrSome : (matchLshr shrOp ctx.raw).isSome := by
    cases hM : matchLshr shrOp ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, shamt, shProps⟩, hLshr⟩ := Option.isSome_iff_exists.mp hLshrSome
  rw [hLshr] at hpattern
  simp only [] at hpattern
  have hShSome : (matchConstantIntVal shamt ctx.raw).isSome := by
    cases hM : matchConstantIntVal shamt ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨shAttr, hShMatch⟩ := Option.isSome_iff_exists.mp hShSome
  rw [hShMatch] at hpattern
  simp only [] at hpattern
  -- Shift-amount range guard.
  split at hpattern
  case isTrue hrange => simp at hpattern
  rename_i hRange
  obtain ⟨hShLo, hShHi⟩ : 0 ≤ shAttr.value ∧ shAttr.value ≤ 63 := by omega
  -- Unfold the `and` interpretation.
  obtain ⟨lhsv, rhsv, hlhsVal, hrhsVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcFn := fun a b _ => Data.LLVM.Int.and a b)
      (props := op.getProperties! ctx.raw (.llvm .and))
      opInBounds hOpType hNumResults hOperands rfl
      (fun bw a b props resultTypes blockOperands mem res hh => by
        simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh; grind)
      hinterp hLhsType hRhsType
  subst hCf
  -- Pin `rhs`'s value to the constant `1`, and `lhs`'s value to `lshr x sh`.
  have hrhsConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hOneMatch (by rw [hOperands]; simp) hRhsType
  obtain rfl : rhsv = Data.LLVM.Int.constant intType.bitwidth one.value := by
    have := hrhsVal.symm.trans hrhsConst; simpa using this
  obtain ⟨xv, hxVal, hlhsConst, hxType, hxDom, hxIn, hxNotRes⟩ :=
    lshrConst_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hLshr hShMatch
      (by rw [hOperands]; simp) hLhsType
  obtain rfl : lhsv = Data.LLVM.Int.lshr xv (Data.LLVM.Int.constant intType.bitwidth shAttr.value)
      shProps.exact := by
    have := hlhsVal.symm.trans hlhsConst; simpa using this
  -- Source value: `op`'s result is `and (lshr x sh) 1`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the three creations (cast `x`, `bexti`, cast back).
  peelCastToRegLocal hpattern ctx₁ xCastOp hXCast hxDom hxDom₁
  peelOpCreation! hpattern ctx₂ bextiOp hBexti hxDom₁ hxDom₂
  peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hxDom₂ hxDom₃
  cleanupHpattern hpattern
  obtain ⟨xt, hXVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hxDom hxDom₃ hxNotRes
  obtain ⟨bw⟩ := intType; simp only at hW64 hxVal hlhsVal hRes hResType ⊢; subst bw
  have hXCastType : xCastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hBextiType : bextiOp.getOpType! ctx₃.raw = .riscv .bexti := by grind
  have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hXCastOperands : xCastOp.getOperands! ctx₃.raw = #[x] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hXCast (operation := xCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hBexti (operation := xCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xCastOp)]
  have hBextiOperands : bextiOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (xCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hBexti (operation := bextiOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := bextiOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (bextiOp.getResult 0)] := by grind
  have hBextiProps : bextiOp.getProperties! ctx₃.raw (.riscv .bexti)
      = RISCVImmediateProperties.mk (IntegerAttr.mk shAttr.value (IntegerType.mk 64)) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hBexti (operation := bextiOp)]
  have hCBType : ((op.getResult 0).get! ctx₂.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hBexti (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hXCast (value := ValuePtr.opResult (op.getResult 0))]
    rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
    rw [h1]; exact hResType
  have hXCastResTypes : xCastOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hXCast (operation := xCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hBexti (operation := xCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xCastOp)]
  have hBextiResTypes : bextiOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hBexti (operation := bextiOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := bextiOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hXCastType hXCastOperands hXCastResTypes hXVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := Data.RISCV.bexti (BitVec.ofInt 6 shAttr.value) (LLVM.Int.toReg xt))
      (fun rt bo mem => rfl)
      hBextiType hBextiProps hBextiOperands hBextiResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64
        (RISCV.Reg.toInt (Data.RISCV.bexti (BitVec.ofInt 6 shAttr.value) (LLVM.Int.toReg xt)) 64)],
        ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
      have := bexti_isRefinedBy (exact := shProps.exact) shAttr.value hShLo hShHi hxtRef
      rw [hOneVal]
      simpa using this

/--
info: 'Veir.bexti_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 OperationPtr.strictlyDominates_trans,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 ValuePtr.dominatesIp_before_of_strictlyDominates,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 bexti_isRefinedBy._native.bv_decide.ax_1_6,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms bexti_local_preservesSemantics

end Veir
