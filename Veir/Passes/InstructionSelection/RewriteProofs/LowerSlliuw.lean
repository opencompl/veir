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
import Veir.Passes.InstructionSelection.RewriteProofs.LowerExt
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm

namespace Veir

theorem setWidth_ofInt_6_64'' (c : Int) :
    BitVec.setWidth 6 (BitVec.ofInt 64 c) = BitVec.ofInt 6 c := by
  rw [← BitVec.toNat_inj]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]; omega

/-- Correctness of `riscv.slliuw` for `shl (zext x) sh` on `i64` with a 32→64 zext and a constant
    shift `sh ∈ [0, 31]` (zero-extend the low word, then shift left). -/
theorem slliuw_isRefinedBy {nneg nsw nuw : Bool} {hw : (32 : Nat) < 64}
    {x xt : Data.LLVM.Int 32} (sh : Int) (_hlo : 0 ≤ sh) (_hhi : sh ≤ 31) (h : x ⊒ xt) :
    Data.LLVM.Int.shl (Data.LLVM.Int.zext x 64 nneg hw) (Data.LLVM.Int.constant 64 sh) nsw nuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.slliuw (BitVec.ofInt 6 sh) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.slliuw, ← setWidth_ofInt_6_64'' sh]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 sh = v
  revert h
  veir_bv_decide

/-- `llvm.zext` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_zext {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .zext) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

set_option maxHeartbeats 1000000 in
/-- Graph lemma for the `shl`'s base operand `base`, which is defined by a `zext`: in a source state
    satisfying `EquationLemmaAt` before `op`, `base`'s runtime value is `zext xv`, and the extended
    value `x`'s facts are recovered. The `zext` (unary, width-crossing) analogue of the `lshr` graph
    lemma; uses `matchExtOp_interpretOp_unfold`. -/
theorem zext_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x : ValuePtr} {zextOp : OperationPtr} {zProps : propertiesOf (.llvm .zext)}
    {retType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some zextOp)
    (hZext : matchZext zextOp ctx.raw = some (x, zProps))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType retType) :
    ∃ (opType : IntegerType) (hw : opType.bitwidth < retType.bitwidth)
      (xv : Data.LLVM.Int opType.bitwidth),
      state.variables.getVar? x = some (RuntimeValue.int opType.bitwidth xv) ∧
      state.variables.getVar? base = some (RuntimeValue.int retType.bitwidth
        (Data.LLVM.Int.zext xv retType.bitwidth zProps.nneg hw)) ∧
      (x.getType! ctx.raw).val = Attribute.integerType opType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
  obtain ⟨basePtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hZextType, hZextNumResults, hZextOperands, hZProps⟩ := matchZext_implies hZext
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hZextOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hbaseIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hbaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hZextVerified : basePtr.op.Verified ctx hZextOpIn := by grind
  obtain ⟨-, -, -, -, opType, retType', hxTypeV, hBaseResTypeV, hwV⟩ :=
    OperationPtr.Verified.llvm_zext hZextVerified hZextType
  -- `base`'s type (`retType`) is the `zext`'s result type (`retType'`).
  have hVTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hbaseEq]; rfl
  have hRetEq : retType = retType' := by
    have h := hBaseResTypeV
    rw [← hVTypeEq] at h
    rw [hbaseEq] at hBaseType
    grind
  subst hRetEq
  have hxIdxEq : x = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hZextOperands]; rfl
  have hZextOperand0 : basePtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType opType := by
    have := hxTypeV; rw [hZextOperand0] at this; rw [this]
  have hResTypes : basePtr.op.getResultTypes! ctx.raw
      = #[⟨Attribute.integerType retType, by grind⟩] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hZextNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hZextNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := basePtr.op) (ctx := ctx.raw)
        (index := 0) (by omega)
      grind
  -- Dominance and interpretation of the `zext`.
  have hZextDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hZextOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hZextSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hZextDefines hOperand
  have hZextDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hZextPure : basePtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_zext hZextType
  obtain ⟨cfZ, hInterpZext⟩ := stateWf basePtr.op hZextOpIn hZextPure hZextDomIp
  obtain ⟨xv, hxVal, -, hBaseResVal, -⟩ :=
    matchExtOp_interpretOp_unfold (srcOp := .zext)
      (srcFn := fun a hw props => Data.LLVM.Int.zext a _ props.nneg hw)
      (props := basePtr.op.getProperties! ctx.raw (.llvm .zext))
      hZextOpIn hZextType hZextNumResults hZextOperands rfl hResTypes hwV zext_interpretOp'
      hInterpZext hxType
  refine ⟨opType, hwV, xv, hxVal, ?_, hxType, ?_, ?_, ?_⟩
  · rw [hbaseEq, hBaseResVal, ← hZProps]
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hZextOpIn (by grind [OperationPtr.getOperands!])) hZextSDom
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hZextSDom) x
      (by grind [OperationPtr.getOperands!])

set_option maxHeartbeats 1000000 in
theorem slliuw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps slliuw_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges slliuw_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds slliuw_local}
    {h₄ : LocalRewritePattern.ReturnValues slliuw_local} :
    LocalRewritePattern.PreservesSemantics slliuw_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, slliuw_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel `matchShl`.
  have hMatchSome : (matchShl op ctx.raw).isSome := by
    cases hM : matchShl op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨base, shamt, shlProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨hOpType, hNumResults, hOperands, hShlPropsEq⟩ := matchShl_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨hNRes, hNOper, hResEqOp0, intType2, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_shl opVerif hOpType
  have hBaseEq : base = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hShamtEq : shamt = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = base := by
    rw [hBaseEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = shamt := by
    rw [hShamtEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- Result type must be integer for the pattern to fire; `base` shares it.
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  have hBaseType : (base.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, ← hResEqOp0, hResType]
  have hShamtType : (shamt.getType! ctx.raw).val = Attribute.integerType intType2 := by
    rw [← hOperand1, hOp1Type]
  rw [hResType] at hpattern
  simp only [] at hpattern
  -- Width guard `intType.bitwidth = 64`.
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hW64
  -- `shamt` is a constant in `[0, 31]`.
  have hShSome : (matchConstantIntVal shamt ctx.raw).isSome := by
    cases hM : matchConstantIntVal shamt ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨shAttr, hShMatch⟩ := Option.isSome_iff_exists.mp hShSome
  rw [hShMatch] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue hrange => simp at hpattern
  rename_i hRange
  obtain ⟨hShLo, hShHi⟩ : 0 ≤ shAttr.value ∧ shAttr.value ≤ 31 := by omega
  -- `base` is defined by a `zext`.
  have hDefSome : (getDefiningOp base ctx.raw).isSome := by
    cases hM : getDefiningOp base ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨baseOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hZextSome : (matchZext baseOp ctx.raw).isSome := by
    cases hM : matchZext baseOp ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, zProps⟩, hZext⟩ := Option.isSome_iff_exists.mp hZextSome
  rw [hZext] at hpattern
  simp only [] at hpattern
  -- Pin `base = zext x`, recovering `x`'s facts (in particular its width `opType`).
  obtain ⟨opType, hw, xv, hxVal, hbaseConst, hxType, hxDom, hxIn, hxNotRes⟩ :=
    zext_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hZext
      (by rw [hOperands]; simp) hBaseType
  -- Source-width guard on `x` (`i32`).
  rw [hxType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hSrc32
  -- Unfold the `shl` interpretation.
  obtain ⟨basev, shamtv, h', hbaseVal, hshamtVal, hMem, hRes, hCf⟩ :=
    matchShiftOp_interpretOp_unfold (srcOp := .shl)
      (shiftFn := fun a b props => Data.LLVM.Int.shl a b props.nsw props.nuw)
      (props := op.getProperties! ctx.raw (.llvm .shl))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw bw' a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp'] at hh
          split at hh
          · exact absurd hh (by simp)
          · rename_i hbw; obtain rfl : bw' = bw := by omega
            refine ⟨rfl, ?_⟩
            simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hh
            grind)
      hinterp hBaseType hShamtType
  subst hCf
  -- Pin `shamt = const sh`.
  have hShamtConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hShMatch (by rw [hOperands]; simp) hShamtType
  obtain rfl : shamtv = Data.LLVM.Int.constant intType2.bitwidth shAttr.value := by
    have := hshamtVal.symm.trans hShamtConst; simpa using this
  -- `base`'s two values agree, pinning `basev = zext xv`.
  obtain rfl : basev = Data.LLVM.Int.zext xv intType.bitwidth zProps.nneg hw := by
    have := hbaseVal.symm.trans hbaseConst; simpa using this
  -- Normalise widths: `intType2.bitwidth = intType.bitwidth = 64`, `opType.bitwidth = 32`.
  obtain ⟨w⟩ := intType; obtain ⟨w2⟩ := intType2; obtain ⟨ws⟩ := opType
  simp only at hW64 h' hSrc32 hxVal hxType hbaseVal hRes hResType hw ⊢
  subst w2; subst w; subst ws
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the three creations (cast `x`, `slliuw`, cast back).
  peelCastToRegLocal hpattern ctx₁ xCastOp hXCast hxDom hxDom₁
  peelOpCreation! hpattern ctx₂ slliuwOp hSlliuw hxDom₁ hxDom₂
  peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hxDom₂ hxDom₃
  cleanupHpattern hpattern
  obtain ⟨xt, hXVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hxDom hxDom₃ hxNotRes
  have hXCastType : xCastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hSlliuwType : slliuwOp.getOpType! ctx₃.raw = .riscv .slliuw := by grind
  have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hXCastOperands : xCastOp.getOperands! ctx₃.raw = #[x] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hXCast (operation := xCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSlliuw (operation := xCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xCastOp)]
  have hSlliuwOperands : slliuwOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (xCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSlliuw (operation := slliuwOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := slliuwOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (slliuwOp.getResult 0)] := by grind
  have hSlliuwProps : slliuwOp.getProperties! ctx₃.raw (.riscv .slliuw)
      = RISCVImmediateProperties.mk (IntegerAttr.mk shAttr.value (IntegerType.mk 64)) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSlliuw (operation := slliuwOp)]
  have hCBType : ((op.getResult 0).get! ctx₂.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hSlliuw (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hXCast (value := ValuePtr.opResult (op.getResult 0))]
    rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
    rw [h1]; exact Subtype.ext hResType
  have hXCastResTypes : xCastOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hXCast (operation := xCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSlliuw (operation := xCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xCastOp)]
  have hSlliuwResTypes : slliuwOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSlliuw (operation := slliuwOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := slliuwOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hXCastType hXCastOperands hXCastResTypes hXVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := Data.RISCV.slliuw (BitVec.ofInt 6 shAttr.value) (LLVM.Int.toReg xt))
      (fun rt bo mem => rfl)
      hSlliuwType hSlliuwProps hSlliuwOperands hSlliuwResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64
        (RISCV.Reg.toInt (Data.RISCV.slliuw (BitVec.ofInt 6 shAttr.value) (LLVM.Int.toReg xt)) 64)],
        ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
      have := slliuw_isRefinedBy (nsw := shlProps.nsw) (nuw := shlProps.nuw)
        (nneg := zProps.nneg) (hw := hw) shAttr.value hShLo hShHi hxtRef
      rw [hShlPropsEq] at this
      simpa using this

/--
info: 'Veir.slliuw_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 ValuePtr.dominatesIp_before_of_strictlyDominates,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 slliuw_isRefinedBy._native.bv_decide.ax_1_6,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms slliuw_local_preservesSemantics

end Veir
