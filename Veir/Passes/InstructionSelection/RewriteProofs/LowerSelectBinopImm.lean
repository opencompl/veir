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

end Veir
