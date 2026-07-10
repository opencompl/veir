import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.Casting
import Veir.Passes.InstructionSelection.Proofs
import Veir.Passes.InstructionSelection.RISCV64Sdag
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelect
-- Imported for their pre-generated match-congruence auxiliaries (`selectBinopImmLocal.match_1.…`
-- and `lowerBinopNotLocal.match_1.…`); without these the aggregator hits a duplicate-generation
-- clash. See `LowerSelectBinopImm` / `LowerRoliw` for the same pattern.
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRoriw
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm

namespace Veir

/-!
## Generic correctness of `selectSingleBitLocal`

`selectSingleBitLocal match? dst h complement` lowers `OP x (const)` on `i64`, where the constant
(or, for `bclri`, its complement) is a single set bit, to the Zbs single-bit-immediate op emitting
the *bit index*: `unrealized_conversion_cast x → dst (bit index) → unrealized_conversion_cast`.
Instances: `bseti` (`or`), `binvi` (`xor`), `bclri` (`and`, `complement = true`).

Same `castToReg → imm-op → castBack` shape as `selectBinopImmLocal`, but the emitted immediate is
the *bit index* `n` recovered from `singleSetBit`, not the constant itself. The core new ingredient
is `singleSetBit_bridge`: a successful `singleSetBit y = some n` means `y = 1 <<< n`, proved by
extracting the "power of two" fact (`eq_two_pow_log2`) from the `y &&& (y-1) = 0` guard.
-/

/-- `m`'s top bit (bit `k`) is set whenever `2^k ≤ m < 2^(k+1)`. -/
private theorem two_pow_top_bit (m k : Nat) (h1 : 2 ^ k ≤ m) (h2 : m < 2 ^ (k + 1)) :
    m.testBit k = true := by
  have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hd : m / 2 ^ k = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]

/-- A nonzero `u` with its lowest set bit equal to its only set bit (`u &&& (u-1) = 0`) is exactly
    `2 ^ log2 u`. If `u > 2^log2 u` then bit `log2 u` is set in both `u` and `u-1` (both lie in
    `[2^log2 u, 2^(log2 u + 1))`), so `u &&& (u-1) ≠ 0`. -/
theorem eq_two_pow_log2 (u : Nat) (h0 : u ≠ 0) (h1 : u &&& (u - 1) = 0) :
    u = 2 ^ (Nat.log2 u) := by
  have hlo : 2 ^ (Nat.log2 u) ≤ u := by
    rcases Nat.lt_or_ge u (2 ^ (Nat.log2 u)) with hc | hc
    · have := (Nat.log2_lt h0 (k := Nat.log2 u)).mpr hc; omega
    · exact hc
  have hhi : u < 2 ^ (Nat.log2 u + 1) := Nat.lt_log2_self
  rcases Nat.lt_or_ge (2 ^ (Nat.log2 u)) u with hgt | hle
  · exfalso
    have hb1 := two_pow_top_bit u (Nat.log2 u) hlo hhi
    have hb2 := two_pow_top_bit (u - 1) (Nat.log2 u) (by omega) (by omega)
    have hcon := congrArg (fun z => z.testBit (Nat.log2 u)) h1
    simp [Nat.testBit_and, hb1, hb2] at hcon
  · omega

/-- A successful single-set-bit match `singleSetBit y = some n` means `y` is the single bit `1 <<< n`
    (the RISC-V single-bit immediate ops shift `1` by the emitted index `n`). -/
theorem singleSetBit_bridge (y : BitVec 64) (n : Int) (h : singleSetBit y = some n) :
    y = 1#64 <<< BitVec.ofInt 6 n := by
  have hfacts : y.toNat ≠ 0 ∧ y.toNat &&& (y.toNat - 1) = 0 ∧ n = (Nat.log2 y.toNat : Int) := by
    unfold singleSetBit at h
    generalize y.toNat = u at h ⊢
    dsimp only at h
    split at h
    · nomatch h
    · rename_i hcond
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        bne_eq_false_iff_eq] at hcond
      rw [Option.some.injEq] at h
      exact ⟨hcond.1, hcond.2, h.symm⟩
  obtain ⟨hne, hand, hn⟩ := hfacts
  have hu : y.toNat = 2 ^ (Nat.log2 y.toNat) := eq_two_pow_log2 y.toNat hne hand
  have hlt : Nat.log2 y.toNat < 64 := by
    have hb : 2 ^ (Nat.log2 y.toNat) < 2 ^ 64 := by rw [← hu]; exact y.isLt
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp hb
  apply BitVec.eq_of_toNat_eq
  subst hn
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  have hsh : (BitVec.ofInt 6 (Nat.log2 y.toNat : Int)).toNat = Nat.log2 y.toNat := by
    rw [BitVec.toNat_ofInt]; omega
  rw [hsh, Nat.shiftLeft_eq]
  have hup : 2 ^ (Nat.log2 y.toNat) < 2 ^ 64 := by rw [← hu]; exact y.isLt
  have h1t : (1#64 : BitVec 64).toNat = 1 := by decide
  rw [h1t, Nat.one_mul, Nat.mod_eq_of_lt hup]
  exact hu

set_option maxHeartbeats 1600000 in
/-- Shared correctness proof for every `selectSingleBitLocal` lowering. Per-lowering inputs mirror
    `selectBinopImmLocal_preservesSemantics`, except `hRefine` receives the `singleSetBit` fact
    linking the constant `c` to the emitted bit index `n`. -/
theorem selectSingleBitLocal_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode →
      Option (ValuePtr × ValuePtr × propertiesOf (.llvm srcOp))}
    {dst : Riscv} {hdst : Riscv.propertiesOf dst = RISCVImmediateProperties}
    {complement : Bool}
    {resFn : Int → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props},
        match? op ctx = some (lhs, rhs, props) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[lhs, rhs] ∧
        props = op.getProperties! ctx (.llvm srcOp))
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
    (hSemR : ∀ (n : Int) (r : Data.RISCV.Reg)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' dst
            (cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk n (IntegerType.mk 64))))
            resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (resFn n r)], mem, none)))
    (hRefine : ∀ (x xt : Data.LLVM.Int 64) (c n : Int) (props : propertiesOf (.llvm srcOp)),
        singleSetBit (if complement then ~~~ BitVec.ofInt 64 c else BitVec.ofInt 64 c) = some n →
        x ⊒ xt →
        srcFn x (Data.LLVM.Int.constant 64 c) props
          ⊒ RISCV.Reg.toInt (resFn n (LLVM.Int.toReg xt)) 64)
    {h : LocalRewritePattern.ReturnOps (selectSingleBitLocal match? dst hdst complement)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectSingleBitLocal match? dst hdst complement)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (selectSingleBitLocal match? dst hdst complement)}
    {h₄ : LocalRewritePattern.ReturnValues (selectSingleBitLocal match? dst hdst complement)} :
    LocalRewritePattern.PreservesSemantics
      (selectSingleBitLocal match? dst hdst complement) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectSingleBitLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := hMatchImplies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    hVerified opVerif hOpType
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
  have isT : Attribute.isType (Attribute.integerType intType) :=
    hResTypeVal ▸ (((op.getResult 0).get! ctx.raw).type).2
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Bitwidth guard: `intType.bitwidth = 64`.
  peelSplittableCondition' [hBw] hpattern
  -- Peel the constant match on the rhs.
  have hCVSome : (matchConstantIntVal rhs ctx.raw).isSome := by
    cases hCV : matchConstantIntVal rhs ctx.raw with
    | some y => rfl
    | none => rw [hCV] at hpattern; simp at hpattern
  obtain ⟨imm, hCV⟩ := Option.isSome_iff_exists.mp hCVSome
  rw [hCV] at hpattern
  simp only [] at hpattern
  -- The `!(simm12)` fire guard: continue only when the immediate is *out* of the simm12 range.
  split at hpattern
  · simp at hpattern
  -- Peel the `singleSetBit` match, obtaining the bit index `n`.
  have hSSBSome : (singleSetBit (if complement then ~~~ BitVec.ofInt 64 imm.value
      else BitVec.ofInt 64 imm.value)).isSome := by
    cases hSSB : singleSetBit (if complement then ~~~ BitVec.ofInt 64 imm.value
        else BitVec.ofInt 64 imm.value) with
    | some y => rfl
    | none => rw [hSSB] at hpattern; simp at hpattern
  obtain ⟨n, hSSB⟩ := Option.isSome_iff_exists.mp hSSBSome
  rw [hSSB] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched binop.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps hSemSrc
      hinterp hLhsType hRhsType
  subst hCf
  -- Pin the rhs's runtime value to the matched constant.
  have hyConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf
    hCV (by rw [hOperands]; simp) hRhsType
  obtain rfl : yVal = Data.LLVM.Int.constant intType.bitwidth imm.value := by
    have h := hyVal.symm.trans hyConst; simpa using h
  have hDomCtxLhs : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have lhsNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the three creations.
  peelCastToRegLocal hpattern ctx₁ castOp hCast hDomCtxLhs hDom₁
  peelOpCreation! hpattern ctx₂ immOp hImm hDom₁ hDom₂
  peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
  cleanupHpattern hpattern
  obtain ⟨xt, hOpVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
      hDomCtxLhs hDom₃ lhsNotOp
  obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
  have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hImmType : immOp.getOpType! ctx₃.raw = .riscv dst := by grind
  have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastOperands : castOp.getOperands! ctx₃.raw = #[lhs] := by grind
  have hImmOperands :
      immOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by grind
  have hCastBackOperands :
      castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (immOp.getResult 0)] := by grind
  have hImmProps : immOp.getProperties! ctx₃.raw (.riscv dst)
      = cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk n (IntegerType.mk 64))) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hImm (operation := immOp)]
  have hCBType : ((op.getResult 0).get! ctx₂.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, isT⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hImm
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCast
          (value := ValuePtr.opResult (op.getResult 0))]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hCastResTypes : castOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hImm (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
  have hImmResTypes : immOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hImm (operation := immOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := immOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, isT⟩] := by grind
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hCastType hCastOperands hCastResTypes hOpVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := resFn n (LLVM.Int.toReg xt))
      (props := cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk n (IntegerType.mk 64))))
      (hSemR n (LLVM.Int.toReg xt))
      hImmType hImmProps hImmOperands hImmResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt (resFn n (LLVM.Int.toReg xt)) 64)], ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using hRefine xVal xt imm.value n props hSSB hxtRef⟩

/-! ### Instantiations -/

namespace Example

/-- Correctness of `riscv.bseti` lowering of `llvm.or x (const)` when `const` is a single set bit. -/
theorem or_isRefinedBy_toInt_bseti {x xt : Data.LLVM.Int 64} (c n : Int) (d : Bool)
    (hb : singleSetBit (BitVec.ofInt 64 c) = some n) (h : x ⊒ xt) :
    Data.LLVM.Int.or x (Data.LLVM.Int.constant 64 c) d
      ⊒ RISCV.Reg.toInt (Data.RISCV.bseti (BitVec.ofInt 6 n) (LLVM.Int.toReg xt)) 64 := by
  have hbr := singleSetBit_bridge _ _ hb
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by rw [Data.LLVM.Int.isPoison_or] at hnp; grind
  have hvd : x.getValueD = xt.getValueD := by grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.bseti]
  veir_bv_decide

/-- Correctness of `riscv.binvi` lowering of `llvm.xor x (const)` when `const` is a single set bit. -/
theorem xor_isRefinedBy_toInt_binvi {x xt : Data.LLVM.Int 64} (c n : Int)
    (hb : singleSetBit (BitVec.ofInt 64 c) = some n) (h : x ⊒ xt) :
    Data.LLVM.Int.xor x (Data.LLVM.Int.constant 64 c)
      ⊒ RISCV.Reg.toInt (Data.RISCV.binvi (BitVec.ofInt 6 n) (LLVM.Int.toReg xt)) 64 := by
  have hbr := singleSetBit_bridge _ _ hb
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by rw [Data.LLVM.Int.isPoison_xor] at hnp; grind
  have hvd : x.getValueD = xt.getValueD := by grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.binvi]
  veir_bv_decide

/-- Correctness of `riscv.bclri` lowering of `llvm.and x (const)` when `~const` is a single set bit. -/
theorem and_isRefinedBy_toInt_bclri {x xt : Data.LLVM.Int 64} (c n : Int)
    (hb : singleSetBit (~~~ BitVec.ofInt 64 c) = some n) (h : x ⊒ xt) :
    Data.LLVM.Int.and x (Data.LLVM.Int.constant 64 c)
      ⊒ RISCV.Reg.toInt (Data.RISCV.bclri (BitVec.ofInt 6 n) (LLVM.Int.toReg xt)) 64 := by
  have hbr := singleSetBit_bridge _ _ hb
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by rw [Data.LLVM.Int.isPoison_and] at hnp; grind
  have hvd : x.getValueD = xt.getValueD := by grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.bclri]
  veir_bv_decide

theorem bseti_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics
      (selectSingleBitLocal matchOr .bseti rfl false) h h₂ h₃ h₄ :=
  selectSingleBitLocal_preservesSemantics
    (srcOp := .or) (srcFn := fun x y props => Data.LLVM.Int.or x y props.disjoint)
    (resFn := fun n r => Data.RISCV.bseti (BitVec.ofInt 6 n) r)
    (fun hMatch => matchOr_implies hMatch)
    OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ c n props hb hx => by
      simpa using or_isRefinedBy_toInt_bseti c n props.disjoint (by simpa using hb) hx)

theorem binvi_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics
      (selectSingleBitLocal matchXor .binvi rfl false) h h₂ h₃ h₄ :=
  selectSingleBitLocal_preservesSemantics
    (srcOp := .xor) (srcFn := fun x y _ => Data.LLVM.Int.xor x y)
    (resFn := fun n r => Data.RISCV.binvi (BitVec.ofInt 6 n) r)
    (fun hMatch => matchXor_implies hMatch)
    OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ c n _ hb hx => by
      simpa using xor_isRefinedBy_toInt_binvi c n (by simpa using hb) hx)

theorem bclri_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics
      (selectSingleBitLocal matchAnd .bclri rfl true) h h₂ h₃ h₄ :=
  selectSingleBitLocal_preservesSemantics
    (srcOp := .and) (srcFn := fun x y _ => Data.LLVM.Int.and x y)
    (resFn := fun n r => Data.RISCV.bclri (BitVec.ofInt 6 n) r)
    (fun hMatch => matchAnd_implies hMatch)
    OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ _ h => by
      simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ c n _ hb hx => by
      simpa using and_isRefinedBy_toInt_bclri c n (by simpa using hb) hx)

end Example

end Veir
