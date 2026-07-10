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
-- Imported for their pre-generated match-congruence auxiliaries (see `LowerSelectSingleBit`).
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRoriw
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectSingleBit

namespace Veir

/-!
## Generic correctness of `udivPow2GenLocal`

`udivPow2GenLocal dst h width` strength-reduces `udiv x (2^k)` to a logical shift right by `k`
(`riscv.srli`/`srliw`): `castToReg x → dst (k) → castBack`. Instances: `udivPow2` (`srli`, i64),
`udivwPow2` (`srliw`, i32).

Same `castToReg → imm-op → castBack` shape as `selectSingleBitLocal`, with the emitted immediate the
shift amount `k` recovered from `matchUnsignedPow2Divisor` (and `matchUdiv`/`.udiv` baked into the
def). The two new data ingredients are `udiv_two_pow_eq_shift` (`x / 2^k = x >>> k` on bitvectors,
proved via `toNat` since `bv_decide` times out on division) and `mupd_singleSetBit` (a successful
power-of-two divisor match is a single set bit, reusing `singleSetBit_bridge`). The source `udiv`
raises UB on a zero/poison divisor, so the `hSemSrc` discharge is the UB-aware split (as in
`udiv_local`). -/

/-- Unsigned division by a single-bit power of two is a logical shift right. `bv_decide` times out on
    the 64-bit division circuit with a variable shift, so this goes through `toNat`. -/
theorem udiv_two_pow_eq_shift (x : BitVec 64) (s : BitVec 6) : x.udiv (1#64 <<< s) = x >>> s := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.udiv_eq, BitVec.toNat_udiv, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft,
    BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight]
  rw [(by decide : (1#64 : BitVec 64).toNat = 1), Nat.shiftLeft_eq, Nat.one_mul,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) s.isLt), Nat.shiftRight_eq_div_pow]

/-- A successful unsigned power-of-two divisor match on `i64` says the divisor's bit pattern is the
    single set bit `singleSetBit` recognizes, so `singleSetBit_bridge` applies. -/
theorem mupd_singleSetBit (c : Int) (k : Nat) (h : matchUnsignedPow2Divisor 64 c = some k) :
    singleSetBit (BitVec.ofInt 64 c) = some (k : Int) := by
  unfold matchUnsignedPow2Divisor singleSetBit unsignedMod at *
  rw [BitVec.toNat_ofInt]; simp only [Nat.reducePow]
  rw [log2IfPow2] at h; split at h <;> simp_all

/-- The `i32` analogue of `udiv_two_pow_eq_shift`. -/
theorem udiv_two_pow_eq_shift_32 (x : BitVec 32) (s : BitVec 5) :
    x.udiv (1#32 <<< s) = x >>> s := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.udiv_eq, BitVec.toNat_udiv, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft,
    BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight]
  rw [(by decide : (1#32 : BitVec 32).toNat = 1), Nat.shiftLeft_eq, Nat.one_mul,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) s.isLt), Nat.shiftRight_eq_div_pow]

/-- The `i32` analogue of `mupd_singleSetBit ∘ singleSetBit_bridge`: an unsigned power-of-two divisor
    match at width 32 pins the divisor's 32-bit pattern to the single bit `1 <<< k`. -/
theorem mupd_bridge_32 (c : Int) (k : Nat) (h : matchUnsignedPow2Divisor 32 c = some k) :
    BitVec.ofInt 32 c = 1#32 <<< BitVec.ofInt 5 (k : Int) := by
  have hfacts : (BitVec.ofInt 32 c).toNat ≠ 0 ∧
      (BitVec.ofInt 32 c).toNat &&& ((BitVec.ofInt 32 c).toNat - 1) = 0 ∧
      k = Nat.log2 (BitVec.ofInt 32 c).toNat := by
    unfold matchUnsignedPow2Divisor unsignedMod at h
    rw [show ((c % (2:Int)^32).toNat) = (BitVec.ofInt 32 c).toNat by
      rw [BitVec.toNat_ofInt]; simp] at h
    unfold log2IfPow2 at h
    split at h
    · nomatch h
    · rename_i hcond
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        bne_eq_false_iff_eq] at hcond
      rw [Option.some.injEq] at h
      exact ⟨hcond.1, hcond.2, h.symm⟩
  obtain ⟨hne, hand, hn⟩ := hfacts
  have hu := eq_two_pow_log2 _ hne hand
  have hlt : Nat.log2 (BitVec.ofInt 32 c).toNat < 32 := by
    have hb : 2 ^ (Nat.log2 (BitVec.ofInt 32 c).toNat) < 2 ^ 32 := by
      rw [← hu]; exact (BitVec.ofInt 32 c).isLt
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp hb
  apply BitVec.eq_of_toNat_eq
  subst hn
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  have hsh : (BitVec.ofInt 5 (Nat.log2 (BitVec.ofInt 32 c).toNat : Int)).toNat
      = Nat.log2 (BitVec.ofInt 32 c).toNat := by rw [BitVec.toNat_ofInt]; omega
  rw [hsh, Nat.shiftLeft_eq, (by decide : (1#32 : BitVec 32).toNat = 1), Nat.one_mul,
    Nat.mod_eq_of_lt (by rw [← hu]; exact (BitVec.ofInt 32 c).isLt)]
  exact hu

set_option maxHeartbeats 1600000 in
/-- Shared correctness proof for both `udivPow2GenLocal` lowerings. Per-lowering inputs: the emitted
    RISC-V op's interpreter fact (`hSemR`) and the data-level refinement (`hRefine`). -/
theorem udivPow2GenLocal_preservesSemantics
    {dst : Riscv} {hdst : Riscv.propertiesOf dst = RISCVImmediateProperties} {width : Nat}
    {resFn : Nat → Data.RISCV.Reg → Data.RISCV.Reg}
    (hSemR : ∀ (k : Nat) (r : Data.RISCV.Reg)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' dst
            (cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64))))
            resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (resFn k r)], mem, none)))
    (hRefine : ∀ (x xt : Data.LLVM.Int width) (c : Int) (k : Nat) (props : propertiesOf (.llvm .udiv)),
        matchUnsignedPow2Divisor width c = some k → x ⊒ xt →
        Data.LLVM.Int.udiv x (Data.LLVM.Int.constant width c) props.exact
          ⊒ RISCV.Reg.toInt (resFn k (LLVM.Int.toReg xt)) width)
    {h : LocalRewritePattern.ReturnOps (udivPow2GenLocal dst hdst width)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (udivPow2GenLocal dst hdst width)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (udivPow2GenLocal dst hdst width)}
    {h₄ : LocalRewritePattern.ReturnValues (udivPow2GenLocal dst hdst width)} :
    LocalRewritePattern.PreservesSemantics (udivPow2GenLocal dst hdst width) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, udivPow2GenLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  have hMatchSome : (matchUdiv op ctx.raw).isSome := by
    cases hM : matchUdiv op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchUdiv_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_udiv opVerif hOpType
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
  peelSplittableCondition' [hBw] hpattern
  have hCVSome : (matchConstantIntVal rhs ctx.raw).isSome := by
    cases hCV : matchConstantIntVal rhs ctx.raw with
    | some y => rfl
    | none => rw [hCV] at hpattern; simp at hpattern
  obtain ⟨imm, hCV⟩ := Option.isSome_iff_exists.mp hCVSome
  rw [hCV] at hpattern
  simp only [] at hpattern
  -- Peel the power-of-two divisor match, obtaining the shift amount `k`.
  have hKSome : (matchUnsignedPow2Divisor width imm.value).isSome := by
    cases hK : matchUnsignedPow2Divisor width imm.value with
    | some y => rfl
    | none => rw [hK] at hpattern; simp at hpattern
  obtain ⟨k, hK⟩ := Option.isSome_iff_exists.mp hKSome
  rw [hK] at hpattern
  simp only [] at hpattern
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .udiv)
      (srcFn := fun x y props => Data.LLVM.Int.udiv x y props.exact)
      opInBounds hOpType hNumResults hOperands hProps
      (fun _ _ _ _ _ _ _ _ hh => by
        simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self] at hh
        split at hh
        · simp at hh
        · split at hh
          · nomatch hh
          · split at hh
            · nomatch hh
            · simpa [pure, Interp] using hh.symm)
      hinterp hLhsType hRhsType
  subst hCf
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
      = cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64)))
      := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hImm (operation := immOp)]
  have hCBType : ((op.getResult 0).get! ctx₂.raw).type
      = (⟨Attribute.integerType { bitwidth := bw }, isT⟩ : TypeAttr) := by
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
      = #[⟨Attribute.integerType { bitwidth := bw }, isT⟩] := by grind
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hCastType hCastOperands hCastResTypes hOpVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := resFn k (LLVM.Int.toReg xt))
      (props := cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk (k : Int) (IntegerType.mk 64))))
      (hSemR k (LLVM.Int.toReg xt))
      hImmType hImmProps hImmOperands hImmResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int bw (RISCV.Reg.toInt (resFn k (LLVM.Int.toReg xt)) bw)], ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using hRefine xVal xt imm.value k props hK hxtRef⟩

/-! ### Instantiations -/

namespace Example

/-- Correctness of `riscv.srli` lowering of `llvm.udiv x (2^k)` on `i64`. -/
theorem udiv_isRefinedBy_toInt_srli {x xt : Data.LLVM.Int 64} (c : Int) (k : Nat) (e : Bool)
    (hk : matchUnsignedPow2Divisor 64 c = some k) (h : x ⊒ xt) :
    Data.LLVM.Int.udiv x (Data.LLVM.Int.constant 64 c) e
      ⊒ RISCV.Reg.toInt (Data.RISCV.srli (BitVec.ofInt 6 (k : Int)) (LLVM.Int.toReg xt)) 64 := by
  have hbr := singleSetBit_bridge _ _ (mupd_singleSetBit c k hk)
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by rw [Data.LLVM.Int.isPoison_udiv] at hnp; grind
  have hvd : x.getValueD = xt.getValueD := by grind [Data.LLVM.Int.getValueD_eq]
  rw [Data.LLVM.Int.getValue_udiv _ _ hnp, toInt_getValue]
  simp only [Data.LLVM.Int.getValue_eq_getValueD]
  rw [hvd, show (Data.LLVM.Int.constant 64 c).getValueD = BitVec.ofInt 64 c by
      simp [Data.LLVM.Int.getValueD, Data.LLVM.Int.constant],
    hbr, Data.RISCV.srli, udiv_two_pow_eq_shift]
  simp only [val_toReg, dif_neg (by simp [hp hxnp] : ¬ xt.isPoison = true),
    Data.LLVM.Int.getValue_eq_getValueD]
  bv_decide

theorem udivPow2_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics (udivPow2GenLocal .srli rfl 64) h h₂ h₃ h₄ :=
  udivPow2GenLocal_preservesSemantics
    (resFn := fun k r => Data.RISCV.srli (BitVec.ofInt 6 (k : Int)) r)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ c k props hk hx => udiv_isRefinedBy_toInt_srli c k props.exact hk hx)

/-- Correctness of `riscv.srliw` lowering of `llvm.udiv x (2^k)` on `i32`. -/
theorem udiv_isRefinedBy_toInt_srliw {x xt : Data.LLVM.Int 32} (c : Int) (k : Nat) (e : Bool)
    (hk : matchUnsignedPow2Divisor 32 c = some k) (h : x ⊒ xt) :
    Data.LLVM.Int.udiv x (Data.LLVM.Int.constant 32 c) e
      ⊒ RISCV.Reg.toInt (Data.RISCV.srliw (BitVec.ofInt 5 (k : Int)) (LLVM.Int.toReg xt)) 32 := by
  have hbr := mupd_bridge_32 c k hk
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by rw [Data.LLVM.Int.isPoison_udiv] at hnp; grind
  have hvd : x.getValueD = xt.getValueD := by grind [Data.LLVM.Int.getValueD_eq]
  rw [Data.LLVM.Int.getValue_udiv _ _ hnp, toInt_getValue]
  simp only [Data.LLVM.Int.getValue_eq_getValueD]
  rw [hvd, show (Data.LLVM.Int.constant 32 c).getValueD = BitVec.ofInt 32 c by
      simp [Data.LLVM.Int.getValueD, Data.LLVM.Int.constant],
    hbr, Data.RISCV.srliw]
  simp only [val_toReg, dif_neg (by simp [hp hxnp] : ¬ xt.isPoison = true),
    Data.LLVM.Int.getValue_eq_getValueD]
  rw [udiv_two_pow_eq_shift_32]
  bv_decide

theorem udivwPow2_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics (udivPow2GenLocal .srliw rfl 32) h h₂ h₃ h₄ :=
  udivPow2GenLocal_preservesSemantics
    (resFn := fun k r => Data.RISCV.srliw (BitVec.ofInt 5 (k : Int)) r)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ c k props hk hx => udiv_isRefinedBy_toInt_srliw c k props.exact hk hx)

end Example

end Veir
