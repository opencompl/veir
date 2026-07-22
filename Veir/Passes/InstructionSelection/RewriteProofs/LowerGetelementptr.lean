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
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.LowerLoad
import Veir.Passes.InstructionSelection.RewriteProofs.LowerIcmp

namespace Veir

open Veir.Data

/-!
## Correctness of `getelementptr_local`

`getelementptr_local` lowers a single-dynamic-index `llvm.getelementptr` computing
`ptr + idx * scale` (`scale` the byte size of the element type, `idx` an `i64`) to
`unrealized_conversion_cast ×2` (pointer and index to registers) → an address computation →
`unrealized_conversion_cast` back to `!llvm.ptr`. The address computation has five shapes:
`add` (`scale = 1`), `sh1add`/`sh2add`/`sh3add` (`scale = 2/4/8`), `slli (log2 scale); add`
(any other nonzero power of two below `2^64`), and `li scale; mul; add` (everything else — this
fallback is correct for *every* scale, since both `idx * scale` and the register multiply are
taken mod `2^64`).

The source interpretation has a UB branch (a poison index is immediate UB), so — as with the
div/rem lowerings — a *successful* source interpretation is what rules it out: the unfold lemma
below exposes the index as a concrete `.val idxv`. Addresses refine only themselves, so the final
obligation per shape is an exact `UInt64` equality (the `gep_bridge_*` lemmas), closed by
`toNat`-normalisation and `omega` (the symbolic-scale shapes generalize the `idx * scale` product
so `omega` stays linear).
-/

/-- A runtime value conforming to a type while being an address forces the type to be
    `!llvm.ptr`. Used to pin the matched `getelementptr`'s result type from its interpreted
    result value. -/
theorem conforms_addr_llvmPointerType {a : UInt64} {ty : TypeAttr}
    (h : RuntimeValue.Conforms (.addr a) ty) :
    ∃ pt, ty.val = Attribute.llvmPointerType pt := by
  obtain ⟨tv, htv⟩ := ty
  cases tv <;> simp_all [RuntimeValue.Conforms]

/-- A non-poison `LLVM.Int` is refined only by itself. -/
theorem LLVM.Int.val_isRefinedBy {w : Nat} {v : BitVec w} {i : Data.LLVM.Int w}
    (h : (Data.LLVM.Int.val v) ⊒ i) : i = .val v := by
  cases i <;> simp_all [_root_.isRefinedBy]

/-- Pointer cast-back forward lemma, symmetric to `interpretOp_castAddrToReg_forward`: a
    `builtin.unrealized_conversion_cast` with a single register operand `.reg r` and a
    `!llvm.ptr` result binds the result to `.addr ⟨r.val⟩` (the register bits as an address),
    leaving memory and every non-result variable unchanged. -/
theorem interpretOp_castRegToAddr_forward
    {ctx : WfIRContext OpCode} {castOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : castOp.InBounds ctx.raw} {v : ValuePtr} {pt} {hIsTy}
    {r : Data.RISCV.Reg}
    (hType : castOp.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hOperands : castOp.getOperands! ctx.raw = #[v])
    (hResTypes : castOp.getResultTypes! ctx.raw = #[⟨.llvmPointerType pt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp castOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (.addr ⟨r.val⟩) ∧
      (∀ v', v' ∉ castOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVar⟩ :=
    interpretOp_forward (op := castOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.addr ⟨r.val⟩]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [hResTypes, interpretOp', pure, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Unfold the interpretation of a matched `llvm.getelementptr`: from a successful `interpretOp`
    we read the pointer operand's address `.addr pa`, the (necessarily non-poison — the poison
    branch is UB) `i64` index value `.val idxv`, the element size `size`, and the computed result
    address, with memory unchanged and no control flow. -/
theorem matchGetelementptr_interpretOp_unfold {ctx : WfIRContext OpCode}
    {op : OperationPtr} {base idx : ValuePtr}
    {state : InterpreterState ctx} {newState cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm .getelementptr)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[base, idx])
    (hIdxType : (idx.getType! ctx.raw).val = Attribute.integerType ⟨64⟩)
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ (pa : UInt64) (idxv : BitVec 64) (size : Nat),
      state.variables.getVar? base = some (.addr pa) ∧
      state.variables.getVar? idx = some (.int 64 (.val idxv)) ∧
      Attribute.sizeOfType
        ((op.getProperties! ctx.raw (.llvm .getelementptr)).elem_type.val) = some size ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0)
        = some (.addr (pa.toNat + idxv.toNat * size).toUInt64) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 2 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hBaseEq : base = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hIdxEq : idx = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  -- Read the two operand values.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize0 : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize1 : 1 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨baseVal, hbaseVal⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize0
  obtain ⟨idxVal, hidxVal⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 1 hsize1
  have hBaseVar : state.variables.getVar? base = some baseVal := by
    rw [hBaseEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hbaseVal
  have hIdxVar : state.variables.getVar? idx = some idxVal := by
    rw [hIdxEq, show (op.getOperands! ctx.raw)[1]! = (op.getOperands! ctx.raw)[1] from by grind]
    exact hidxVal
  -- The index conforms to `i64`.
  have hIdxConf := VariableState.getVar?_conforms hIdxVar
  rw [show idx.getType! ctx.raw = ⟨.integerType ⟨64⟩, hIdxType ▸ (idx.getType! ctx.raw).2⟩
        from Subtype.ext hIdxType] at hIdxConf
  obtain ⟨xi, rfl⟩ := RuntimeValue.Conforms.integerType hIdxConf
  -- Assemble the full operand-value array.
  have hOperand0 : op.getOperand! ctx.raw 0 = base := by
    rw [hBaseEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = idx := by
    rw [hIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[baseVal, RuntimeValue.int 64 xi] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · simpa [hOperand0] using hBaseVar
    · simpa [hOperand1] using hIdxVar
  -- Unfold `.getelementptr`.
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Llvm.interpretOp', List.toList_toArray, bind, pure] at hInterp'
  -- Force `baseVal = .addr pa` (the only list pattern that can succeed).
  split at hInterp'
  next pa bw ixi heq =>
    have hb : baseVal = .addr pa := by grind
    subst hb
    have hbw : bw = 64 := by grind
    subst hbw
    have hxi : ixi = xi := by grind
    subst hxi
    -- The element size must resolve.
    cases hS : Attribute.sizeOfType
        ((op.getProperties! ctx.raw (.llvm .getelementptr)).elem_type.val) with
    | none => rw [hS] at hInterp'; simp [Interp] at hInterp'
    | some size =>
      rw [hS] at hInterp'
      simp only [Interp, Option.bind_some] at hInterp'
      -- The index must be a concrete value (poison is UB).
      cases ixi with
      | poison =>
        simp only [liftM, monadLift, MonadLift.monadLift, Interp.ub] at hInterp'
        simp at hInterp'
      | val idxv =>
        simp only [Interp, Option.some.injEq, UBOr.ok.injEq, Prod.mk.injEq] at hInterp'
        obtain ⟨rfl, rfl, rfl⟩ := hInterp'
        subst hNew
        refine ⟨pa, idxv, size, hBaseVar, hIdxVar, rfl, rfl, ?_, rfl⟩
        rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
        simp
  next heq => simp [Interp] at hInterp'

/-!
### Address bridges

One exact `UInt64` equality per emitted shape: the source address `ptr + idx * scale` (computed
in `Nat`, truncated to `UInt64`) equals the bits of the final register. `P` is the pointer
register (`ofNat 64 pa.toNat`), the index register is `toReg (.val idxv) = idxv`
(zero-extension at width 64 is the identity).
-/

private theorem toReg_val_64 (idxv : BitVec 64) :
    (LLVM.Int.toReg (Data.LLVM.Int.val idxv)).val = idxv := by
  rw [val_toReg]
  simp [Data.LLVM.Int.isPoison, Data.LLVM.Int.getValue]

/-- `scale = 1`: `riscv.add ptr idx`. -/
theorem gep_bridge_add (pa : UInt64) (idxv : BitVec 64) :
    (pa.toNat + idxv.toNat * 1).toUInt64
      = ⟨(Data.RISCV.add (LLVM.Int.toReg (Data.LLVM.Int.val idxv))
          ⟨BitVec.ofNat 64 pa.toNat⟩).val⟩ := by
  apply UInt64.toNat_inj.mp
  simp only [Data.RISCV.add, toReg_val_64, Nat.toUInt64, UInt64.toNat_ofNat',
    UInt64.toNat_ofBitVec, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `scale = 2`: `riscv.sh1add idx ptr`. -/
theorem gep_bridge_sh1add (pa : UInt64) (idxv : BitVec 64) :
    (pa.toNat + idxv.toNat * 2).toUInt64
      = ⟨(Data.RISCV.sh1add ⟨BitVec.ofNat 64 pa.toNat⟩
          (LLVM.Int.toReg (Data.LLVM.Int.val idxv))).val⟩ := by
  apply UInt64.toNat_inj.mp
  simp only [Data.RISCV.sh1add, toReg_val_64, Nat.toUInt64, UInt64.toNat_ofNat',
    UInt64.toNat_ofBitVec, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    BitVec.shiftLeft_eq', BitVec.toNat_ofFin, Nat.shiftLeft_eq, Nat.reduceMod, Nat.reducePow]
  omega

/-- `scale = 4`: `riscv.sh2add idx ptr`. -/
theorem gep_bridge_sh2add (pa : UInt64) (idxv : BitVec 64) :
    (pa.toNat + idxv.toNat * 4).toUInt64
      = ⟨(Data.RISCV.sh2add ⟨BitVec.ofNat 64 pa.toNat⟩
          (LLVM.Int.toReg (Data.LLVM.Int.val idxv))).val⟩ := by
  apply UInt64.toNat_inj.mp
  simp only [Data.RISCV.sh2add, toReg_val_64, Nat.toUInt64, UInt64.toNat_ofNat',
    UInt64.toNat_ofBitVec, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    BitVec.shiftLeft_eq', BitVec.toNat_ofFin, Nat.shiftLeft_eq, Nat.reduceMod, Nat.reducePow]
  omega

/-- `scale = 8`: `riscv.sh3add idx ptr`. -/
theorem gep_bridge_sh3add (pa : UInt64) (idxv : BitVec 64) :
    (pa.toNat + idxv.toNat * 8).toUInt64
      = ⟨(Data.RISCV.sh3add ⟨BitVec.ofNat 64 pa.toNat⟩
          (LLVM.Int.toReg (Data.LLVM.Int.val idxv))).val⟩ := by
  apply UInt64.toNat_inj.mp
  simp only [Data.RISCV.sh3add, toReg_val_64, Nat.toUInt64, UInt64.toNat_ofNat',
    UInt64.toNat_ofBitVec, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    BitVec.shiftLeft_eq', BitVec.toNat_ofFin, Nat.shiftLeft_eq, Nat.reduceMod, Nat.reducePow]
  omega

/-- Nonzero power-of-two `scale = 2^k`, `k < 64`: `riscv.slli k idx` then `riscv.add`. -/
theorem gep_bridge_slli_add (pa : UInt64) (idxv : BitVec 64) (k : Nat) (hk : k < 64) :
    (pa.toNat + idxv.toNat * 2 ^ k).toUInt64
      = ⟨(Data.RISCV.add
          (Data.RISCV.slli (BitVec.ofInt 6 k) (LLVM.Int.toReg (Data.LLVM.Int.val idxv)))
          ⟨BitVec.ofNat 64 pa.toNat⟩).val⟩ := by
  apply UInt64.toNat_inj.mp
  have hsh : (BitVec.ofInt 6 (k : Int)).toNat = k := by
    rw [show ((k : Int) : Int) = ((k : Nat) : Int) from rfl]
    simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    omega
  simp only [Data.RISCV.add, Data.RISCV.slli, toReg_val_64, Nat.toUInt64, UInt64.toNat_ofNat',
    UInt64.toNat_ofBitVec, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    BitVec.shiftLeft_eq', BitVec.toNat_ofFin, Nat.shiftLeft_eq, hsh]
  generalize idxv.toNat * 2 ^ k = t
  omega

/-- Arbitrary `scale`: `riscv.li scale`, `riscv.mul`, `riscv.add`. Correct for *every* `scale`
    (both sides multiply mod `2^64`). -/
theorem gep_bridge_li_mul_add (pa : UInt64) (idxv : BitVec 64) (scale : Nat) :
    (pa.toNat + idxv.toNat * scale).toUInt64
      = ⟨(Data.RISCV.add
          (Data.RISCV.mul (Data.RISCV.li (BitVec.ofInt 64 scale))
            (LLVM.Int.toReg (Data.LLVM.Int.val idxv)))
          ⟨BitVec.ofNat 64 pa.toNat⟩).val⟩ := by
  apply UInt64.toNat_inj.mp
  have hli : (BitVec.ofInt 64 (scale : Int)).toNat = scale % 2 ^ 64 := by
    rw [show ((scale : Int) : Int) = ((scale : Nat) : Int) from rfl]
    simp [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  simp only [Data.RISCV.add, Data.RISCV.mul, Data.RISCV.li, toReg_val_64, Nat.toUInt64,
    UInt64.toNat_ofNat', UInt64.toNat_ofBitVec, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, hli]
  have h1 : idxv.toNat * (scale % 2 ^ 64) % 2 ^ 64 = idxv.toNat * scale % 2 ^ 64 := by
    rw [Nat.mul_mod, Nat.mul_mod idxv.toNat scale]
    congr 1
    congr 1
    omega
  rw [h1]
  generalize idxv.toNat * scale = t
  omega

/-!
### Correctness of `getelementptr_local`
-/

set_option maxHeartbeats 4000000 in
theorem getelementptr_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps getelementptr_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges getelementptr_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds getelementptr_local}
    {h₄ : LocalRewritePattern.ReturnValues getelementptr_local} :
    LocalRewritePattern.PreservesSemantics getelementptr_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, getelementptr_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchGetelementptr op ctx.raw).isSome := by
    cases hM : matchGetelementptr op ctx.raw with
    | some _ => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨base, idx, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchGetelementptr_implies hMatch
  -- Peel the single-dynamic-index guard.
  peelSplittableCondition' [hRawIdx] hpattern
  -- Peel the index-type destructure and the `i64` guard.
  split at hpattern
  case isFalse => simp at hpattern
  rename_i itype hIdxTy
  peelSplittableCondition' [hIBw] hpattern
  obtain ⟨ibw⟩ := itype; simp only at hIBw; subst hIBw
  -- Peel the element-size destructure.
  cases hScaleEq : Attribute.sizeOfType props.elem_type.val with
  | none => rw [hScaleEq] at hpattern; simp at hpattern
  | some scale =>
  rw [hScaleEq] at hpattern
  simp only [] at hpattern
  -- Unfold the source interpretation: pointer address, non-poison index, size, result address.
  obtain ⟨pa, idxv, size, hBaseVal, hIdxVal, hSize, hMem, hRes, hCf⟩ :=
    matchGetelementptr_interpretOp_unfold opInBounds hOpType hNumResults hOperands hIdxTy
      hinterp
  subst hCf
  -- The pattern's `scale` and the interpreter's `size` coincide.
  obtain rfl : size = scale := by
    rw [← hProps, hScaleEq] at hSize
    exact (Option.some.injEq _ _ ▸ hSize).symm
  -- The result type is a pointer type (from the conformance of the interpreted result).
  obtain ⟨pt, hPtrTy⟩ := conforms_addr_llvmPointerType (VariableState.getVar?_conforms hRes)
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.llvmPointerType pt := by
    simpa only [ValuePtr.getType!_opResult] using hPtrTy
  have hResType : ((op.getResult 0).get! ctx.raw).type
      = (⟨Attribute.llvmPointerType pt, hResTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩
          : TypeAttr) :=
    Subtype.ext hResTypeVal
  -- In-bounds, dominance, and not-a-result facts for the two operands.
  have hBaseIn : base.InBounds ctx.raw := by clear hpattern; grind
  have hIdxIn : idx.InBounds ctx.raw := by clear hpattern; grind
  have hDomCtxB : base.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxI : idx.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is the computed address.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have baseNotOp : ¬ base ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have idxNotOp : ¬ idx ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the two casts.
  peelOpCreation hpattern ctx₁ pcastOp hPcast
  replace hPcast := WfRewriter.createOp!_none_some hPcast
  obtain ⟨_, _, _, hPcast⟩ := hPcast
  peelOpCreation hpattern ctx₂ icastOp hIcast
  replace hIcast := WfRewriter.createOp!_none_some hIcast
  obtain ⟨_, _, _, hIcast⟩ := hIcast
  -- Open the scale-dispatch block: its creations sit under one extra existential.
  have ⟨⟨ctxG, gepOps, retOp⟩, hGep, hRest⟩ := hpattern
  clear hpattern
  -- Case on the emitted address-computation shape.
  split at hGep
  · -- ===== `scale = 1`: `riscv.add ptr idx` =====
    peelOpCreation hGep ctx₃ addOp hAdd
    replace hAdd := WfRewriter.createOp!_none_some hAdd
    obtain ⟨_, _, _, hAdd⟩ := hAdd
    cleanupHpattern hGep
    peelOpCreation hRest ctx₄ castOp hCast
    replace hCast := WfRewriter.createOp!_none_some hCast
    obtain ⟨_, _, _, hCast⟩ := hCast
    cleanupHpattern hRest
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hPcast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hIcast hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hAdd hOpIn₂
    have E₁ := CtxExtends.of_createOp (op := op) hPcast opInBounds
    have E₂ := CtxExtends.of_createOp (op := op) hIcast hOpIn₁
    have E₃ := CtxExtends.of_createOp (op := op) hAdd hOpIn₂
    have E₄ := CtxExtends.of_createOp (op := op) hCast hOpIn₃
    have F₃ : CtxExtends op ctx₃ ctx₄ := E₄
    have F₂ : CtxExtends op ctx₂ ctx₄ := E₃.trans F₃
    have F₁ : CtxExtends op ctx₁ ctx₄ := E₂.trans F₂
    have Ectx : CtxExtends op ctx ctx₄ := E₁.trans F₁
    -- Refined operand values in the target state.
    have hBase' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
      hBaseIn hBaseVal hDomCtxB (Ectx.dominates base hDomCtxB) baseNotOp
    obtain ⟨it, hIVal', hitRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hIdxIn hIdxVal
        hDomCtxI (Ectx.dominates idx hDomCtxI) idxNotOp
    have hItEq := LLVM.Int.val_isRefinedBy hitRef
    subst hItEq
    -- Structural facts.
    have hPcastIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
    have hIcastIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
    have hAddIn₃ : addOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds addOp hAdd
    have hCastIn₄ : castOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds castOp hCast
    have hPcastType : pcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType pcastOp hPcastIn₁]; grind
    have hIcastType : icastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType icastOp hIcastIn₂]; grind
    have hAddType : addOp.getOpType! ctx₄.raw = .riscv .add := by
      rw [F₃.opType addOp hAddIn₃]; grind
    have hCastType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hPcastOperands : pcastOp.getOperands! ctx₄.raw = #[base] := by
      rw [F₁.operands pcastOp hPcastIn₁]; grind
    have hIcastOperands : icastOp.getOperands! ctx₄.raw = #[idx] := by
      rw [F₂.operands icastOp hIcastIn₂]; grind
    have hAddOperands : addOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (pcastOp.getResult 0), ValuePtr.opResult (icastOp.getResult 0)] := by
      rw [F₃.operands addOp hAddIn₃]; grind
    have hCastOperands : castOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (addOp.getResult 0)] := by grind
    have hPcastResTypes : pcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes pcastOp hPcastIn₁]; grind
    have hIcastResTypes : icastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes icastOp hIcastIn₂]; grind
    have hAddResTypes : addOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₃.resultTypes addOp hAddIn₃]; grind
    have hCastResTypes : castOp.getResultTypes! ctx₄.raw
        = #[(⟨Attribute.llvmPointerType pt,
              hResTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
      have hC : castOp.getResultTypes! ctx₄.raw = #[((op.getResult 0).get! ctx.raw).type] := by
        grind
      rw [hC, hResType]
    -- Freshness facts for the frame clauses.
    have hPcastFresh : ¬ pcastOp.InBounds ctx.raw :=
      WfRewriter.createOp_new_not_inBounds pcastOp hPcast
    have hIcastFresh : ¬ icastOp.InBounds ctx₁.raw :=
      WfRewriter.createOp_new_not_inBounds icastOp hIcast
    have hPResIn₁ : (ValuePtr.opResult (pcastOp.getResult 0)).InBounds ctx₁.raw :=
      opResult_getResult_inBounds_of_createOp hPcast (by simp)
    -- Execute the chain.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castAddrToReg_forward (state := state')
        (inBounds := F₁.inBounds pcastOp hPcastIn₁)
        hPcastType hPcastOperands hPcastResTypes hBase'
    have hIVal₁ : s₁.variables.getVar? idx
        = some (RuntimeValue.int 64 (Data.LLVM.Int.val idxv)) := by
      rw [hFrame₁ idx (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hIdxIn hPcastFresh)]
      exact hIVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁)
        (inBounds := F₂.inBounds icastOp hIcastIn₂)
        hIcastType hIcastOperands hIcastResTypes hIVal₁
    have hP₂ : s₂.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
        = some (RuntimeValue.reg ⟨BitVec.ofNat 64 pa.toNat⟩) := by
      rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hPResIn₁ hIcastFresh)]
      exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₂)
        (inBounds := F₃.inBounds addOp hAddIn₃)
        (f := fun r₁ r₂ => Data.RISCV.add r₂ r₁) (fun _ _ _ _ => rfl)
        hAddType hAddOperands hAddResTypes hP₂ hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castRegToAddr_forward (state := s₃) (inBounds := hCastIn₄)
        hCastType hCastOperands hCastResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.add (LLVM.Int.toReg (Data.LLVM.Int.val idxv))
          ⟨BitVec.ofNat 64 pa.toNat⟩).val⟩], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          (by simpa [RuntimeValue.isRefinedBy] using gep_bridge_add pa idxv)
  · -- ===== `scale = 2`: `riscv.sh1add idx ptr` =====
    peelOpCreation hGep ctx₃ addOp hAdd
    replace hAdd := WfRewriter.createOp!_none_some hAdd
    obtain ⟨_, _, _, hAdd⟩ := hAdd
    cleanupHpattern hGep
    peelOpCreation hRest ctx₄ castOp hCast
    replace hCast := WfRewriter.createOp!_none_some hCast
    obtain ⟨_, _, _, hCast⟩ := hCast
    cleanupHpattern hRest
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hPcast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hIcast hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hAdd hOpIn₂
    have E₁ := CtxExtends.of_createOp (op := op) hPcast opInBounds
    have E₂ := CtxExtends.of_createOp (op := op) hIcast hOpIn₁
    have E₃ := CtxExtends.of_createOp (op := op) hAdd hOpIn₂
    have E₄ := CtxExtends.of_createOp (op := op) hCast hOpIn₃
    have F₃ : CtxExtends op ctx₃ ctx₄ := E₄
    have F₂ : CtxExtends op ctx₂ ctx₄ := E₃.trans F₃
    have F₁ : CtxExtends op ctx₁ ctx₄ := E₂.trans F₂
    have Ectx : CtxExtends op ctx ctx₄ := E₁.trans F₁
    have hBase' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
      hBaseIn hBaseVal hDomCtxB (Ectx.dominates base hDomCtxB) baseNotOp
    obtain ⟨it, hIVal', hitRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hIdxIn hIdxVal
        hDomCtxI (Ectx.dominates idx hDomCtxI) idxNotOp
    have hItEq := LLVM.Int.val_isRefinedBy hitRef
    subst hItEq
    have hPcastIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
    have hIcastIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
    have hAddIn₃ : addOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds addOp hAdd
    have hCastIn₄ : castOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds castOp hCast
    have hPcastType : pcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType pcastOp hPcastIn₁]; grind
    have hIcastType : icastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType icastOp hIcastIn₂]; grind
    have hAddType : addOp.getOpType! ctx₄.raw = .riscv .sh1add := by
      rw [F₃.opType addOp hAddIn₃]; grind
    have hCastType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hPcastOperands : pcastOp.getOperands! ctx₄.raw = #[base] := by
      rw [F₁.operands pcastOp hPcastIn₁]; grind
    have hIcastOperands : icastOp.getOperands! ctx₄.raw = #[idx] := by
      rw [F₂.operands icastOp hIcastIn₂]; grind
    have hAddOperands : addOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (icastOp.getResult 0), ValuePtr.opResult (pcastOp.getResult 0)] := by
      rw [F₃.operands addOp hAddIn₃]; grind
    have hCastOperands : castOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (addOp.getResult 0)] := by grind
    have hPcastResTypes : pcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes pcastOp hPcastIn₁]; grind
    have hIcastResTypes : icastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes icastOp hIcastIn₂]; grind
    have hAddResTypes : addOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₃.resultTypes addOp hAddIn₃]; grind
    have hCastResTypes : castOp.getResultTypes! ctx₄.raw
        = #[(⟨Attribute.llvmPointerType pt,
              hResTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
      have hC : castOp.getResultTypes! ctx₄.raw = #[((op.getResult 0).get! ctx.raw).type] := by
        grind
      rw [hC, hResType]
    have hPcastFresh : ¬ pcastOp.InBounds ctx.raw :=
      WfRewriter.createOp_new_not_inBounds pcastOp hPcast
    have hIcastFresh : ¬ icastOp.InBounds ctx₁.raw :=
      WfRewriter.createOp_new_not_inBounds icastOp hIcast
    have hPResIn₁ : (ValuePtr.opResult (pcastOp.getResult 0)).InBounds ctx₁.raw :=
      opResult_getResult_inBounds_of_createOp hPcast (by simp)
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castAddrToReg_forward (state := state')
        (inBounds := F₁.inBounds pcastOp hPcastIn₁)
        hPcastType hPcastOperands hPcastResTypes hBase'
    have hIVal₁ : s₁.variables.getVar? idx
        = some (RuntimeValue.int 64 (Data.LLVM.Int.val idxv)) := by
      rw [hFrame₁ idx (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hIdxIn hPcastFresh)]
      exact hIVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁)
        (inBounds := F₂.inBounds icastOp hIcastIn₂)
        hIcastType hIcastOperands hIcastResTypes hIVal₁
    have hP₂ : s₂.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
        = some (RuntimeValue.reg ⟨BitVec.ofNat 64 pa.toNat⟩) := by
      rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hPResIn₁ hIcastFresh)]
      exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₂)
        (inBounds := F₃.inBounds addOp hAddIn₃)
        (f := fun r₁ r₂ => Data.RISCV.sh1add r₂ r₁) (fun _ _ _ _ => rfl)
        hAddType hAddOperands hAddResTypes hRes₂ hP₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castRegToAddr_forward (state := s₃) (inBounds := hCastIn₄)
        hCastType hCastOperands hCastResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.sh1add ⟨BitVec.ofNat 64 pa.toNat⟩
          (LLVM.Int.toReg (Data.LLVM.Int.val idxv))).val⟩], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          (by simpa [RuntimeValue.isRefinedBy] using gep_bridge_sh1add pa idxv)
  · -- ===== `scale = 4`: `riscv.sh2add idx ptr` =====
    peelOpCreation hGep ctx₃ addOp hAdd
    replace hAdd := WfRewriter.createOp!_none_some hAdd
    obtain ⟨_, _, _, hAdd⟩ := hAdd
    cleanupHpattern hGep
    peelOpCreation hRest ctx₄ castOp hCast
    replace hCast := WfRewriter.createOp!_none_some hCast
    obtain ⟨_, _, _, hCast⟩ := hCast
    cleanupHpattern hRest
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hPcast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hIcast hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hAdd hOpIn₂
    have E₁ := CtxExtends.of_createOp (op := op) hPcast opInBounds
    have E₂ := CtxExtends.of_createOp (op := op) hIcast hOpIn₁
    have E₃ := CtxExtends.of_createOp (op := op) hAdd hOpIn₂
    have E₄ := CtxExtends.of_createOp (op := op) hCast hOpIn₃
    have F₃ : CtxExtends op ctx₃ ctx₄ := E₄
    have F₂ : CtxExtends op ctx₂ ctx₄ := E₃.trans F₃
    have F₁ : CtxExtends op ctx₁ ctx₄ := E₂.trans F₂
    have Ectx : CtxExtends op ctx ctx₄ := E₁.trans F₁
    have hBase' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
      hBaseIn hBaseVal hDomCtxB (Ectx.dominates base hDomCtxB) baseNotOp
    obtain ⟨it, hIVal', hitRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hIdxIn hIdxVal
        hDomCtxI (Ectx.dominates idx hDomCtxI) idxNotOp
    have hItEq := LLVM.Int.val_isRefinedBy hitRef
    subst hItEq
    have hPcastIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
    have hIcastIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
    have hAddIn₃ : addOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds addOp hAdd
    have hCastIn₄ : castOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds castOp hCast
    have hPcastType : pcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType pcastOp hPcastIn₁]; grind
    have hIcastType : icastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType icastOp hIcastIn₂]; grind
    have hAddType : addOp.getOpType! ctx₄.raw = .riscv .sh2add := by
      rw [F₃.opType addOp hAddIn₃]; grind
    have hCastType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hPcastOperands : pcastOp.getOperands! ctx₄.raw = #[base] := by
      rw [F₁.operands pcastOp hPcastIn₁]; grind
    have hIcastOperands : icastOp.getOperands! ctx₄.raw = #[idx] := by
      rw [F₂.operands icastOp hIcastIn₂]; grind
    have hAddOperands : addOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (icastOp.getResult 0), ValuePtr.opResult (pcastOp.getResult 0)] := by
      rw [F₃.operands addOp hAddIn₃]; grind
    have hCastOperands : castOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (addOp.getResult 0)] := by grind
    have hPcastResTypes : pcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes pcastOp hPcastIn₁]; grind
    have hIcastResTypes : icastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes icastOp hIcastIn₂]; grind
    have hAddResTypes : addOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₃.resultTypes addOp hAddIn₃]; grind
    have hCastResTypes : castOp.getResultTypes! ctx₄.raw
        = #[(⟨Attribute.llvmPointerType pt,
              hResTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
      have hC : castOp.getResultTypes! ctx₄.raw = #[((op.getResult 0).get! ctx.raw).type] := by
        grind
      rw [hC, hResType]
    have hPcastFresh : ¬ pcastOp.InBounds ctx.raw :=
      WfRewriter.createOp_new_not_inBounds pcastOp hPcast
    have hIcastFresh : ¬ icastOp.InBounds ctx₁.raw :=
      WfRewriter.createOp_new_not_inBounds icastOp hIcast
    have hPResIn₁ : (ValuePtr.opResult (pcastOp.getResult 0)).InBounds ctx₁.raw :=
      opResult_getResult_inBounds_of_createOp hPcast (by simp)
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castAddrToReg_forward (state := state')
        (inBounds := F₁.inBounds pcastOp hPcastIn₁)
        hPcastType hPcastOperands hPcastResTypes hBase'
    have hIVal₁ : s₁.variables.getVar? idx
        = some (RuntimeValue.int 64 (Data.LLVM.Int.val idxv)) := by
      rw [hFrame₁ idx (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hIdxIn hPcastFresh)]
      exact hIVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁)
        (inBounds := F₂.inBounds icastOp hIcastIn₂)
        hIcastType hIcastOperands hIcastResTypes hIVal₁
    have hP₂ : s₂.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
        = some (RuntimeValue.reg ⟨BitVec.ofNat 64 pa.toNat⟩) := by
      rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hPResIn₁ hIcastFresh)]
      exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₂)
        (inBounds := F₃.inBounds addOp hAddIn₃)
        (f := fun r₁ r₂ => Data.RISCV.sh2add r₂ r₁) (fun _ _ _ _ => rfl)
        hAddType hAddOperands hAddResTypes hRes₂ hP₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castRegToAddr_forward (state := s₃) (inBounds := hCastIn₄)
        hCastType hCastOperands hCastResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.sh2add ⟨BitVec.ofNat 64 pa.toNat⟩
          (LLVM.Int.toReg (Data.LLVM.Int.val idxv))).val⟩], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          (by simpa [RuntimeValue.isRefinedBy] using gep_bridge_sh2add pa idxv)
  · -- ===== `scale = 8`: `riscv.sh3add idx ptr` =====
    peelOpCreation hGep ctx₃ addOp hAdd
    replace hAdd := WfRewriter.createOp!_none_some hAdd
    obtain ⟨_, _, _, hAdd⟩ := hAdd
    cleanupHpattern hGep
    peelOpCreation hRest ctx₄ castOp hCast
    replace hCast := WfRewriter.createOp!_none_some hCast
    obtain ⟨_, _, _, hCast⟩ := hCast
    cleanupHpattern hRest
    have hOpIn₁ : op.InBounds ctx₁.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hPcast opInBounds
    have hOpIn₂ : op.InBounds ctx₂.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hIcast hOpIn₁
    have hOpIn₃ : op.InBounds ctx₃.raw :=
      WfRewriter.createOp_inBounds_mono (ptr := .operation op) hAdd hOpIn₂
    have E₁ := CtxExtends.of_createOp (op := op) hPcast opInBounds
    have E₂ := CtxExtends.of_createOp (op := op) hIcast hOpIn₁
    have E₃ := CtxExtends.of_createOp (op := op) hAdd hOpIn₂
    have E₄ := CtxExtends.of_createOp (op := op) hCast hOpIn₃
    have F₃ : CtxExtends op ctx₃ ctx₄ := E₄
    have F₂ : CtxExtends op ctx₂ ctx₄ := E₃.trans F₃
    have F₁ : CtxExtends op ctx₁ ctx₄ := E₂.trans F₂
    have Ectx : CtxExtends op ctx ctx₄ := E₁.trans F₁
    have hBase' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
      hBaseIn hBaseVal hDomCtxB (Ectx.dominates base hDomCtxB) baseNotOp
    obtain ⟨it, hIVal', hitRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hIdxIn hIdxVal
        hDomCtxI (Ectx.dominates idx hDomCtxI) idxNotOp
    have hItEq := LLVM.Int.val_isRefinedBy hitRef
    subst hItEq
    have hPcastIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
    have hIcastIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
    have hAddIn₃ : addOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds addOp hAdd
    have hCastIn₄ : castOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds castOp hCast
    have hPcastType : pcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType pcastOp hPcastIn₁]; grind
    have hIcastType : icastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType icastOp hIcastIn₂]; grind
    have hAddType : addOp.getOpType! ctx₄.raw = .riscv .sh3add := by
      rw [F₃.opType addOp hAddIn₃]; grind
    have hCastType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hPcastOperands : pcastOp.getOperands! ctx₄.raw = #[base] := by
      rw [F₁.operands pcastOp hPcastIn₁]; grind
    have hIcastOperands : icastOp.getOperands! ctx₄.raw = #[idx] := by
      rw [F₂.operands icastOp hIcastIn₂]; grind
    have hAddOperands : addOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (icastOp.getResult 0), ValuePtr.opResult (pcastOp.getResult 0)] := by
      rw [F₃.operands addOp hAddIn₃]; grind
    have hCastOperands : castOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (addOp.getResult 0)] := by grind
    have hPcastResTypes : pcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes pcastOp hPcastIn₁]; grind
    have hIcastResTypes : icastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes icastOp hIcastIn₂]; grind
    have hAddResTypes : addOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₃.resultTypes addOp hAddIn₃]; grind
    have hCastResTypes : castOp.getResultTypes! ctx₄.raw
        = #[(⟨Attribute.llvmPointerType pt,
              hResTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
      have hC : castOp.getResultTypes! ctx₄.raw = #[((op.getResult 0).get! ctx.raw).type] := by
        grind
      rw [hC, hResType]
    have hPcastFresh : ¬ pcastOp.InBounds ctx.raw :=
      WfRewriter.createOp_new_not_inBounds pcastOp hPcast
    have hIcastFresh : ¬ icastOp.InBounds ctx₁.raw :=
      WfRewriter.createOp_new_not_inBounds icastOp hIcast
    have hPResIn₁ : (ValuePtr.opResult (pcastOp.getResult 0)).InBounds ctx₁.raw :=
      opResult_getResult_inBounds_of_createOp hPcast (by simp)
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castAddrToReg_forward (state := state')
        (inBounds := F₁.inBounds pcastOp hPcastIn₁)
        hPcastType hPcastOperands hPcastResTypes hBase'
    have hIVal₁ : s₁.variables.getVar? idx
        = some (RuntimeValue.int 64 (Data.LLVM.Int.val idxv)) := by
      rw [hFrame₁ idx (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hIdxIn hPcastFresh)]
      exact hIVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁)
        (inBounds := F₂.inBounds icastOp hIcastIn₂)
        hIcastType hIcastOperands hIcastResTypes hIVal₁
    have hP₂ : s₂.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
        = some (RuntimeValue.reg ⟨BitVec.ofNat 64 pa.toNat⟩) := by
      rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        hPResIn₁ hIcastFresh)]
      exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₂)
        (inBounds := F₃.inBounds addOp hAddIn₃)
        (f := fun r₁ r₂ => Data.RISCV.sh3add r₂ r₁) (fun _ _ _ _ => rfl)
        hAddType hAddOperands hAddResTypes hRes₂ hP₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castRegToAddr_forward (state := s₃) (inBounds := hCastIn₄)
        hCastType hCastOperands hCastResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.sh3add ⟨BitVec.ofNat 64 pa.toNat⟩
          (LLVM.Int.toReg (Data.LLVM.Int.val idxv))).val⟩], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          (by simpa [RuntimeValue.isRefinedBy] using gep_bridge_sh3add pa idxv)
  · -- ===== default: power-of-two (`slli`/`add`) or arbitrary (`li`/`mul`/`add`) =====
    split at hGep
    · -- power of two: `scale = 2 ^ Nat.log2 scale`, `Nat.log2 scale < 64`
      rename_i hPow2
      obtain ⟨hPowEq, hLogLt⟩ := hPow2
      peelOpCreation hGep ctx₃ slliOp hSlli
      replace hSlli := WfRewriter.createOp!_none_some hSlli
      obtain ⟨_, _, _, hSlli⟩ := hSlli
      peelOpCreation hGep ctx₄ addOp hAdd
      replace hAdd := WfRewriter.createOp!_none_some hAdd
      obtain ⟨_, _, _, hAdd⟩ := hAdd
      cleanupHpattern hGep
      peelOpCreation hRest ctx₅ castOp hCast
      replace hCast := WfRewriter.createOp!_none_some hCast
      obtain ⟨_, _, _, hCast⟩ := hCast
      cleanupHpattern hRest
      have hOpIn₁ : op.InBounds ctx₁.raw :=
        WfRewriter.createOp_inBounds_mono (ptr := .operation op) hPcast opInBounds
      have hOpIn₂ : op.InBounds ctx₂.raw :=
        WfRewriter.createOp_inBounds_mono (ptr := .operation op) hIcast hOpIn₁
      have hOpIn₃ : op.InBounds ctx₃.raw :=
        WfRewriter.createOp_inBounds_mono (ptr := .operation op) hSlli hOpIn₂
      have hOpIn₄ : op.InBounds ctx₄.raw :=
        WfRewriter.createOp_inBounds_mono (ptr := .operation op) hAdd hOpIn₃
      have E₁ := CtxExtends.of_createOp (op := op) hPcast opInBounds
      have E₂ := CtxExtends.of_createOp (op := op) hIcast hOpIn₁
      have E₃ := CtxExtends.of_createOp (op := op) hSlli hOpIn₂
      have E₄ := CtxExtends.of_createOp (op := op) hAdd hOpIn₃
      have E₅ := CtxExtends.of_createOp (op := op) hCast hOpIn₄
      have F₄ : CtxExtends op ctx₄ ctx₅ := E₅
      have F₃ : CtxExtends op ctx₃ ctx₅ := E₄.trans F₄
      have F₂ : CtxExtends op ctx₂ ctx₅ := E₃.trans F₃
      have F₁ : CtxExtends op ctx₁ ctx₅ := E₂.trans F₂
      have Ectx : CtxExtends op ctx ctx₅ := E₁.trans F₁
      have hBase' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
        hBaseIn hBaseVal hDomCtxB (Ectx.dominates base hDomCtxB) baseNotOp
      obtain ⟨it, hIVal', hitRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hIdxIn hIdxVal
          hDomCtxI (Ectx.dominates idx hDomCtxI) idxNotOp
      have hItEq := LLVM.Int.val_isRefinedBy hitRef
      subst hItEq
      have hPcastIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
      have hIcastIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
      have hSlliIn₃ : slliOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds slliOp hSlli
      have hAddIn₄ : addOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds addOp hAdd
      have hCastIn₅ : castOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds castOp hCast
      have hPcastType : pcastOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
        rw [F₁.opType pcastOp hPcastIn₁]; grind
      have hIcastType : icastOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
        rw [F₂.opType icastOp hIcastIn₂]; grind
      have hSlliType : slliOp.getOpType! ctx₅.raw = .riscv .slli := by
        rw [F₃.opType slliOp hSlliIn₃]; grind
      have hAddType : addOp.getOpType! ctx₅.raw = .riscv .add := by
        rw [F₄.opType addOp hAddIn₄]; grind
      have hCastType : castOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
        grind
      have hPcastOperands : pcastOp.getOperands! ctx₅.raw = #[base] := by
        rw [F₁.operands pcastOp hPcastIn₁]; grind
      have hIcastOperands : icastOp.getOperands! ctx₅.raw = #[idx] := by
        rw [F₂.operands icastOp hIcastIn₂]; grind
      have hSlliOperands : slliOp.getOperands! ctx₅.raw
          = #[ValuePtr.opResult (icastOp.getResult 0)] := by
        rw [F₃.operands slliOp hSlliIn₃]; grind
      have hAddOperands : addOp.getOperands! ctx₅.raw
          = #[ValuePtr.opResult (pcastOp.getResult 0),
              ValuePtr.opResult (slliOp.getResult 0)] := by
        rw [F₄.operands addOp hAddIn₄]; grind
      have hCastOperands : castOp.getOperands! ctx₅.raw
          = #[ValuePtr.opResult (addOp.getResult 0)] := by grind
      have hPcastResTypes : pcastOp.getResultTypes! ctx₅.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        rw [F₁.resultTypes pcastOp hPcastIn₁]; grind
      have hIcastResTypes : icastOp.getResultTypes! ctx₅.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        rw [F₂.resultTypes icastOp hIcastIn₂]; grind
      have hSlliResTypes : slliOp.getResultTypes! ctx₅.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        rw [F₃.resultTypes slliOp hSlliIn₃]; grind
      have hAddResTypes : addOp.getResultTypes! ctx₅.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        rw [F₄.resultTypes addOp hAddIn₄]; grind
      have hCastResTypes : castOp.getResultTypes! ctx₅.raw
          = #[(⟨Attribute.llvmPointerType pt,
                hResTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
        have hC : castOp.getResultTypes! ctx₅.raw = #[((op.getResult 0).get! ctx.raw).type] := by
          grind
        rw [hC, hResType]
      have hSlliProps : slliOp.getProperties! ctx₅.raw (.riscv .slli)
          = RISCVImmediateProperties.mk
              (IntegerAttr.mk (Nat.log2 scale) (IntegerType.mk 64)) := by
        rw [F₃.properties slliOp hSlliIn₃]
        grind [OperationPtr.getProperties!_WfRewriter_createOp hSlli (operation := slliOp)]
      have hPcastFresh : ¬ pcastOp.InBounds ctx.raw :=
        WfRewriter.createOp_new_not_inBounds pcastOp hPcast
      have hIcastFresh : ¬ icastOp.InBounds ctx₁.raw :=
        WfRewriter.createOp_new_not_inBounds icastOp hIcast
      have hSlliFresh : ¬ slliOp.InBounds ctx₂.raw :=
        WfRewriter.createOp_new_not_inBounds slliOp hSlli
      have hPResIn₁ : (ValuePtr.opResult (pcastOp.getResult 0)).InBounds ctx₁.raw :=
        opResult_getResult_inBounds_of_createOp hPcast (by simp)
      have hPResIn₂ : (ValuePtr.opResult (pcastOp.getResult 0)).InBounds ctx₂.raw :=
        E₂.valueInBounds _ hPResIn₁
      obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
        interpretOp_castAddrToReg_forward (state := state')
          (inBounds := F₁.inBounds pcastOp hPcastIn₁)
          hPcastType hPcastOperands hPcastResTypes hBase'
      have hIVal₁ : s₁.variables.getVar? idx
          = some (RuntimeValue.int 64 (Data.LLVM.Int.val idxv)) := by
        rw [hFrame₁ idx (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
          hIdxIn hPcastFresh)]
        exact hIVal'
      obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
        interpretOp_castToReg_forward (state := s₁)
          (inBounds := F₂.inBounds icastOp hIcastIn₂)
          hIcastType hIcastOperands hIcastResTypes hIVal₁
      obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
        interpretOp_riscv_unaryReg_imm_forward (state := s₂)
          (inBounds := F₃.inBounds slliOp hSlliIn₃)
          (res := Data.RISCV.slli (BitVec.ofInt 6 (Nat.log2 scale))
            (LLVM.Int.toReg (Data.LLVM.Int.val idxv)))
          (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
          hSlliType hSlliProps hSlliOperands hSlliResTypes hRes₂
      have hP₃ : s₃.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
          = some (RuntimeValue.reg ⟨BitVec.ofNat 64 pa.toNat⟩) := by
        rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
          hPResIn₂ hSlliFresh),
          hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
          hPResIn₁ hIcastFresh)]
        exact hRes₁
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
        interpretOp_riscv_binaryReg_forward (state := s₃)
          (inBounds := F₄.inBounds addOp hAddIn₄)
          (f := fun r₁ r₂ => Data.RISCV.add r₂ r₁) (fun _ _ _ _ => rfl)
          hAddType hAddOperands hAddResTypes hP₃ hRes₃
      obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
        interpretOp_castRegToAddr_forward (state := s₄) (inBounds := hCastIn₅)
          hCastType hCastOperands hCastResTypes hRes₄
      refine ⟨s₅, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, liftM, monadLift,
          MonadLift.monadLift, Interp]
      · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.add
            (Data.RISCV.slli (BitVec.ofInt 6 (Nat.log2 scale))
              (LLVM.Int.toReg (Data.LLVM.Int.val idxv)))
            ⟨BitVec.ofNat 64 pa.toNat⟩).val⟩], ?_, ?_⟩
        · simp [hRes₅, Option.bind, Option.map]
        · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
          have hBr := gep_bridge_slli_add pa idxv (Nat.log2 scale) hLogLt
          rw [← hPowEq] at hBr
          simpa [RuntimeValue.isRefinedBy] using hBr
    · -- arbitrary scale: `li`/`mul`/`add`
      peelOpCreation hGep ctx₃ liOp hLi
      replace hLi := WfRewriter.createOp!_none_some hLi
      obtain ⟨_, _, _, hLi⟩ := hLi
      peelOpCreation hGep ctx₄ mulOp hMul
      replace hMul := WfRewriter.createOp!_none_some hMul
      obtain ⟨_, _, _, hMul⟩ := hMul
      peelOpCreation hGep ctx₅ addOp hAdd
      replace hAdd := WfRewriter.createOp!_none_some hAdd
      obtain ⟨_, _, _, hAdd⟩ := hAdd
      cleanupHpattern hGep
      peelOpCreation hRest ctx₆ castOp hCast
      replace hCast := WfRewriter.createOp!_none_some hCast
      obtain ⟨_, _, _, hCast⟩ := hCast
      cleanupHpattern hRest
      have hOpIn₁ : op.InBounds ctx₁.raw :=
        WfRewriter.createOp_inBounds_mono (ptr := .operation op) hPcast opInBounds
      have hOpIn₂ : op.InBounds ctx₂.raw :=
        WfRewriter.createOp_inBounds_mono (ptr := .operation op) hIcast hOpIn₁
      have hOpIn₃ : op.InBounds ctx₃.raw :=
        WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLi hOpIn₂
      have hOpIn₄ : op.InBounds ctx₄.raw :=
        WfRewriter.createOp_inBounds_mono (ptr := .operation op) hMul hOpIn₃
      have hOpIn₅ : op.InBounds ctx₅.raw :=
        WfRewriter.createOp_inBounds_mono (ptr := .operation op) hAdd hOpIn₄
      have E₁ := CtxExtends.of_createOp (op := op) hPcast opInBounds
      have E₂ := CtxExtends.of_createOp (op := op) hIcast hOpIn₁
      have E₃ := CtxExtends.of_createOp (op := op) hLi hOpIn₂
      have E₄ := CtxExtends.of_createOp (op := op) hMul hOpIn₃
      have E₅ := CtxExtends.of_createOp (op := op) hAdd hOpIn₄
      have E₆ := CtxExtends.of_createOp (op := op) hCast hOpIn₅
      have F₅ : CtxExtends op ctx₅ ctx₆ := E₆
      have F₄ : CtxExtends op ctx₄ ctx₆ := E₅.trans F₅
      have F₃ : CtxExtends op ctx₃ ctx₆ := E₄.trans F₄
      have F₂ : CtxExtends op ctx₂ ctx₆ := E₃.trans F₃
      have F₁ : CtxExtends op ctx₁ ctx₆ := E₂.trans F₂
      have Ectx : CtxExtends op ctx ctx₆ := E₁.trans F₁
      have hBase' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
        hBaseIn hBaseVal hDomCtxB (Ectx.dominates base hDomCtxB) baseNotOp
      obtain ⟨it, hIVal', hitRef⟩ :=
        LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hIdxIn hIdxVal
          hDomCtxI (Ectx.dominates idx hDomCtxI) idxNotOp
      have hItEq := LLVM.Int.val_isRefinedBy hitRef
      subst hItEq
      have hPcastIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
      have hIcastIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
      have hLiIn₃ : liOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds liOp hLi
      have hMulIn₄ : mulOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds mulOp hMul
      have hAddIn₅ : addOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds addOp hAdd
      have hCastIn₆ : castOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds castOp hCast
      have hPcastType : pcastOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
        rw [F₁.opType pcastOp hPcastIn₁]; grind
      have hIcastType : icastOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
        rw [F₂.opType icastOp hIcastIn₂]; grind
      have hLiType : liOp.getOpType! ctx₆.raw = .riscv .li := by
        rw [F₃.opType liOp hLiIn₃]; grind
      have hMulType : mulOp.getOpType! ctx₆.raw = .riscv .mul := by
        rw [F₄.opType mulOp hMulIn₄]; grind
      have hAddType : addOp.getOpType! ctx₆.raw = .riscv .add := by
        rw [F₅.opType addOp hAddIn₅]; grind
      have hCastType : castOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
        grind
      have hPcastOperands : pcastOp.getOperands! ctx₆.raw = #[base] := by
        rw [F₁.operands pcastOp hPcastIn₁]; grind
      have hIcastOperands : icastOp.getOperands! ctx₆.raw = #[idx] := by
        rw [F₂.operands icastOp hIcastIn₂]; grind
      have hLiOperands : liOp.getOperands! ctx₆.raw = #[] := by
        rw [F₃.operands liOp hLiIn₃]; grind
      have hMulOperands : mulOp.getOperands! ctx₆.raw
          = #[ValuePtr.opResult (icastOp.getResult 0), ValuePtr.opResult (liOp.getResult 0)] := by
        rw [F₄.operands mulOp hMulIn₄]; grind
      have hAddOperands : addOp.getOperands! ctx₆.raw
          = #[ValuePtr.opResult (pcastOp.getResult 0), ValuePtr.opResult (mulOp.getResult 0)] := by
        rw [F₅.operands addOp hAddIn₅]; grind
      have hCastOperands : castOp.getOperands! ctx₆.raw
          = #[ValuePtr.opResult (addOp.getResult 0)] := by grind
      have hPcastResTypes : pcastOp.getResultTypes! ctx₆.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        rw [F₁.resultTypes pcastOp hPcastIn₁]; grind
      have hIcastResTypes : icastOp.getResultTypes! ctx₆.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        rw [F₂.resultTypes icastOp hIcastIn₂]; grind
      have hLiResTypes : liOp.getResultTypes! ctx₆.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        rw [F₃.resultTypes liOp hLiIn₃]; grind
      have hMulResTypes : mulOp.getResultTypes! ctx₆.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        rw [F₄.resultTypes mulOp hMulIn₄]; grind
      have hAddResTypes : addOp.getResultTypes! ctx₆.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        rw [F₅.resultTypes addOp hAddIn₅]; grind
      have hCastResTypes : castOp.getResultTypes! ctx₆.raw
          = #[(⟨Attribute.llvmPointerType pt,
                hResTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
        have hC : castOp.getResultTypes! ctx₆.raw = #[((op.getResult 0).get! ctx.raw).type] := by
          grind
        rw [hC, hResType]
      have hLiProps : liOp.getProperties! ctx₆.raw (.riscv .li)
          = RISCVImmediateProperties.mk (IntegerAttr.mk scale (IntegerType.mk 64)) := by
        rw [F₃.properties liOp hLiIn₃]
        grind [OperationPtr.getProperties!_WfRewriter_createOp hLi (operation := liOp)]
      have hPcastFresh : ¬ pcastOp.InBounds ctx.raw :=
        WfRewriter.createOp_new_not_inBounds pcastOp hPcast
      have hIcastFresh : ¬ icastOp.InBounds ctx₁.raw :=
        WfRewriter.createOp_new_not_inBounds icastOp hIcast
      have hLiFresh : ¬ liOp.InBounds ctx₂.raw :=
        WfRewriter.createOp_new_not_inBounds liOp hLi
      have hMulFresh : ¬ mulOp.InBounds ctx₃.raw :=
        WfRewriter.createOp_new_not_inBounds mulOp hMul
      have hPResIn₁ : (ValuePtr.opResult (pcastOp.getResult 0)).InBounds ctx₁.raw :=
        opResult_getResult_inBounds_of_createOp hPcast (by simp)
      have hPResIn₂ : (ValuePtr.opResult (pcastOp.getResult 0)).InBounds ctx₂.raw :=
        E₂.valueInBounds _ hPResIn₁
      have hPResIn₃ : (ValuePtr.opResult (pcastOp.getResult 0)).InBounds ctx₃.raw :=
        E₃.valueInBounds _ hPResIn₂
      have hIResIn₂ : (ValuePtr.opResult (icastOp.getResult 0)).InBounds ctx₂.raw :=
        opResult_getResult_inBounds_of_createOp hIcast (by simp)
      obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
        interpretOp_castAddrToReg_forward (state := state')
          (inBounds := F₁.inBounds pcastOp hPcastIn₁)
          hPcastType hPcastOperands hPcastResTypes hBase'
      have hIVal₁ : s₁.variables.getVar? idx
          = some (RuntimeValue.int 64 (Data.LLVM.Int.val idxv)) := by
        rw [hFrame₁ idx (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
          hIdxIn hPcastFresh)]
        exact hIVal'
      obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
        interpretOp_castToReg_forward (state := s₁)
          (inBounds := F₂.inBounds icastOp hIcastIn₂)
          hIcastType hIcastOperands hIcastResTypes hIVal₁
      obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
        interpretOp_riscv_li_forward (state := s₂) (inBounds := F₃.inBounds liOp hLiIn₃)
          hLiType hLiProps hLiOperands hLiResTypes
      have hLi₃ : s₃.variables.getVar? (ValuePtr.opResult (liOp.getResult 0))
          = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 scale))) := hRes₃
      have hIReg₃ : s₃.variables.getVar? (ValuePtr.opResult (icastOp.getResult 0))
          = some (RuntimeValue.reg (LLVM.Int.toReg (Data.LLVM.Int.val idxv))) := by
        rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
          hIResIn₂ hLiFresh)]
        exact hRes₂
      obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
        interpretOp_riscv_binaryReg_forward (state := s₃)
          (inBounds := F₄.inBounds mulOp hMulIn₄)
          (f := fun r₁ r₂ => Data.RISCV.mul r₂ r₁) (fun _ _ _ _ => rfl)
          hMulType hMulOperands hMulResTypes hIReg₃ hLi₃
      have hP₄ : s₄.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
          = some (RuntimeValue.reg ⟨BitVec.ofNat 64 pa.toNat⟩) := by
        rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
          hPResIn₃ hMulFresh),
          hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
          hPResIn₂ hLiFresh),
          hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
          hPResIn₁ hIcastFresh)]
        exact hRes₁
      obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
        interpretOp_riscv_binaryReg_forward (state := s₄)
          (inBounds := F₅.inBounds addOp hAddIn₅)
          (f := fun r₁ r₂ => Data.RISCV.add r₂ r₁) (fun _ _ _ _ => rfl)
          hAddType hAddOperands hAddResTypes hP₄ hRes₄
      obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
        interpretOp_castRegToAddr_forward (state := s₅) (inBounds := hCastIn₆)
          hCastType hCastOperands hCastResTypes hRes₅
      refine ⟨s₆, ?_, by grind, ?_⟩
      · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, liftM, monadLift,
          MonadLift.monadLift, Interp]
      · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.add
            (Data.RISCV.mul (Data.RISCV.li (BitVec.ofInt 64 scale))
              (LLVM.Int.toReg (Data.LLVM.Int.val idxv)))
            ⟨BitVec.ofNat 64 pa.toNat⟩).val⟩], ?_, ?_⟩
        · simp [hRes₆, Option.bind, Option.map]
        · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
            (by simpa [RuntimeValue.isRefinedBy] using gep_bridge_li_mul_add pa idxv scale)

end Veir

