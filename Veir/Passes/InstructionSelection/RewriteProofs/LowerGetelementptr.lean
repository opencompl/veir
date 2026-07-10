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
import Veir.ForLean
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerConst
import Veir.Passes.InstructionSelection.RewriteProofs.LowerLoad
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectSingleBit

/-!
  Correctness of `getelementptr_local`, the lowering of a single-dynamic-index
  `llvm.getelementptr` to `ptr + idx * scale`, where `scale` is the byte size of the element type.

  The source semantics are pure `UInt64` (i.e. `BitVec 64`) arithmetic: `.addr ptr` and an `i64`
  index `idx` produce `.addr (ptr + idx * scale)`, wrapping modulo `2^64`. The lowering picks one of
  six instruction sequences depending on `scale`, all bracketed by a pointer-to-register cast of
  `ptr`, an integer-to-register cast of `idx`, and a register-to-pointer cast back:

  * `scale = 1`: `add ptr, idx`
  * `scale = 2, 4, 8`: `sh1add`/`sh2add`/`sh3add idx, ptr`
  * `scale` a power of two with `0 < scale` and `Nat.log2 scale < 64`: `slli idx, log2 scale`, `add`
  * otherwise: `li scale`, `mul idx, scale`, `add`

  The `0 < scale` guard matters: `scale = 0` also satisfies `scale &&& (scale - 1) = 0`, and
  `Nat.log2 0 = 0` would emit `idx << 0`. It falls into the last case, where `li 0`/`mul` correctly
  yields `ptr`.

  Each `gep_*_bridge` below is the arithmetic core of one branch: the register the sequence computes
  carries exactly the bits of the address the source produces. `getelementptr_local_preservesSemantics`
  peels the six-way dispatch and chains the interpretation of each branch's four to six created ops.
-/

namespace Veir

open Veir.Data

/-! ### Field transports across a `createOp`

  The longest branch creates six operations, at which point the
  `grind [getX!_WfRewriter_createOp …]` idiom used by the shorter lowerings falls over:
  `PreservesSemantics` bakes `hpattern` into the *types* of `state'Wf`/`state'Dom`/
  `valueRefinement`, so the unreduced pattern body can never be cleared from the context, and it
  grows with the emitted sequence. Every field transport is therefore done by explicit rewriting.
  (These duplicate the helpers in `LowerSdivPow2`; they belong in `CommonBaseLemmas`.) -/

theorem getOpType!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getOpType! ctx'.raw = opType := by
  rw [OperationPtr.getOpType!_WfRewriter_createOp h, if_pos rfl]

theorem getOpType!_createOp_ne {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    o.getOpType! ctx'.raw = o.getOpType! ctx.raw := by
  rw [OperationPtr.getOpType!_WfRewriter_createOp h, if_neg hne]

theorem getOperands!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getOperands! ctx'.raw = operands := by
  rw [OperationPtr.getOperands!_WfRewriter_createOp h, if_pos rfl]

theorem getOperands!_createOp_ne {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    o.getOperands! ctx'.raw = o.getOperands! ctx.raw := by
  rw [OperationPtr.getOperands!_WfRewriter_createOp h, if_neg hne]

theorem getResultTypes!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getResultTypes! ctx'.raw = resultTypes := by
  rw [OperationPtr.getResultTypes!_WfRewriter_createOp h, if_pos rfl]

theorem getResultTypes!_createOp_ne {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    o.getResultTypes! ctx'.raw = o.getResultTypes! ctx.raw := by
  rw [OperationPtr.getResultTypes!_WfRewriter_createOp h, if_neg hne]

theorem getProperties!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getProperties! ctx'.raw opType = properties := by
  rw [OperationPtr.getProperties!_WfRewriter_createOp h, if_pos rfl]

theorem getType!_opResult_createOp_ne {ctx ctx' : WfIRContext OpCode}
    {o newOp : OperationPtr} {i : Nat}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    (ValuePtr.opResult (o.getResult i)).getType! ctx'.raw
      = (ValuePtr.opResult (o.getResult i)).getType! ctx.raw := by
  rw [ValuePtr.getType!_WfRewriter_createOp h]
  exact dif_neg (by rintro ⟨hc, -⟩; exact hne hc)

/-- A pre-existing operation is distinct from one `createOp` freshly allocates. -/
theorem ne_createOp_new {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hIn : o.InBounds ctx.raw) :
    o ≠ newOp :=
  fun he => WfRewriter.createOp_new_not_inBounds newOp h (he ▸ hIn)

/-- A distinct operation's result is never among `b`'s results. -/
theorem opResult_not_mem_getResults! {ctx : IRContext OpCode} {a b : OperationPtr} {i : Nat}
    (hne : a ≠ b) : (ValuePtr.opResult (a.getResult i)) ∉ b.getResults! ctx := by
  rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx
      (ValuePtr.opResult (a.getResult i)) b with hres | ⟨j, hj, heq⟩
  · exact hres
  · exact absurd heq (by grind [OperationPtr.getResult])

/-! ### Structural facts about the matched operation

  Stated standalone because `grind` cannot reach them from inside the `PreservesSemantics` proof:
  the unreduced `hpattern` sits in the context and swamps its search. -/

/-- An operand of an in-bounds operation is in bounds. -/
theorem operand_inBounds {ctx : WfIRContext OpCode} {op : OperationPtr}
    (opInBounds : op.InBounds ctx.raw) {v : ValuePtr} (hv : v ∈ op.getOperands! ctx.raw) :
    v.InBounds ctx.raw := by grind

/-- An operand of an operation is never one of its results. -/
theorem operand_not_mem_getResults! {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    {op : OperationPtr} {v : ValuePtr}
    (hv : v ∈ op.getOperands! ctx.raw) : ¬ v ∈ op.getResults! ctx.raw := by
  grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]

/-- A single-result operation's result array. -/
theorem getResults_of_numResults_eq_one {ctx : WfIRContext OpCode} {op : OperationPtr}
    {hin : op.InBounds ctx.raw} (h : op.getNumResults! ctx.raw = 1) :
    op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by grind

/-! ### Pointer plumbing -/

/-- Only a pointer type admits an `.addr` runtime value. -/
theorem RuntimeValue.Conforms.of_addr {a : UInt64} {ty : TypeAttr}
    (h : RuntimeValue.Conforms (.addr a) ty) : ∃ p, ty.val = .llvmPointerType p := by
  obtain ⟨v, hv⟩ := ty
  cases v <;> simp only [RuntimeValue.Conforms] at h
  case llvmPointerType p => exact ⟨p, rfl⟩

/-- Cast-back forward lemma: a `builtin.unrealized_conversion_cast` with a single `!riscv.reg`
operand and an `!llvm.ptr` result binds the result to `.addr ⟨r.val⟩` (the register bits, read as an
address), leaving memory and every non-result variable unchanged. -/
theorem interpretOp_castRegToAddr_forward
    {ctx : WfIRContext OpCode} {castOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : castOp.InBounds ctx.raw} {v : ValuePtr} {pt : LLVM.PointerType} {hIsTy}
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

/-- Unfold the interpretation of a matched single-dynamic-index `llvm.getelementptr`: a successful
`interpretOp` forces the base operand to hold an address `.addr a` and the (`i64`-typed) index
operand to hold a non-poison value `.val idx`, and produces `.addr (a + ⟨idx⟩ * scale)` in a result
of pointer type, with memory unchanged and no control flow. -/
theorem matchGetelementptr_interpretOp_unfold {ctx : WfIRContext OpCode}
    {op : OperationPtr} {base idx : ValuePtr} {props : propertiesOf (.llvm .getelementptr)}
    {scale : Nat} {state newState : InterpreterState ctx} {cf}
    (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm .getelementptr)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[base, idx])
    (hProps : props = op.getProperties! ctx.raw (.llvm .getelementptr))
    (hScale : Attribute.sizeOfType props.elem_type.val = some scale)
    (hIdxType : (idx.getType! ctx.raw).val = Attribute.integerType ⟨64⟩)
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ a bv,
      state.variables.getVar? base = some (RuntimeValue.addr a) ∧
      state.variables.getVar? idx = some (RuntimeValue.int 64 (.val bv)) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0)
        = some (RuntimeValue.addr (a + ⟨bv⟩ * UInt64.ofNat scale)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 2 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hBaseEq : base = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hIdxEq : idx = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize0 : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize1 : 1 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨bval, hbval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize0
  obtain ⟨ival, hival⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 1 hsize1
  have hbGetVar : state.variables.getVar? base = some bval := by
    rw [hBaseEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hbval
  have hiGetVar : state.variables.getVar? idx = some ival := by
    rw [hIdxEq, show (op.getOperands! ctx.raw)[1]! = (op.getOperands! ctx.raw)[1] from by grind]
    exact hival
  -- The index operand's `i64` type pins its runtime value's bitwidth.
  have hiconf := VariableState.getVar?_conforms hiGetVar
  rw [show idx.getType! ctx.raw = ⟨.integerType ⟨64⟩, hIdxType ▸ (idx.getType! ctx.raw).2⟩
        from Subtype.ext hIdxType] at hiconf
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType hiconf
  have hOperand0 : op.getOperand! ctx.raw 0 = base := by
    rw [hBaseEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = idx := by
    rw [hIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op = some #[bval, RuntimeValue.int 64 y] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    match i, hi with
    | 0, _ => simpa [hOperand0] using hbGetVar
    | 1, _ => simpa [hOperand1] using hiGetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [← hProps, interpretOp', Llvm.interpretOp', bind, pure] at hInterp'
  -- Force `bval = .addr a` (the only arm that can succeed) and `y = .val bv` (poison is UB).
  split at hInterp'
  next _ a bw idx' heq =>
    obtain ⟨rfl, hiv, -⟩ : bval = .addr a ∧ RuntimeValue.int 64 y = RuntimeValue.int bw idx' ∧ True := by
      simpa only [List.cons.injEq] using heq
    obtain ⟨rfl, hidx⟩ : (64 : Nat) = bw ∧ HEq y idx' := by simpa using hiv
    obtain rfl : y = idx' := eq_of_heq hidx
    cases y with
    | poison =>
      simp [hScale, Interp, Interp.ub, liftM, monadLift, MonadLift.monadLift] at hInterp'
    | val bv =>
      simp only [hScale, Interp, liftM, monadLift, MonadLift.monadLift, Option.some.injEq,
        UBOr.ok.injEq] at hInterp'
      obtain ⟨rfl, rfl, rfl⟩ := hInterp'
      refine ⟨a, bv, hbGetVar, hiGetVar, by grind, ?_, rfl⟩
      have hres : (RuntimeValue.addr (a.toNat + bv.toNat * scale).toUInt64)
          = RuntimeValue.addr (a + ⟨bv⟩ * UInt64.ofNat scale) := by simp
      rw [← hres]; grind
  next => simp [Interp] at hInterp'

/-! ### Arithmetic bridges, one per emitted sequence

  In each, `pv := BitVec.ofNat 64 a.toNat` is the base pointer's register image (as produced by
  `interpretOp_castAddrToReg_forward`) and `⟨bv⟩` is the index's (as produced by
  `LLVM.Int.toReg` on a non-poison `i64`). The right-hand side is the address the `getelementptr`
  interpreter computes, read back through the register-to-pointer cast. The `Data.RISCV` operand
  order is `f rs2 rs1 = ⟨rs1.val ⋯ rs2.val⟩`, matching how the interpreter applies a binary
  register op to `#[r₁, r₂]`. -/

/-- The `i64` index's register image is just its bits. -/
theorem toReg_val_i64 (bv : BitVec 64) :
    LLVM.Int.toReg (Data.LLVM.Int.val bv) = ⟨bv⟩ := by simp [LLVM.Int.toReg]

/-- `scale = 1`: `add ptr, idx`. -/
theorem gep_scale1_bridge (a : UInt64) (bv : BitVec 64) :
    (Data.RISCV.add (⟨bv⟩ : Data.RISCV.Reg) ⟨BitVec.ofNat 64 a.toNat⟩).val
      = (a + (⟨bv⟩ : UInt64) * UInt64.ofNat 1).toBitVec := by
  simp only [Data.RISCV.add, BitVec.ofNat_uInt64ToNat, UInt64.toBitVec_add, UInt64.toBitVec_mul,
    UInt64.toBitVec_ofNat']
  bv_decide

/-- `scale = 2`: `sh1add idx, ptr`. -/
theorem gep_scale2_bridge (a : UInt64) (bv : BitVec 64) :
    (Data.RISCV.sh1add (⟨BitVec.ofNat 64 a.toNat⟩ : Data.RISCV.Reg) ⟨bv⟩).val
      = (a + (⟨bv⟩ : UInt64) * UInt64.ofNat 2).toBitVec := by
  simp only [Data.RISCV.sh1add, BitVec.ofNat_uInt64ToNat, UInt64.toBitVec_add, UInt64.toBitVec_mul,
    UInt64.toBitVec_ofNat']
  bv_decide

/-- `scale = 4`: `sh2add idx, ptr`. -/
theorem gep_scale4_bridge (a : UInt64) (bv : BitVec 64) :
    (Data.RISCV.sh2add (⟨BitVec.ofNat 64 a.toNat⟩ : Data.RISCV.Reg) ⟨bv⟩).val
      = (a + (⟨bv⟩ : UInt64) * UInt64.ofNat 4).toBitVec := by
  simp only [Data.RISCV.sh2add, BitVec.ofNat_uInt64ToNat, UInt64.toBitVec_add, UInt64.toBitVec_mul,
    UInt64.toBitVec_ofNat']
  bv_decide

/-- `scale = 8`: `sh3add idx, ptr`. -/
theorem gep_scale8_bridge (a : UInt64) (bv : BitVec 64) :
    (Data.RISCV.sh3add (⟨BitVec.ofNat 64 a.toNat⟩ : Data.RISCV.Reg) ⟨bv⟩).val
      = (a + (⟨bv⟩ : UInt64) * UInt64.ofNat 8).toBitVec := by
  simp only [Data.RISCV.sh3add, BitVec.ofNat_uInt64ToNat, UInt64.toBitVec_add, UInt64.toBitVec_mul,
    UInt64.toBitVec_ofNat']
  bv_decide

/-- A `slli` by `k < 64` multiplies by `2^k`. -/
theorem shiftLeft_ofInt_6_eq_mul (bv : BitVec 64) (k : Nat) (hk : k < 64) :
    bv <<< (BitVec.ofInt 6 (k : Int)) = bv * BitVec.ofNat 64 (2 ^ k) := by
  have hkn : (BitVec.ofInt 6 (k : Int)).toNat = k := by rw [BitVec.toNat_ofInt]; omega
  rw [BitVec.shiftLeft_eq', hkn]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp [Nat.mul_mod]

/-- `scale = 2^k` with `k = Nat.log2 scale < 64`: `slli idx, k` then `add ptr, _`. -/
theorem gep_pow2_bridge (a : UInt64) (bv : BitVec 64) (scale k : Nat)
    (hk : k < 64) (hscale : scale = 2 ^ k) :
    (Data.RISCV.add (Data.RISCV.slli (BitVec.ofInt 6 (k : Int)) ⟨bv⟩)
        (⟨BitVec.ofNat 64 a.toNat⟩ : Data.RISCV.Reg)).val
      = (a + (⟨bv⟩ : UInt64) * UInt64.ofNat scale).toBitVec := by
  subst hscale
  simp only [Data.RISCV.add, Data.RISCV.slli, shiftLeft_ofInt_6_eq_mul bv k hk,
    BitVec.ofNat_uInt64ToNat, UInt64.toBitVec_add, UInt64.toBitVec_mul, UInt64.toBitVec_ofNat']

/-- Arbitrary `scale`: `li scale`, `mul idx, scale`, `add ptr, _`. Correct for every `scale`,
    including `0` and values `≥ 2^64`, since both sides truncate modulo `2^64`. -/
theorem gep_general_bridge (a : UInt64) (bv : BitVec 64) (scale : Nat) :
    (Data.RISCV.add (Data.RISCV.mul (Data.RISCV.li (BitVec.ofInt 64 (scale : Int))) ⟨bv⟩)
        (⟨BitVec.ofNat 64 a.toNat⟩ : Data.RISCV.Reg)).val
      = (a + (⟨bv⟩ : UInt64) * UInt64.ofNat scale).toBitVec := by
  simp only [Data.RISCV.add, Data.RISCV.mul, Data.RISCV.li, BitVec.ofNat_uInt64ToNat,
    UInt64.toBitVec_add, UInt64.toBitVec_mul, UInt64.toBitVec_ofNat']
  congr 1


/-! ### Correctness of `getelementptr_local` -/

/-- A non-poison `i64` value is refined only by itself. -/
theorem eq_of_val_isRefinedBy {bv : BitVec 64} {xt : Data.LLVM.Int 64}
    (h : Data.LLVM.Int.val bv ⊒ xt) : xt = Data.LLVM.Int.val bv := by
  cases xt <;> rw [Data.LLVM.Int.isRefinedBy_iff] at h <;>
    simp_all [Data.LLVM.Int.isPoison, Data.LLVM.Int.getValue]

set_option maxHeartbeats 2000000 in
/-- Correctness of `getelementptr_local`: every one of the six emitted sequences computes the
    address `ptr + idx * scale` that the `llvm.getelementptr` interpreter produces. -/
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
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  have hMatchSome : (matchGetelementptr op ctx.raw).isSome := by
    cases hM : matchGetelementptr op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨base, idxv, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchGetelementptr_implies hMatch
  peelSplittableCondition' [hRci] hpattern
  split at hpattern
  · rename_i itype hIdxTyEq
    peelSplittableCondition' [hBw] hpattern
    split at hpattern
    · rename_i scale hScale
      obtain ⟨bw⟩ := itype
      simp only at hBw
      subst hBw
      -- Structural facts about the source op.
      have hBaseMem : base ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
      have hIdxMem : idxv ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
      have hBaseIn : base.InBounds ctx.raw := operand_inBounds opInBounds hBaseMem
      have hIdxIn : idxv.InBounds ctx.raw := operand_inBounds opInBounds hIdxMem
      have hDomBase : base.dominatesIp (InsertPoint.before op) ctx :=
        WfIRContext.Dom.operand_dominates_op ctxDom opInBounds hBaseMem
      have hDomIdx : idxv.dominatesIp (InsertPoint.before op) ctx :=
        WfIRContext.Dom.operand_dominates_op ctxDom opInBounds hIdxMem
      have hBaseNotOp : ¬ base ∈ op.getResults! ctx.raw := operand_not_mem_getResults! ctxDom hBaseMem
      have hIdxNotOp : ¬ idxv ∈ op.getResults! ctx.raw := operand_not_mem_getResults! ctxDom hIdxMem
      -- Unfold the source interpretation.
      obtain ⟨a, bv, hbVal, hiVal, hMem, hRes, hCf⟩ :=
        matchGetelementptr_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps
          hScale hIdxTyEq hinterp
      subst hCf
      -- The result type is a pointer type.
      have hResConf := VariableState.getVar?_conforms hRes
      rw [ValuePtr.getType!_opResult] at hResConf
      obtain ⟨pt, hPtrTy⟩ := RuntimeValue.Conforms.of_addr hResConf
      have isPt : Attribute.isType (Attribute.llvmPointerType pt) :=
        hPtrTy ▸ (((op.getResult 0).get! ctx.raw).type).2
      rw [getResults_of_numResults_eq_one hNumResults] at hsourceValues
      simp at hsourceValues
      simp [hRes] at hsourceValues
      subst sourceValues
      peelOpCreation!₂ hpattern ctx₁ pcastOp hPcast hDomBase hDomB₁ hDomIdx hDomI₁
      peelOpCreation!₂ hpattern ctx₂ icastOp hIcast hDomB₁ hDomB₂ hDomI₁ hDomI₂
      split at hpattern
      · -- scale = 1: `add ptr, idx`
        peelOpCreation!₂ hpattern ctx₃ addOp hAdd hDomB₂ hDomB₃ hDomI₂ hDomI₃
        peelOpCreation!₂ hpattern ctx₄ castOp hCast hDomB₃ hDomB₄ hDomI₃ hDomI₄
        cleanupHpattern hpattern
        -- Refined operand values in the target state.
        have hbVal' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
          hBaseIn hbVal hDomBase hDomB₄ hBaseNotOp
        obtain ⟨xt, hiVal', hxtRef⟩ := LocalRewritePattern.exists_refined_int_getVar?
          valueRefinement state'Dom hIdxIn hiVal hDomIdx hDomI₄ hIdxNotOp
        obtain rfl : xt = Data.LLVM.Int.val bv := eq_of_val_isRefinedBy hxtRef
        -- In-bounds and distinctness.
        have hPIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
        have hPIn₂ : pcastOp.InBounds ctx₂.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hIcast hPIn₁
        have hPIn₃ : pcastOp.InBounds ctx₃.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hAdd hPIn₂
        have hPIn₄ : pcastOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hCast hPIn₃
        have hIIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
        have hIIn₃ : icastOp.InBounds ctx₃.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hAdd hIIn₂
        have hIIn₄ : icastOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hCast hIIn₃
        have hAIn₃ : addOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds addOp hAdd
        have hAIn₄ : addOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation addOp) hCast hAIn₃
        have hCIn₄ : castOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds castOp hCast
        have nePI : pcastOp ≠ icastOp := ne_createOp_new hIcast hPIn₁
        have nePA : pcastOp ≠ addOp := ne_createOp_new hAdd hPIn₂
        have nePC : pcastOp ≠ castOp := ne_createOp_new hCast hPIn₃
        have neIA : icastOp ≠ addOp := ne_createOp_new hAdd hIIn₂
        have neIC : icastOp ≠ castOp := ne_createOp_new hCast hIIn₃
        have neAC : addOp ≠ castOp := ne_createOp_new hCast hAIn₃
        -- Field transports into `ctx₄`.
        have hPType : pcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_ne hCast nePC, getOpType!_createOp_ne hAdd nePA,
            getOpType!_createOp_ne hIcast nePI, getOpType!_createOp_self hPcast]
        have hIType : icastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_ne hCast neIC, getOpType!_createOp_ne hAdd neIA,
            getOpType!_createOp_self hIcast]
        have hAType : addOp.getOpType! ctx₄.raw = .riscv .add := by
          rw [getOpType!_createOp_ne hCast neAC, getOpType!_createOp_self hAdd]
        have hCType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_self hCast]
        have hPOperands : pcastOp.getOperands! ctx₄.raw = #[base] := by
          rw [getOperands!_createOp_ne hCast nePC, getOperands!_createOp_ne hAdd nePA,
            getOperands!_createOp_ne hIcast nePI, getOperands!_createOp_self hPcast]
        have hIOperands : icastOp.getOperands! ctx₄.raw = #[idxv] := by
          rw [getOperands!_createOp_ne hCast neIC, getOperands!_createOp_ne hAdd neIA,
            getOperands!_createOp_self hIcast]
        have hAOperands : addOp.getOperands! ctx₄.raw
            = #[ValuePtr.opResult (pcastOp.getResult 0), ValuePtr.opResult (icastOp.getResult 0)] := by
          rw [getOperands!_createOp_ne hCast neAC, getOperands!_createOp_self hAdd]
        have hCOperands : castOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (addOp.getResult 0)] := by
          rw [getOperands!_createOp_self hCast]
        have hPResTypes : pcastOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast nePC, getResultTypes!_createOp_ne hAdd nePA,
            getResultTypes!_createOp_ne hIcast nePI, getResultTypes!_createOp_self hPcast]
        have hIResTypes : icastOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast neIC, getResultTypes!_createOp_ne hAdd neIA,
            getResultTypes!_createOp_self hIcast]
        have hAResTypes : addOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast neAC, getResultTypes!_createOp_self hAdd]
        have hCResTypes : castOp.getResultTypes! ctx₄.raw
            = #[⟨Attribute.llvmPointerType pt, isPt⟩] := by
          rw [getResultTypes!_createOp_self hCast,
            show ((op.getResult 0).get! ctx.raw).type = (⟨Attribute.llvmPointerType pt, isPt⟩ : TypeAttr)
              from Subtype.ext hPtrTy]
        -- Execute the target chain.
        obtain ⟨s₁, hI₁, hMem₁, hRes₁, hOth₁⟩ :=
          interpretOp_castAddrToReg_forward (state := state') (inBounds := hPIn₄)
            hPType hPOperands hPResTypes hbVal'
        obtain ⟨s₂, hI₂, hMem₂, hRes₂, hOth₂⟩ :=
          interpretOp_castToReg_forward (state := s₁) (inBounds := hIIn₄)
            hIType hIOperands hIResTypes (by rw [hOth₁ _ (by grind [ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds])]; exact hiVal')
        have hPRes₂ : s₂.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
            = some (RuntimeValue.reg ⟨BitVec.ofNat 64 a.toNat⟩) := by
          rw [hOth₂ _ (opResult_not_mem_getResults! nePI)]; exact hRes₁
        obtain ⟨s₃, hI₃, hMem₃, hRes₃, hOth₃⟩ :=
          interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := hAIn₄)
            (f := fun r₁ r₂ => Data.RISCV.add r₂ r₁) (fun _ _ _ _ => rfl)
            hAType hAOperands hAResTypes hPRes₂ hRes₂
        obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
          interpretOp_castRegToAddr_forward (state := s₃) (inBounds := hCIn₄)
            hCType hCOperands hCResTypes hRes₃
        refine ⟨s₄, ?_, ?_, ?_⟩
        · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
            Interp]
        · rw [hMem₄, hMem₃, hMem₂, hMem₁, ← memoryRefinement]; exact hMem.symm
        · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.add (LLVM.Int.toReg (Data.LLVM.Int.val bv))
              ⟨BitVec.ofNat 64 a.toNat⟩).val⟩], ?_, ?_⟩
          · simp [hRes₄, Option.bind, Option.map]
          · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
            simp only [RuntimeValue.isRefinedBy, toReg_val_i64]
            rw [gep_scale1_bridge]
      · -- scale = 2: `sh1add idx, ptr`
        peelOpCreation!₂ hpattern ctx₃ addOp hAdd hDomB₂ hDomB₃ hDomI₂ hDomI₃
        peelOpCreation!₂ hpattern ctx₄ castOp hCast hDomB₃ hDomB₄ hDomI₃ hDomI₄
        cleanupHpattern hpattern
        -- Refined operand values in the target state.
        have hbVal' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
          hBaseIn hbVal hDomBase hDomB₄ hBaseNotOp
        obtain ⟨xt, hiVal', hxtRef⟩ := LocalRewritePattern.exists_refined_int_getVar?
          valueRefinement state'Dom hIdxIn hiVal hDomIdx hDomI₄ hIdxNotOp
        obtain rfl : xt = Data.LLVM.Int.val bv := eq_of_val_isRefinedBy hxtRef
        -- In-bounds and distinctness.
        have hPIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
        have hPIn₂ : pcastOp.InBounds ctx₂.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hIcast hPIn₁
        have hPIn₃ : pcastOp.InBounds ctx₃.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hAdd hPIn₂
        have hPIn₄ : pcastOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hCast hPIn₃
        have hIIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
        have hIIn₃ : icastOp.InBounds ctx₃.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hAdd hIIn₂
        have hIIn₄ : icastOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hCast hIIn₃
        have hAIn₃ : addOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds addOp hAdd
        have hAIn₄ : addOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation addOp) hCast hAIn₃
        have hCIn₄ : castOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds castOp hCast
        have nePI : pcastOp ≠ icastOp := ne_createOp_new hIcast hPIn₁
        have nePA : pcastOp ≠ addOp := ne_createOp_new hAdd hPIn₂
        have nePC : pcastOp ≠ castOp := ne_createOp_new hCast hPIn₃
        have neIA : icastOp ≠ addOp := ne_createOp_new hAdd hIIn₂
        have neIC : icastOp ≠ castOp := ne_createOp_new hCast hIIn₃
        have neAC : addOp ≠ castOp := ne_createOp_new hCast hAIn₃
        -- Field transports into `ctx₄`.
        have hPType : pcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_ne hCast nePC, getOpType!_createOp_ne hAdd nePA,
            getOpType!_createOp_ne hIcast nePI, getOpType!_createOp_self hPcast]
        have hIType : icastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_ne hCast neIC, getOpType!_createOp_ne hAdd neIA,
            getOpType!_createOp_self hIcast]
        have hAType : addOp.getOpType! ctx₄.raw = .riscv .sh1add := by
          rw [getOpType!_createOp_ne hCast neAC, getOpType!_createOp_self hAdd]
        have hCType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_self hCast]
        have hPOperands : pcastOp.getOperands! ctx₄.raw = #[base] := by
          rw [getOperands!_createOp_ne hCast nePC, getOperands!_createOp_ne hAdd nePA,
            getOperands!_createOp_ne hIcast nePI, getOperands!_createOp_self hPcast]
        have hIOperands : icastOp.getOperands! ctx₄.raw = #[idxv] := by
          rw [getOperands!_createOp_ne hCast neIC, getOperands!_createOp_ne hAdd neIA,
            getOperands!_createOp_self hIcast]
        have hAOperands : addOp.getOperands! ctx₄.raw
            = #[ValuePtr.opResult (icastOp.getResult 0), ValuePtr.opResult (pcastOp.getResult 0)] := by
          rw [getOperands!_createOp_ne hCast neAC, getOperands!_createOp_self hAdd]
        have hCOperands : castOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (addOp.getResult 0)] := by
          rw [getOperands!_createOp_self hCast]
        have hPResTypes : pcastOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast nePC, getResultTypes!_createOp_ne hAdd nePA,
            getResultTypes!_createOp_ne hIcast nePI, getResultTypes!_createOp_self hPcast]
        have hIResTypes : icastOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast neIC, getResultTypes!_createOp_ne hAdd neIA,
            getResultTypes!_createOp_self hIcast]
        have hAResTypes : addOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast neAC, getResultTypes!_createOp_self hAdd]
        have hCResTypes : castOp.getResultTypes! ctx₄.raw
            = #[⟨Attribute.llvmPointerType pt, isPt⟩] := by
          rw [getResultTypes!_createOp_self hCast,
            show ((op.getResult 0).get! ctx.raw).type = (⟨Attribute.llvmPointerType pt, isPt⟩ : TypeAttr)
              from Subtype.ext hPtrTy]
        -- Execute the target chain.
        obtain ⟨s₁, hI₁, hMem₁, hRes₁, hOth₁⟩ :=
          interpretOp_castAddrToReg_forward (state := state') (inBounds := hPIn₄)
            hPType hPOperands hPResTypes hbVal'
        obtain ⟨s₂, hI₂, hMem₂, hRes₂, hOth₂⟩ :=
          interpretOp_castToReg_forward (state := s₁) (inBounds := hIIn₄)
            hIType hIOperands hIResTypes (by rw [hOth₁ _ (by grind [ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds])]; exact hiVal')
        have hPRes₂ : s₂.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
            = some (RuntimeValue.reg ⟨BitVec.ofNat 64 a.toNat⟩) := by
          rw [hOth₂ _ (opResult_not_mem_getResults! nePI)]; exact hRes₁
        obtain ⟨s₃, hI₃, hMem₃, hRes₃, hOth₃⟩ :=
          interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := hAIn₄)
            (f := fun r₁ r₂ => Data.RISCV.sh1add r₂ r₁) (fun _ _ _ _ => rfl)
            hAType hAOperands hAResTypes hRes₂ hPRes₂
        obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
          interpretOp_castRegToAddr_forward (state := s₃) (inBounds := hCIn₄)
            hCType hCOperands hCResTypes hRes₃
        refine ⟨s₄, ?_, ?_, ?_⟩
        · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
            Interp]
        · rw [hMem₄, hMem₃, hMem₂, hMem₁, ← memoryRefinement]; exact hMem.symm
        · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.sh1add ⟨BitVec.ofNat 64 a.toNat⟩
              (LLVM.Int.toReg (Data.LLVM.Int.val bv))).val⟩], ?_, ?_⟩
          · simp [hRes₄, Option.bind, Option.map]
          · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
            simp only [RuntimeValue.isRefinedBy, toReg_val_i64]
            rw [gep_scale2_bridge]
      · -- scale = 4: `sh2add idx, ptr`
        peelOpCreation!₂ hpattern ctx₃ addOp hAdd hDomB₂ hDomB₃ hDomI₂ hDomI₃
        peelOpCreation!₂ hpattern ctx₄ castOp hCast hDomB₃ hDomB₄ hDomI₃ hDomI₄
        cleanupHpattern hpattern
        -- Refined operand values in the target state.
        have hbVal' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
          hBaseIn hbVal hDomBase hDomB₄ hBaseNotOp
        obtain ⟨xt, hiVal', hxtRef⟩ := LocalRewritePattern.exists_refined_int_getVar?
          valueRefinement state'Dom hIdxIn hiVal hDomIdx hDomI₄ hIdxNotOp
        obtain rfl : xt = Data.LLVM.Int.val bv := eq_of_val_isRefinedBy hxtRef
        -- In-bounds and distinctness.
        have hPIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
        have hPIn₂ : pcastOp.InBounds ctx₂.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hIcast hPIn₁
        have hPIn₃ : pcastOp.InBounds ctx₃.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hAdd hPIn₂
        have hPIn₄ : pcastOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hCast hPIn₃
        have hIIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
        have hIIn₃ : icastOp.InBounds ctx₃.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hAdd hIIn₂
        have hIIn₄ : icastOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hCast hIIn₃
        have hAIn₃ : addOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds addOp hAdd
        have hAIn₄ : addOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation addOp) hCast hAIn₃
        have hCIn₄ : castOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds castOp hCast
        have nePI : pcastOp ≠ icastOp := ne_createOp_new hIcast hPIn₁
        have nePA : pcastOp ≠ addOp := ne_createOp_new hAdd hPIn₂
        have nePC : pcastOp ≠ castOp := ne_createOp_new hCast hPIn₃
        have neIA : icastOp ≠ addOp := ne_createOp_new hAdd hIIn₂
        have neIC : icastOp ≠ castOp := ne_createOp_new hCast hIIn₃
        have neAC : addOp ≠ castOp := ne_createOp_new hCast hAIn₃
        -- Field transports into `ctx₄`.
        have hPType : pcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_ne hCast nePC, getOpType!_createOp_ne hAdd nePA,
            getOpType!_createOp_ne hIcast nePI, getOpType!_createOp_self hPcast]
        have hIType : icastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_ne hCast neIC, getOpType!_createOp_ne hAdd neIA,
            getOpType!_createOp_self hIcast]
        have hAType : addOp.getOpType! ctx₄.raw = .riscv .sh2add := by
          rw [getOpType!_createOp_ne hCast neAC, getOpType!_createOp_self hAdd]
        have hCType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_self hCast]
        have hPOperands : pcastOp.getOperands! ctx₄.raw = #[base] := by
          rw [getOperands!_createOp_ne hCast nePC, getOperands!_createOp_ne hAdd nePA,
            getOperands!_createOp_ne hIcast nePI, getOperands!_createOp_self hPcast]
        have hIOperands : icastOp.getOperands! ctx₄.raw = #[idxv] := by
          rw [getOperands!_createOp_ne hCast neIC, getOperands!_createOp_ne hAdd neIA,
            getOperands!_createOp_self hIcast]
        have hAOperands : addOp.getOperands! ctx₄.raw
            = #[ValuePtr.opResult (icastOp.getResult 0), ValuePtr.opResult (pcastOp.getResult 0)] := by
          rw [getOperands!_createOp_ne hCast neAC, getOperands!_createOp_self hAdd]
        have hCOperands : castOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (addOp.getResult 0)] := by
          rw [getOperands!_createOp_self hCast]
        have hPResTypes : pcastOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast nePC, getResultTypes!_createOp_ne hAdd nePA,
            getResultTypes!_createOp_ne hIcast nePI, getResultTypes!_createOp_self hPcast]
        have hIResTypes : icastOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast neIC, getResultTypes!_createOp_ne hAdd neIA,
            getResultTypes!_createOp_self hIcast]
        have hAResTypes : addOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast neAC, getResultTypes!_createOp_self hAdd]
        have hCResTypes : castOp.getResultTypes! ctx₄.raw
            = #[⟨Attribute.llvmPointerType pt, isPt⟩] := by
          rw [getResultTypes!_createOp_self hCast,
            show ((op.getResult 0).get! ctx.raw).type = (⟨Attribute.llvmPointerType pt, isPt⟩ : TypeAttr)
              from Subtype.ext hPtrTy]
        -- Execute the target chain.
        obtain ⟨s₁, hI₁, hMem₁, hRes₁, hOth₁⟩ :=
          interpretOp_castAddrToReg_forward (state := state') (inBounds := hPIn₄)
            hPType hPOperands hPResTypes hbVal'
        obtain ⟨s₂, hI₂, hMem₂, hRes₂, hOth₂⟩ :=
          interpretOp_castToReg_forward (state := s₁) (inBounds := hIIn₄)
            hIType hIOperands hIResTypes (by rw [hOth₁ _ (by grind [ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds])]; exact hiVal')
        have hPRes₂ : s₂.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
            = some (RuntimeValue.reg ⟨BitVec.ofNat 64 a.toNat⟩) := by
          rw [hOth₂ _ (opResult_not_mem_getResults! nePI)]; exact hRes₁
        obtain ⟨s₃, hI₃, hMem₃, hRes₃, hOth₃⟩ :=
          interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := hAIn₄)
            (f := fun r₁ r₂ => Data.RISCV.sh2add r₂ r₁) (fun _ _ _ _ => rfl)
            hAType hAOperands hAResTypes hRes₂ hPRes₂
        obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
          interpretOp_castRegToAddr_forward (state := s₃) (inBounds := hCIn₄)
            hCType hCOperands hCResTypes hRes₃
        refine ⟨s₄, ?_, ?_, ?_⟩
        · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
            Interp]
        · rw [hMem₄, hMem₃, hMem₂, hMem₁, ← memoryRefinement]; exact hMem.symm
        · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.sh2add ⟨BitVec.ofNat 64 a.toNat⟩
              (LLVM.Int.toReg (Data.LLVM.Int.val bv))).val⟩], ?_, ?_⟩
          · simp [hRes₄, Option.bind, Option.map]
          · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
            simp only [RuntimeValue.isRefinedBy, toReg_val_i64]
            rw [gep_scale4_bridge]
      · -- scale = 8: `sh3add idx, ptr`
        peelOpCreation!₂ hpattern ctx₃ addOp hAdd hDomB₂ hDomB₃ hDomI₂ hDomI₃
        peelOpCreation!₂ hpattern ctx₄ castOp hCast hDomB₃ hDomB₄ hDomI₃ hDomI₄
        cleanupHpattern hpattern
        -- Refined operand values in the target state.
        have hbVal' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
          hBaseIn hbVal hDomBase hDomB₄ hBaseNotOp
        obtain ⟨xt, hiVal', hxtRef⟩ := LocalRewritePattern.exists_refined_int_getVar?
          valueRefinement state'Dom hIdxIn hiVal hDomIdx hDomI₄ hIdxNotOp
        obtain rfl : xt = Data.LLVM.Int.val bv := eq_of_val_isRefinedBy hxtRef
        -- In-bounds and distinctness.
        have hPIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
        have hPIn₂ : pcastOp.InBounds ctx₂.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hIcast hPIn₁
        have hPIn₃ : pcastOp.InBounds ctx₃.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hAdd hPIn₂
        have hPIn₄ : pcastOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hCast hPIn₃
        have hIIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
        have hIIn₃ : icastOp.InBounds ctx₃.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hAdd hIIn₂
        have hIIn₄ : icastOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hCast hIIn₃
        have hAIn₃ : addOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds addOp hAdd
        have hAIn₄ : addOp.InBounds ctx₄.raw :=
          WfRewriter.createOp_inBounds_mono (ptr := .operation addOp) hCast hAIn₃
        have hCIn₄ : castOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds castOp hCast
        have nePI : pcastOp ≠ icastOp := ne_createOp_new hIcast hPIn₁
        have nePA : pcastOp ≠ addOp := ne_createOp_new hAdd hPIn₂
        have nePC : pcastOp ≠ castOp := ne_createOp_new hCast hPIn₃
        have neIA : icastOp ≠ addOp := ne_createOp_new hAdd hIIn₂
        have neIC : icastOp ≠ castOp := ne_createOp_new hCast hIIn₃
        have neAC : addOp ≠ castOp := ne_createOp_new hCast hAIn₃
        -- Field transports into `ctx₄`.
        have hPType : pcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_ne hCast nePC, getOpType!_createOp_ne hAdd nePA,
            getOpType!_createOp_ne hIcast nePI, getOpType!_createOp_self hPcast]
        have hIType : icastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_ne hCast neIC, getOpType!_createOp_ne hAdd neIA,
            getOpType!_createOp_self hIcast]
        have hAType : addOp.getOpType! ctx₄.raw = .riscv .sh3add := by
          rw [getOpType!_createOp_ne hCast neAC, getOpType!_createOp_self hAdd]
        have hCType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
          rw [getOpType!_createOp_self hCast]
        have hPOperands : pcastOp.getOperands! ctx₄.raw = #[base] := by
          rw [getOperands!_createOp_ne hCast nePC, getOperands!_createOp_ne hAdd nePA,
            getOperands!_createOp_ne hIcast nePI, getOperands!_createOp_self hPcast]
        have hIOperands : icastOp.getOperands! ctx₄.raw = #[idxv] := by
          rw [getOperands!_createOp_ne hCast neIC, getOperands!_createOp_ne hAdd neIA,
            getOperands!_createOp_self hIcast]
        have hAOperands : addOp.getOperands! ctx₄.raw
            = #[ValuePtr.opResult (icastOp.getResult 0), ValuePtr.opResult (pcastOp.getResult 0)] := by
          rw [getOperands!_createOp_ne hCast neAC, getOperands!_createOp_self hAdd]
        have hCOperands : castOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (addOp.getResult 0)] := by
          rw [getOperands!_createOp_self hCast]
        have hPResTypes : pcastOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast nePC, getResultTypes!_createOp_ne hAdd nePA,
            getResultTypes!_createOp_ne hIcast nePI, getResultTypes!_createOp_self hPcast]
        have hIResTypes : icastOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast neIC, getResultTypes!_createOp_ne hAdd neIA,
            getResultTypes!_createOp_self hIcast]
        have hAResTypes : addOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
          rw [getResultTypes!_createOp_ne hCast neAC, getResultTypes!_createOp_self hAdd]
        have hCResTypes : castOp.getResultTypes! ctx₄.raw
            = #[⟨Attribute.llvmPointerType pt, isPt⟩] := by
          rw [getResultTypes!_createOp_self hCast,
            show ((op.getResult 0).get! ctx.raw).type = (⟨Attribute.llvmPointerType pt, isPt⟩ : TypeAttr)
              from Subtype.ext hPtrTy]
        -- Execute the target chain.
        obtain ⟨s₁, hI₁, hMem₁, hRes₁, hOth₁⟩ :=
          interpretOp_castAddrToReg_forward (state := state') (inBounds := hPIn₄)
            hPType hPOperands hPResTypes hbVal'
        obtain ⟨s₂, hI₂, hMem₂, hRes₂, hOth₂⟩ :=
          interpretOp_castToReg_forward (state := s₁) (inBounds := hIIn₄)
            hIType hIOperands hIResTypes (by rw [hOth₁ _ (by grind [ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds])]; exact hiVal')
        have hPRes₂ : s₂.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
            = some (RuntimeValue.reg ⟨BitVec.ofNat 64 a.toNat⟩) := by
          rw [hOth₂ _ (opResult_not_mem_getResults! nePI)]; exact hRes₁
        obtain ⟨s₃, hI₃, hMem₃, hRes₃, hOth₃⟩ :=
          interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := hAIn₄)
            (f := fun r₁ r₂ => Data.RISCV.sh3add r₂ r₁) (fun _ _ _ _ => rfl)
            hAType hAOperands hAResTypes hRes₂ hPRes₂
        obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
          interpretOp_castRegToAddr_forward (state := s₃) (inBounds := hCIn₄)
            hCType hCOperands hCResTypes hRes₃
        refine ⟨s₄, ?_, ?_, ?_⟩
        · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift,
            Interp]
        · rw [hMem₄, hMem₃, hMem₂, hMem₁, ← memoryRefinement]; exact hMem.symm
        · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.sh3add ⟨BitVec.ofNat 64 a.toNat⟩
              (LLVM.Int.toReg (Data.LLVM.Int.val bv))).val⟩], ?_, ?_⟩
          · simp [hRes₄, Option.bind, Option.map]
          · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
            simp only [RuntimeValue.isRefinedBy, toReg_val_i64]
            rw [gep_scale8_bridge]
      · split at hpattern
        · -- `scale = 2^k` with `0 < scale` and `k = Nat.log2 scale < 64`: `slli`, `add`.
          rename_i hPow
          obtain ⟨hPos, hAnd, hLog⟩ := hPow
          have hScaleEq : scale = 2 ^ Nat.log2 scale := eq_two_pow_log2 scale (by omega) hAnd
          peelOpCreation!₂ hpattern ctx₃ slliOp hSlli hDomB₂ hDomB₃ hDomI₂ hDomI₃
          peelOpCreation!₂ hpattern ctx₄ addOp hAdd hDomB₃ hDomB₄ hDomI₃ hDomI₄
          peelOpCreation!₂ hpattern ctx₅ castOp hCast hDomB₄ hDomB₅ hDomI₄ hDomI₅
          cleanupHpattern hpattern
          have hbVal' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
            hBaseIn hbVal hDomBase hDomB₅ hBaseNotOp
          obtain ⟨xt, hiVal', hxtRef⟩ := LocalRewritePattern.exists_refined_int_getVar?
            valueRefinement state'Dom hIdxIn hiVal hDomIdx hDomI₅ hIdxNotOp
          obtain rfl : xt = Data.LLVM.Int.val bv := eq_of_val_isRefinedBy hxtRef
          have hPIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
          have hPIn₂ : pcastOp.InBounds ctx₂.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hIcast hPIn₁
          have hPIn₃ : pcastOp.InBounds ctx₃.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hSlli hPIn₂
          have hPIn₄ : pcastOp.InBounds ctx₄.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hAdd hPIn₃
          have hPIn₅ : pcastOp.InBounds ctx₅.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hCast hPIn₄
          have hIIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
          have hIIn₃ : icastOp.InBounds ctx₃.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hSlli hIIn₂
          have hIIn₄ : icastOp.InBounds ctx₄.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hAdd hIIn₃
          have hIIn₅ : icastOp.InBounds ctx₅.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hCast hIIn₄
          have hSIn₃ : slliOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds slliOp hSlli
          have hSIn₄ : slliOp.InBounds ctx₄.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation slliOp) hAdd hSIn₃
          have hSIn₅ : slliOp.InBounds ctx₅.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation slliOp) hCast hSIn₄
          have hAIn₄ : addOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds addOp hAdd
          have hAIn₅ : addOp.InBounds ctx₅.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation addOp) hCast hAIn₄
          have hCIn₅ : castOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds castOp hCast
          have nePI : pcastOp ≠ icastOp := ne_createOp_new hIcast hPIn₁
          have nePS : pcastOp ≠ slliOp := ne_createOp_new hSlli hPIn₂
          have nePA : pcastOp ≠ addOp := ne_createOp_new hAdd hPIn₃
          have nePC : pcastOp ≠ castOp := ne_createOp_new hCast hPIn₄
          have neIS : icastOp ≠ slliOp := ne_createOp_new hSlli hIIn₂
          have neIA : icastOp ≠ addOp := ne_createOp_new hAdd hIIn₃
          have neIC : icastOp ≠ castOp := ne_createOp_new hCast hIIn₄
          have neSA : slliOp ≠ addOp := ne_createOp_new hAdd hSIn₃
          have neSC : slliOp ≠ castOp := ne_createOp_new hCast hSIn₄
          have neAC : addOp ≠ castOp := ne_createOp_new hCast hAIn₄
          have hPType : pcastOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
            rw [getOpType!_createOp_ne hCast nePC, getOpType!_createOp_ne hAdd nePA,
              getOpType!_createOp_ne hSlli nePS, getOpType!_createOp_ne hIcast nePI,
              getOpType!_createOp_self hPcast]
          have hIType : icastOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
            rw [getOpType!_createOp_ne hCast neIC, getOpType!_createOp_ne hAdd neIA,
              getOpType!_createOp_ne hSlli neIS, getOpType!_createOp_self hIcast]
          have hSType : slliOp.getOpType! ctx₅.raw = .riscv .slli := by
            rw [getOpType!_createOp_ne hCast neSC, getOpType!_createOp_ne hAdd neSA,
              getOpType!_createOp_self hSlli]
          have hAType : addOp.getOpType! ctx₅.raw = .riscv .add := by
            rw [getOpType!_createOp_ne hCast neAC, getOpType!_createOp_self hAdd]
          have hCType : castOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
            rw [getOpType!_createOp_self hCast]
          have hPOperands : pcastOp.getOperands! ctx₅.raw = #[base] := by
            rw [getOperands!_createOp_ne hCast nePC, getOperands!_createOp_ne hAdd nePA,
              getOperands!_createOp_ne hSlli nePS, getOperands!_createOp_ne hIcast nePI,
              getOperands!_createOp_self hPcast]
          have hIOperands : icastOp.getOperands! ctx₅.raw = #[idxv] := by
            rw [getOperands!_createOp_ne hCast neIC, getOperands!_createOp_ne hAdd neIA,
              getOperands!_createOp_ne hSlli neIS, getOperands!_createOp_self hIcast]
          have hSOperands : slliOp.getOperands! ctx₅.raw
              = #[ValuePtr.opResult (icastOp.getResult 0)] := by
            rw [getOperands!_createOp_ne hCast neSC, getOperands!_createOp_ne hAdd neSA,
              getOperands!_createOp_self hSlli]
          have hAOperands : addOp.getOperands! ctx₅.raw
              = #[ValuePtr.opResult (pcastOp.getResult 0), ValuePtr.opResult (slliOp.getResult 0)] := by
            rw [getOperands!_createOp_ne hCast neAC, getOperands!_createOp_self hAdd]
          have hCOperands : castOp.getOperands! ctx₅.raw
              = #[ValuePtr.opResult (addOp.getResult 0)] := by
            rw [getOperands!_createOp_self hCast]
          have hSProps : slliOp.getProperties! ctx₅.raw (.riscv .slli)
              = RISCVImmediateProperties.mk
                  (IntegerAttr.mk ((Nat.log2 scale : Nat) : Int) (IntegerType.mk 64)) := by
            rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCast neSC,
              OperationPtr.getProperties!_WfRewriter_createOp_ne hAdd neSA,
              getProperties!_createOp_self hSlli]
          have hPResTypes : pcastOp.getResultTypes! ctx₅.raw
              = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
            rw [getResultTypes!_createOp_ne hCast nePC, getResultTypes!_createOp_ne hAdd nePA,
              getResultTypes!_createOp_ne hSlli nePS, getResultTypes!_createOp_ne hIcast nePI,
              getResultTypes!_createOp_self hPcast]
          have hIResTypes : icastOp.getResultTypes! ctx₅.raw
              = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
            rw [getResultTypes!_createOp_ne hCast neIC, getResultTypes!_createOp_ne hAdd neIA,
              getResultTypes!_createOp_ne hSlli neIS, getResultTypes!_createOp_self hIcast]
          have hSResTypes : slliOp.getResultTypes! ctx₅.raw
              = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
            rw [getResultTypes!_createOp_ne hCast neSC, getResultTypes!_createOp_ne hAdd neSA,
              getResultTypes!_createOp_self hSlli]
          have hAResTypes : addOp.getResultTypes! ctx₅.raw
              = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
            rw [getResultTypes!_createOp_ne hCast neAC, getResultTypes!_createOp_self hAdd]
          have hCResTypes : castOp.getResultTypes! ctx₅.raw
              = #[⟨Attribute.llvmPointerType pt, isPt⟩] := by
            rw [getResultTypes!_createOp_self hCast,
              show ((op.getResult 0).get! ctx.raw).type = (⟨Attribute.llvmPointerType pt, isPt⟩ : TypeAttr)
                from Subtype.ext hPtrTy]
          obtain ⟨s₁, hI₁, hMem₁, hRes₁, hOth₁⟩ :=
            interpretOp_castAddrToReg_forward (state := state') (inBounds := hPIn₅)
              hPType hPOperands hPResTypes hbVal'
          obtain ⟨s₂, hI₂, hMem₂, hRes₂, hOth₂⟩ :=
            interpretOp_castToReg_forward (state := s₁) (inBounds := hIIn₅)
              hIType hIOperands hIResTypes
              (by rw [hOth₁ _ (by grind [ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds])]
                  exact hiVal')
          obtain ⟨s₃, hI₃, hMem₃, hRes₃, hOth₃⟩ :=
            interpretOp_riscv_unaryReg_imm_forward (rop := Riscv.slli) (state := s₂)
              (inBounds := hSIn₅)
              (res := Data.RISCV.slli (BitVec.ofInt 6 ((Nat.log2 scale : Nat) : Int))
                (LLVM.Int.toReg (Data.LLVM.Int.val bv)))
              (props := RISCVImmediateProperties.mk
                (IntegerAttr.mk ((Nat.log2 scale : Nat) : Int) (IntegerType.mk 64)))
              (fun _ _ _ => rfl) hSType hSProps hSOperands hSResTypes hRes₂
          have hPRes₃ : s₃.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
              = some (RuntimeValue.reg ⟨BitVec.ofNat 64 a.toNat⟩) := by
            rw [hOth₃ _ (opResult_not_mem_getResults! nePS),
              hOth₂ _ (opResult_not_mem_getResults! nePI)]
            exact hRes₁
          obtain ⟨s₄, hI₄, hMem₄, hRes₄, hOth₄⟩ :=
            interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := hAIn₅)
              (f := fun r₁ r₂ => Data.RISCV.add r₂ r₁) (fun _ _ _ _ => rfl)
              hAType hAOperands hAResTypes hPRes₃ hRes₃
          obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
            interpretOp_castRegToAddr_forward (state := s₄) (inBounds := hCIn₅)
              hCType hCOperands hCResTypes hRes₄
          refine ⟨s₅, ?_, ?_, ?_⟩
          · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, liftM, monadLift,
              MonadLift.monadLift, Interp]
          · rw [hMem₅, hMem₄, hMem₃, hMem₂, hMem₁, ← memoryRefinement]; exact hMem.symm
          · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.add
                (Data.RISCV.slli (BitVec.ofInt 6 ((Nat.log2 scale : Nat) : Int))
                  (LLVM.Int.toReg (Data.LLVM.Int.val bv))) ⟨BitVec.ofNat 64 a.toNat⟩).val⟩], ?_, ?_⟩
            · simp [hRes₅, Option.bind, Option.map]
            · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
              simp only [RuntimeValue.isRefinedBy, toReg_val_i64]
              rw [gep_pow2_bridge a bv scale (Nat.log2 scale) hLog hScaleEq]
        · -- Any other `scale` (including `0`): `li scale`, `mul idx, scale`, `add ptr, _`.
          peelOpCreation!₂ hpattern ctx₃ liOp hLi hDomB₂ hDomB₃ hDomI₂ hDomI₃
          peelOpCreation!₂ hpattern ctx₄ mulOp hMul hDomB₃ hDomB₄ hDomI₃ hDomI₄
          peelOpCreation!₂ hpattern ctx₅ addOp hAdd hDomB₄ hDomB₅ hDomI₄ hDomI₅
          peelOpCreation!₂ hpattern ctx₆ castOp hCast hDomB₅ hDomB₆ hDomI₅ hDomI₆
          cleanupHpattern hpattern
          have hbVal' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
            hBaseIn hbVal hDomBase hDomB₆ hBaseNotOp
          obtain ⟨xt, hiVal', hxtRef⟩ := LocalRewritePattern.exists_refined_int_getVar?
            valueRefinement state'Dom hIdxIn hiVal hDomIdx hDomI₆ hIdxNotOp
          obtain rfl : xt = Data.LLVM.Int.val bv := eq_of_val_isRefinedBy hxtRef
          have hPIn₁ : pcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds pcastOp hPcast
          have hPIn₂ : pcastOp.InBounds ctx₂.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hIcast hPIn₁
          have hPIn₃ : pcastOp.InBounds ctx₃.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hLi hPIn₂
          have hPIn₄ : pcastOp.InBounds ctx₄.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hMul hPIn₃
          have hPIn₅ : pcastOp.InBounds ctx₅.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hAdd hPIn₄
          have hPIn₆ : pcastOp.InBounds ctx₆.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation pcastOp) hCast hPIn₅
          have hIIn₂ : icastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds icastOp hIcast
          have hIIn₃ : icastOp.InBounds ctx₃.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hLi hIIn₂
          have hIIn₄ : icastOp.InBounds ctx₄.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hMul hIIn₃
          have hIIn₅ : icastOp.InBounds ctx₅.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hAdd hIIn₄
          have hIIn₆ : icastOp.InBounds ctx₆.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation icastOp) hCast hIIn₅
          have hLIn₃ : liOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds liOp hLi
          have hLIn₄ : liOp.InBounds ctx₄.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation liOp) hMul hLIn₃
          have hLIn₅ : liOp.InBounds ctx₅.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation liOp) hAdd hLIn₄
          have hLIn₆ : liOp.InBounds ctx₆.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation liOp) hCast hLIn₅
          have hMIn₄ : mulOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds mulOp hMul
          have hMIn₅ : mulOp.InBounds ctx₅.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation mulOp) hAdd hMIn₄
          have hMIn₆ : mulOp.InBounds ctx₆.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation mulOp) hCast hMIn₅
          have hAIn₅ : addOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds addOp hAdd
          have hAIn₆ : addOp.InBounds ctx₆.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation addOp) hCast hAIn₅
          have hCIn₆ : castOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds castOp hCast
          have nePI : pcastOp ≠ icastOp := ne_createOp_new hIcast hPIn₁
          have nePL : pcastOp ≠ liOp := ne_createOp_new hLi hPIn₂
          have nePM : pcastOp ≠ mulOp := ne_createOp_new hMul hPIn₃
          have nePA : pcastOp ≠ addOp := ne_createOp_new hAdd hPIn₄
          have nePC : pcastOp ≠ castOp := ne_createOp_new hCast hPIn₅
          have neIL : icastOp ≠ liOp := ne_createOp_new hLi hIIn₂
          have neIM : icastOp ≠ mulOp := ne_createOp_new hMul hIIn₃
          have neIA : icastOp ≠ addOp := ne_createOp_new hAdd hIIn₄
          have neIC : icastOp ≠ castOp := ne_createOp_new hCast hIIn₅
          have neLM : liOp ≠ mulOp := ne_createOp_new hMul hLIn₃
          have neLA : liOp ≠ addOp := ne_createOp_new hAdd hLIn₄
          have neLC : liOp ≠ castOp := ne_createOp_new hCast hLIn₅
          have neMA : mulOp ≠ addOp := ne_createOp_new hAdd hMIn₄
          have neMC : mulOp ≠ castOp := ne_createOp_new hCast hMIn₅
          have neAC : addOp ≠ castOp := ne_createOp_new hCast hAIn₅
          have hPType : pcastOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
            rw [getOpType!_createOp_ne hCast nePC, getOpType!_createOp_ne hAdd nePA,
              getOpType!_createOp_ne hMul nePM, getOpType!_createOp_ne hLi nePL,
              getOpType!_createOp_ne hIcast nePI, getOpType!_createOp_self hPcast]
          have hIType : icastOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
            rw [getOpType!_createOp_ne hCast neIC, getOpType!_createOp_ne hAdd neIA,
              getOpType!_createOp_ne hMul neIM, getOpType!_createOp_ne hLi neIL,
              getOpType!_createOp_self hIcast]
          have hLType : liOp.getOpType! ctx₆.raw = .riscv .li := by
            rw [getOpType!_createOp_ne hCast neLC, getOpType!_createOp_ne hAdd neLA,
              getOpType!_createOp_ne hMul neLM, getOpType!_createOp_self hLi]
          have hMType : mulOp.getOpType! ctx₆.raw = .riscv .mul := by
            rw [getOpType!_createOp_ne hCast neMC, getOpType!_createOp_ne hAdd neMA,
              getOpType!_createOp_self hMul]
          have hAType : addOp.getOpType! ctx₆.raw = .riscv .add := by
            rw [getOpType!_createOp_ne hCast neAC, getOpType!_createOp_self hAdd]
          have hCType : castOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
            rw [getOpType!_createOp_self hCast]
          have hPOperands : pcastOp.getOperands! ctx₆.raw = #[base] := by
            rw [getOperands!_createOp_ne hCast nePC, getOperands!_createOp_ne hAdd nePA,
              getOperands!_createOp_ne hMul nePM, getOperands!_createOp_ne hLi nePL,
              getOperands!_createOp_ne hIcast nePI, getOperands!_createOp_self hPcast]
          have hIOperands : icastOp.getOperands! ctx₆.raw = #[idxv] := by
            rw [getOperands!_createOp_ne hCast neIC, getOperands!_createOp_ne hAdd neIA,
              getOperands!_createOp_ne hMul neIM, getOperands!_createOp_ne hLi neIL,
              getOperands!_createOp_self hIcast]
          have hLOperands : liOp.getOperands! ctx₆.raw = #[] := by
            rw [getOperands!_createOp_ne hCast neLC, getOperands!_createOp_ne hAdd neLA,
              getOperands!_createOp_ne hMul neLM, getOperands!_createOp_self hLi]
          have hMOperands : mulOp.getOperands! ctx₆.raw
              = #[ValuePtr.opResult (icastOp.getResult 0), ValuePtr.opResult (liOp.getResult 0)] := by
            rw [getOperands!_createOp_ne hCast neMC, getOperands!_createOp_ne hAdd neMA,
              getOperands!_createOp_self hMul]
          have hAOperands : addOp.getOperands! ctx₆.raw
              = #[ValuePtr.opResult (pcastOp.getResult 0), ValuePtr.opResult (mulOp.getResult 0)] := by
            rw [getOperands!_createOp_ne hCast neAC, getOperands!_createOp_self hAdd]
          have hCOperands : castOp.getOperands! ctx₆.raw
              = #[ValuePtr.opResult (addOp.getResult 0)] := by
            rw [getOperands!_createOp_self hCast]
          have hLProps : liOp.getProperties! ctx₆.raw (.riscv .li)
              = RISCVImmediateProperties.mk (IntegerAttr.mk ((scale : Nat) : Int) (IntegerType.mk 64)) := by
            rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCast neLC,
              OperationPtr.getProperties!_WfRewriter_createOp_ne hAdd neLA,
              OperationPtr.getProperties!_WfRewriter_createOp_ne hMul neLM,
              getProperties!_createOp_self hLi]
          have hPResTypes : pcastOp.getResultTypes! ctx₆.raw
              = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
            rw [getResultTypes!_createOp_ne hCast nePC, getResultTypes!_createOp_ne hAdd nePA,
              getResultTypes!_createOp_ne hMul nePM, getResultTypes!_createOp_ne hLi nePL,
              getResultTypes!_createOp_ne hIcast nePI, getResultTypes!_createOp_self hPcast]
          have hIResTypes : icastOp.getResultTypes! ctx₆.raw
              = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
            rw [getResultTypes!_createOp_ne hCast neIC, getResultTypes!_createOp_ne hAdd neIA,
              getResultTypes!_createOp_ne hMul neIM, getResultTypes!_createOp_ne hLi neIL,
              getResultTypes!_createOp_self hIcast]
          have hLResTypes : liOp.getResultTypes! ctx₆.raw
              = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
            rw [getResultTypes!_createOp_ne hCast neLC, getResultTypes!_createOp_ne hAdd neLA,
              getResultTypes!_createOp_ne hMul neLM, getResultTypes!_createOp_self hLi]
          have hMResTypes : mulOp.getResultTypes! ctx₆.raw
              = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
            rw [getResultTypes!_createOp_ne hCast neMC, getResultTypes!_createOp_ne hAdd neMA,
              getResultTypes!_createOp_self hMul]
          have hAResTypes : addOp.getResultTypes! ctx₆.raw
              = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
            rw [getResultTypes!_createOp_ne hCast neAC, getResultTypes!_createOp_self hAdd]
          have hCResTypes : castOp.getResultTypes! ctx₆.raw
              = #[⟨Attribute.llvmPointerType pt, isPt⟩] := by
            rw [getResultTypes!_createOp_self hCast,
              show ((op.getResult 0).get! ctx.raw).type = (⟨Attribute.llvmPointerType pt, isPt⟩ : TypeAttr)
                from Subtype.ext hPtrTy]
          obtain ⟨s₁, hI₁, hMem₁, hRes₁, hOth₁⟩ :=
            interpretOp_castAddrToReg_forward (state := state') (inBounds := hPIn₆)
              hPType hPOperands hPResTypes hbVal'
          obtain ⟨s₂, hI₂, hMem₂, hRes₂, hOth₂⟩ :=
            interpretOp_castToReg_forward (state := s₁) (inBounds := hIIn₆)
              hIType hIOperands hIResTypes
              (by rw [hOth₁ _ (by grind [ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds])]
                  exact hiVal')
          obtain ⟨s₃, hI₃, hMem₃, hRes₃, hOth₃⟩ :=
            interpretOp_riscv_li_forward (state := s₂) (inBounds := hLIn₆)
              (props := RISCVImmediateProperties.mk
                (IntegerAttr.mk ((scale : Nat) : Int) (IntegerType.mk 64)))
              hLType hLProps hLOperands hLResTypes
          have hIRes₃ : s₃.variables.getVar? (ValuePtr.opResult (icastOp.getResult 0))
              = some (RuntimeValue.reg (LLVM.Int.toReg (Data.LLVM.Int.val bv))) := by
            rw [hOth₃ _ (opResult_not_mem_getResults! neIL)]; exact hRes₂
          obtain ⟨s₄, hI₄, hMem₄, hRes₄, hOth₄⟩ :=
            interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := hMIn₆)
              (f := fun r₁ r₂ => Data.RISCV.mul r₂ r₁) (fun _ _ _ _ => rfl)
              hMType hMOperands hMResTypes hIRes₃ hRes₃
          have hPRes₄ : s₄.variables.getVar? (ValuePtr.opResult (pcastOp.getResult 0))
              = some (RuntimeValue.reg ⟨BitVec.ofNat 64 a.toNat⟩) := by
            rw [hOth₄ _ (opResult_not_mem_getResults! nePM),
              hOth₃ _ (opResult_not_mem_getResults! nePL),
              hOth₂ _ (opResult_not_mem_getResults! nePI)]
            exact hRes₁
          obtain ⟨s₅, hI₅, hMem₅, hRes₅, hOth₅⟩ :=
            interpretOp_riscv_binaryReg_forward (state := s₄) (inBounds := hAIn₆)
              (f := fun r₁ r₂ => Data.RISCV.add r₂ r₁) (fun _ _ _ _ => rfl)
              hAType hAOperands hAResTypes hPRes₄ hRes₄
          obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
            interpretOp_castRegToAddr_forward (state := s₅) (inBounds := hCIn₆)
              hCType hCOperands hCResTypes hRes₅
          refine ⟨s₆, ?_, ?_, ?_⟩
          · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, liftM, monadLift,
              MonadLift.monadLift, Interp]
          · rw [hMem₆, hMem₅, hMem₄, hMem₃, hMem₂, hMem₁, ← memoryRefinement]; exact hMem.symm
          · refine ⟨#[RuntimeValue.addr ⟨(Data.RISCV.add
                (Data.RISCV.mul (Data.RISCV.li (BitVec.ofInt 64 ((scale : Nat) : Int)))
                  (LLVM.Int.toReg (Data.LLVM.Int.val bv))) ⟨BitVec.ofNat 64 a.toNat⟩).val⟩], ?_, ?_⟩
            · simp [hRes₆, Option.bind, Option.map]
            · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
              simp only [RuntimeValue.isRefinedBy, toReg_val_i64]
              rw [gep_general_bridge]

    · simp at hpattern
  all_goals simp at hpattern

end Veir
