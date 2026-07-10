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

  Each `scaleN_bridge` below is the arithmetic core of one branch: the register the sequence
  computes carries exactly the bits of the address the source produces.
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

private theorem getOpType!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getOpType! ctx'.raw = opType := by
  rw [OperationPtr.getOpType!_WfRewriter_createOp h, if_pos rfl]

private theorem getOpType!_createOp_ne {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    o.getOpType! ctx'.raw = o.getOpType! ctx.raw := by
  rw [OperationPtr.getOpType!_WfRewriter_createOp h, if_neg hne]

private theorem getOperands!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getOperands! ctx'.raw = operands := by
  rw [OperationPtr.getOperands!_WfRewriter_createOp h, if_pos rfl]

private theorem getOperands!_createOp_ne {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    o.getOperands! ctx'.raw = o.getOperands! ctx.raw := by
  rw [OperationPtr.getOperands!_WfRewriter_createOp h, if_neg hne]

private theorem getResultTypes!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getResultTypes! ctx'.raw = resultTypes := by
  rw [OperationPtr.getResultTypes!_WfRewriter_createOp h, if_pos rfl]

private theorem getResultTypes!_createOp_ne {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    o.getResultTypes! ctx'.raw = o.getResultTypes! ctx.raw := by
  rw [OperationPtr.getResultTypes!_WfRewriter_createOp h, if_neg hne]

private theorem getProperties!_createOp_self {ctx ctx' : WfIRContext OpCode} {newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) :
    newOp.getProperties! ctx'.raw opType = properties := by
  rw [OperationPtr.getProperties!_WfRewriter_createOp h, if_pos rfl]

private theorem getType!_opResult_createOp_ne {ctx ctx' : WfIRContext OpCode}
    {o newOp : OperationPtr} {i : Nat}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hne : o ≠ newOp) :
    (ValuePtr.opResult (o.getResult i)).getType! ctx'.raw
      = (ValuePtr.opResult (o.getResult i)).getType! ctx.raw := by
  rw [ValuePtr.getType!_WfRewriter_createOp h]
  exact dif_neg (by rintro ⟨hc, -⟩; exact hne hc)

/-- A pre-existing operation is distinct from one `createOp` freshly allocates. -/
private theorem ne_createOp_new {ctx ctx' : WfIRContext OpCode} {o newOp : OperationPtr}
    {opType resultTypes operands blockOperands regions properties insertionPoint hoper hb hr hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hb hr hins = some (ctx', newOp)) (hIn : o.InBounds ctx.raw) :
    o ≠ newOp :=
  fun he => WfRewriter.createOp_new_not_inBounds newOp h (he ▸ hIn)

/-- A distinct operation's result is never among `b`'s results. -/
private theorem opResult_not_mem_getResults! {ctx : IRContext OpCode} {a b : OperationPtr} {i : Nat}
    (hne : a ≠ b) : (ValuePtr.opResult (a.getResult i)) ∉ b.getResults! ctx := by
  rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx
      (ValuePtr.opResult (a.getResult i)) b with hres | ⟨j, hj, heq⟩
  · exact hres
  · exact absurd heq (by grind [OperationPtr.getResult])

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


end Veir
