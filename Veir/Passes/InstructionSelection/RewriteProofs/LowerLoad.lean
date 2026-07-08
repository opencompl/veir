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

namespace Veir

open Veir.Data

/-!
## Correctness of `load_local`

`load_local` lowers `llvm.load %ptr : iX` (`X ∈ {8, 32, 64}`) to
`unrealized_conversion_cast %ptr : !riscv.reg` → `riscv.ld`/`lw`/`lb` (offset 0) →
`unrealized_conversion_cast : iX`.

The mathematical core is a *memory bridge*: reading the same bytes from the same memory with the
RISC-V load refines the LLVM load (poison memory → LLVM poison, which refines the concrete RISC-V
value; otherwise the two decoders agree). It is stated purely on `MemoryState`/`riscvLoad`, one per
width. The `i8`/`i64` byte-decode facts route through the `ForLean` `toBitVecLE_one`/`toBitVecLE_eight`
lemmas; `i32` needs none (both sides decode `toBitVecLE 4`, and `bv_decide` closes the round trip).
-/

set_option maxHeartbeats 1000000

/-- Memory bridge for the `i64` `load` (`riscv.ld`, zero-extend). -/
theorem llvmLoad_i64_bridge (mem : MemoryState) (addr : UInt64) (hz : ¬ addr.toNat = 0)
    (v : RuntimeValue) (hv : mem.llvmLoad addr ⟨.integerType ⟨64⟩, rfl⟩ = some (.ok v)) :
    ∃ bits, riscvLoad mem (riscvEffectiveAddr (BitVec.ofNat 64 addr.toNat) 0) 8 .zeroExt
        = some (.ok (bits, mem)) ∧
      v ⊒ RuntimeValue.int 64 (RISCV.Reg.toInt (Data.RISCV.Reg.mk bits) 64) := by
  have haddr0 : (addr == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro hh; exact hz (by rw [hh]; rfl)
  have hib : addr.toNat + 8 ≤ mem.contents.size := by
    have hv' := hv
    clear hv
    simp only [MemoryState.llvmLoad, MemoryState.load, bind, Interp.ub] at hv'
    split at hv' <;> (try split at hv') <;> grind
  have headdr : riscvEffectiveAddr (BitVec.ofNat 64 addr.toNat) 0 = BitVec.ofNat 64 addr.toNat := by
    simp only [riscvEffectiveAddr]; bv_decide
  have haddrN : (BitVec.ofNat 64 addr.toNat).toNat = addr.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt addr.toNat_lt
  have hens : mem.ensureSize (addr.toNat + 8) = mem := by
    simp only [MemoryState.ensureSize]; rw [if_neg (by omega)]
  have haddrU : addr.toNat.toUInt64 = addr := by simp
  refine ⟨((mem.contents.extract addr.toNat (addr + Nat.toUInt64 8).toNat).toBitVecLE 8).setWidth 64,
      ?_, ?_⟩
  · simp only [riscvLoad, headdr, haddrN, haddrU, hens, MemoryState.load, bind, pure,
      show (Nat.toUInt64 8).toNat = 8 from rfl]
    rw [if_pos (show addr.toNat + 8 ≤ mem.contents.size from hib)]
  · simp only [MemoryState.llvmLoad, haddr0, MemoryState.load, bind, pure,
      show UInt64.toNat 8 = 8 from rfl, Bool.false_eq_true, if_false,
      if_pos (show addr.toNat + 8 ≤ mem.contents.size from hib),
      show (Nat.toUInt64 8) = (8 : UInt64) from rfl] at hv ⊢
    split at hv
    · simp only [Interp, reduceCtorEq] at hv
    · simp only [Interp, Option.some.injEq, reduceCtorEq] at hv
    · split at hv
      · simp only [Interp, Option.some.injEq, UBOr.ok.injEq] at hv
        subst hv
        refine ⟨rfl, ?_⟩
        rw [Data.LLVM.Int.cast_self, Data.LLVM.Int.isRefinedBy_iff]
        refine ⟨fun h => ?_, fun h _ => ?_⟩ <;>
          simp only [Data.LLVM.Int.isPoison_of_poison, reduceCtorEq] at h
      · simp only [Interp, Option.some.injEq, UBOr.ok.injEq] at hv
        subst hv
        refine ⟨rfl, ?_⟩
        rw [Data.LLVM.Int.cast_self, ByteArray.toBitVecLE_eight, Data.LLVM.Int.isRefinedBy_iff]
        refine ⟨fun _ => rfl, fun _ _ => ?_⟩
        simp only [RISCV.Reg.toInt, Data.LLVM.Int.getValue]
        bv_decide

/-- Memory bridge for the `i32` `load` (`riscv.lw`, sign-extend). No byte-decode lemma is needed:
    both sides decode `toBitVecLE 4`, and `bv_decide` closes the sign-extend/truncate round trip. -/
theorem llvmLoad_i32_bridge (mem : MemoryState) (addr : UInt64) (hz : ¬ addr.toNat = 0)
    (v : RuntimeValue) (hv : mem.llvmLoad addr ⟨.integerType ⟨32⟩, rfl⟩ = some (.ok v)) :
    ∃ bits, riscvLoad mem (riscvEffectiveAddr (BitVec.ofNat 64 addr.toNat) 0) 4 .signExt
        = some (.ok (bits, mem)) ∧
      v ⊒ RuntimeValue.int 32 (RISCV.Reg.toInt (Data.RISCV.Reg.mk bits) 32) := by
  have haddr0 : (addr == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro hh; exact hz (by rw [hh]; rfl)
  have hib : addr.toNat + 4 ≤ mem.contents.size := by
    have hv' := hv
    clear hv
    simp only [MemoryState.llvmLoad, MemoryState.load, bind, Interp.ub] at hv'
    split at hv' <;> (try split at hv') <;> grind
  have headdr : riscvEffectiveAddr (BitVec.ofNat 64 addr.toNat) 0 = BitVec.ofNat 64 addr.toNat := by
    simp only [riscvEffectiveAddr]; bv_decide
  have haddrN : (BitVec.ofNat 64 addr.toNat).toNat = addr.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt addr.toNat_lt
  have hens : mem.ensureSize (addr.toNat + 4) = mem := by
    simp only [MemoryState.ensureSize]; rw [if_neg (by omega)]
  have haddrU : addr.toNat.toUInt64 = addr := by simp
  refine ⟨(mem.contents.extract addr.toNat (addr + Nat.toUInt64 4).toNat).toBitVecLE 4 |>.signExtend 64,
      ?_, ?_⟩
  · simp only [riscvLoad, headdr, haddrN, haddrU, hens, MemoryState.load, bind, pure,
      show (Nat.toUInt64 4).toNat = 4 from rfl]
    rw [if_pos (show addr.toNat + 4 ≤ mem.contents.size from hib)]
  · simp only [MemoryState.llvmLoad, haddr0, MemoryState.load, bind, pure,
      show UInt64.toNat 4 = 4 from rfl, Bool.false_eq_true, if_false,
      if_pos (show addr.toNat + 4 ≤ mem.contents.size from hib),
      show (Nat.toUInt64 4) = (4 : UInt64) from rfl] at hv ⊢
    split at hv
    · simp only [Interp, reduceCtorEq] at hv
    · simp only [Interp, Option.some.injEq, reduceCtorEq] at hv
    · split at hv
      · simp only [Interp, Option.some.injEq, UBOr.ok.injEq] at hv
        subst hv
        refine ⟨rfl, ?_⟩
        rw [Data.LLVM.Int.cast_self, Data.LLVM.Int.isRefinedBy_iff]
        refine ⟨fun h => ?_, fun h _ => ?_⟩ <;>
          simp only [Data.LLVM.Int.isPoison_of_poison, reduceCtorEq] at h
      · simp only [Interp, Option.some.injEq, UBOr.ok.injEq] at hv
        subst hv
        refine ⟨rfl, ?_⟩
        rw [Data.LLVM.Int.cast_self, Data.LLVM.Int.isRefinedBy_iff]
        refine ⟨fun _ => rfl, fun _ _ => ?_⟩
        simp only [RISCV.Reg.toInt, Data.LLVM.Int.getValue]
        bv_decide

/-- Memory bridge for the `i8` `load` (`riscv.lb`, sign-extend). -/
theorem llvmLoad_i8_bridge (mem : MemoryState) (addr : UInt64) (hz : ¬ addr.toNat = 0)
    (v : RuntimeValue) (hv : mem.llvmLoad addr ⟨.integerType ⟨8⟩, rfl⟩ = some (.ok v)) :
    ∃ bits, riscvLoad mem (riscvEffectiveAddr (BitVec.ofNat 64 addr.toNat) 0) 1 .signExt
        = some (.ok (bits, mem)) ∧
      v ⊒ RuntimeValue.int 8 (RISCV.Reg.toInt (Data.RISCV.Reg.mk bits) 8) := by
  have haddr0 : (addr == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro hh; exact hz (by rw [hh]; rfl)
  have hib : addr.toNat + 1 ≤ mem.contents.size := by
    have hv' := hv
    clear hv
    simp only [MemoryState.llvmLoad, MemoryState.load, bind, Interp.ub] at hv'
    split at hv' <;> (try split at hv') <;> grind
  have headdr : riscvEffectiveAddr (BitVec.ofNat 64 addr.toNat) 0 = BitVec.ofNat 64 addr.toNat := by
    simp only [riscvEffectiveAddr]; bv_decide
  have haddrN : (BitVec.ofNat 64 addr.toNat).toNat = addr.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt addr.toNat_lt
  have hens : mem.ensureSize (addr.toNat + 1) = mem := by
    simp only [MemoryState.ensureSize]; rw [if_neg (by omega)]
  have haddrU : addr.toNat.toUInt64 = addr := by simp
  refine ⟨(mem.contents.extract addr.toNat (addr + Nat.toUInt64 1).toNat).toBitVecLE 1 |>.signExtend 64,
      ?_, ?_⟩
  · simp only [riscvLoad, headdr, haddrN, haddrU, hens, MemoryState.load, bind, pure,
      show (Nat.toUInt64 1).toNat = 1 from rfl]
    rw [if_pos (show addr.toNat + 1 ≤ mem.contents.size from hib)]
  · simp only [MemoryState.llvmLoad, haddr0, MemoryState.load, bind, pure,
      show UInt64.toNat 1 = 1 from rfl, Bool.false_eq_true, if_false,
      if_pos (show addr.toNat + 1 ≤ mem.contents.size from hib),
      show (Nat.toUInt64 1) = (1 : UInt64) from rfl] at hv ⊢
    split at hv
    · simp only [Interp, reduceCtorEq] at hv
    · simp only [Interp, Option.some.injEq, reduceCtorEq] at hv
    · split at hv
      · simp only [Interp, Option.some.injEq, UBOr.ok.injEq] at hv
        subst hv
        refine ⟨rfl, ?_⟩
        rw [Data.LLVM.Int.cast_self, Data.LLVM.Int.isRefinedBy_iff]
        refine ⟨fun h => ?_, fun h _ => ?_⟩ <;>
          simp only [Data.LLVM.Int.isPoison_of_poison, reduceCtorEq] at h
      · simp only [Interp, Option.some.injEq, UBOr.ok.injEq] at hv
        subst hv
        refine ⟨rfl, ?_⟩
        rw [Data.LLVM.Int.cast_self, ByteArray.toBitVecLE_one, Data.LLVM.Int.isRefinedBy_iff]
        refine ⟨fun _ => rfl, fun _ _ => ?_⟩
        simp only [RISCV.Reg.toInt, Data.LLVM.Int.getValue]
        bv_decide

/-!
## Forward interpretation lemmas for `load`
-/

/-- Pointer-cast forward lemma: a `builtin.unrealized_conversion_cast` with a single pointer
operand `.addr a` and a `!riscv.reg` result binds the result to `.reg ⟨ofNat 64 a.toNat⟩` (the
address bits), leaving memory and every non-result variable unchanged. -/
theorem interpretOp_castAddrToReg_forward
    {ctx : WfIRContext OpCode} {castOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : castOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {a : UInt64}
    (hType : castOp.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hOperands : castOp.getOperands! ctx.raw = #[v])
    (hResTypes : castOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.addr a)) :
    ∃ state', interpretOp castOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (.reg ⟨BitVec.ofNat 64 a.toNat⟩) ∧
      (∀ v', v' ∉ castOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVar⟩ :=
    interpretOp_forward (op := castOp) (state := state) (inBounds := inBounds)
      (vals := #[.addr a]) (results := #[.reg ⟨BitVec.ofNat 64 a.toNat⟩]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [hResTypes, interpretOp', pure, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- RISC-V load forward lemma: a `riscv.ld`/`lw`/`lb` op whose interpretation on the current memory
loads `bits` and leaves memory unchanged (hypothesis `hSem`, supplied by a memory bridge) binds the
result to `.reg (.mk bits)`, leaving memory and every non-result variable unchanged. -/
theorem interpretOp_riscv_load_forward
    {ctx : WfIRContext OpCode} {rop : Riscv} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {addrReg : Data.RISCV.Reg} {bits : BitVec 64}
    (hSem : Riscv.interpretOp' rop (theOp.getProperties! ctx.raw (.riscv rop))
        (theOp.getResultTypes! ctx.raw) #[.reg addrReg] (theOp.getSuccessors! ctx.raw) state.memory
          = some (.ok (#[.reg (Data.RISCV.Reg.mk bits)], state.memory, none)))
    (hType : theOp.getOpType! ctx.raw = .riscv rop)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg addrReg)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (Data.RISCV.Reg.mk bits)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVar⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg addrReg]) (results := #[.reg (Data.RISCV.Reg.mk bits)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simpa only [interpretOp'] using hSem)
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Unfold the interpretation of a matched `llvm.load`: from a successful `interpretOp` we read the
pointer operand's address value `.addr a` (forced by the `.load` interpreter arm), the single result
type `type`, and the loaded value `loadedVal = llvmLoad a type`, with memory unchanged and no control
flow. -/
theorem matchLoad_interpretOp_unfold {ctx : WfIRContext OpCode}
    {op : OperationPtr} {ptr : ValuePtr}
    {state : InterpreterState ctx} {newState cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm .load)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[ptr])
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ a type loadedVal,
      op.getResultTypes! ctx.raw = #[type] ∧
      state.variables.getVar? ptr = some (.addr a) ∧
      state.memory.llvmLoad a type = some (.ok loadedVal) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) = some loadedVal ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 1 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hOperandEq : ptr = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  -- Read the operand value.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨ptrVal, hptrVal⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize
  have hgetVar : state.variables.getVar? ptr = some ptrVal := by
    rw [hOperandEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hptrVal
  have hOperand0 : op.getOperand! ctx.raw 0 = ptr := by
    rw [hOperandEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op = some #[ptrVal] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    obtain rfl : i = 0 := by omega
    simpa [hOperand0] using hgetVar
  -- The result-type array is a singleton.
  have hRTsize : (op.getResultTypes! ctx.raw).size = 1 := by
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!]; omega
  obtain ⟨type, hTypeL⟩ : ∃ type, (op.getResultTypes! ctx.raw).toList = [type] :=
    List.length_eq_one_iff.mp (by rw [Array.length_toList]; exact hRTsize)
  have hType : op.getResultTypes! ctx.raw = #[type] := by
    apply Array.toList_inj.mp; rw [hTypeL]
  -- Unfold `.load`.
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Llvm.interpretOp', hType, List.toList_toArray, bind, pure] at hInterp'
  -- Force `ptrVal = .addr a` (the only arm that can succeed) and extract `loadedVal`.
  split at hInterp'
  next a heq =>
    obtain rfl : ptrVal = .addr a := by simpa using heq
    cases hL : state.memory.llvmLoad a type with
    | none => rw [hL] at hInterp'; simp [Interp] at hInterp'
    | some ubor =>
      cases ubor with
      | ub => rw [hL] at hInterp'; simp [Interp] at hInterp'
      | ok loadedVal =>
        rw [hL] at hInterp'
        simp only [Interp, Option.some.injEq, UBOr.ok.injEq, Prod.mk.injEq] at hInterp'
        obtain ⟨rfl, rfl, rfl⟩ := hInterp'
        subst hNew
        refine ⟨a, type, loadedVal, hType, hgetVar, hL, rfl, ?_, rfl⟩
        rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
        simp
  next heq => simp [Interp] at hInterp'

/-- Read a refined *pointer* operand in a `PreservesSemantics` proof (the address analogue of
`LocalRewritePattern.exists_refined_int_getVar?`): since an address refines only the identical
address, the target state holds the same `.addr a`. -/
theorem LocalRewritePattern.exists_refined_addr_getVar?
    {ctx : WfIRContext OpCode}
    {ipIn : ip.InBounds ctx.raw}
    {pattern : LocalRewritePattern OpCode}
    {hpattern : pattern ctx op = some (newCtx, some (newOps, newValues))}
    {hreturn : pattern.ReturnValuesInBounds} {hreturn₂ : pattern.ReturnValues}
    {hreturn₃ : pattern.ReturnCtxChanges}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx} {a : UInt64}
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpattern hreturn hreturn₂ hreturn₃) (.at ip) (.at ip) ipIn ipIn')
    (state'Dom : state'.DefinesDominating ip ipIn')
    (vIn : v.InBounds ctx.raw)
    (hxVal : state.variables.getVar? v = some (RuntimeValue.addr a))
    (hDomCtx : v.dominatesIp ip ctx) (hDom' : v.dominatesIp ip newCtx)
    (hNotRes : v ∉ op.getResults! ctx.raw) :
    state'.variables.getVar? v = some (RuntimeValue.addr a) := by
  have ⟨tv, hTv⟩ := InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp state'Dom
      (hreturn₃.valuePtr_inBounds hpattern vIn) hDom'
  have hRef : RuntimeValue.addr a ⊒ tv := by
    grind [LocalRewritePattern.mapping, valueRefinement v]
  grind [RuntimeValue.addr_of_isRefinedBy hRef]

/-- Execute the three-op target chain `[pcastOp, ldOp, castOp]` (pointer cast → RISC-V load →
cast-back) and assemble the simulation triple, given the structural facts about the created ops, the
refined pointer value, the RISC-V-load semantics `hSem` (from a memory bridge), and the data
refinement `hRefine`. Shared by all three width branches of `load_local_preservesSemantics`. -/
theorem load_execute_chain {ctx₃ : WfIRContext OpCode}
    {pcastOp ldOp castOp : OperationPtr} {state' : InterpreterState ctx₃}
    {ptr : ValuePtr} {a : UInt64} {loadedVal : RuntimeValue} {bw : Nat} {rop : Riscv}
    {bits : BitVec 64} {hIsReg hIsReg' hIsInt}
    (hPcastIn : pcastOp.InBounds ctx₃.raw) (hLdIn : ldOp.InBounds ctx₃.raw)
    (hCastIn : castOp.InBounds ctx₃.raw)
    (hPcastType : pcastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast)
    (hPcastOperands : pcastOp.getOperands! ctx₃.raw = #[ptr])
    (hPcastResTypes : pcastOp.getResultTypes! ctx₃.raw = #[⟨.registerType ⟨none⟩, hIsReg⟩])
    (hLdType : ldOp.getOpType! ctx₃.raw = .riscv rop)
    (hLdOperands : ldOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (pcastOp.getResult 0)])
    (hLdResTypes : ldOp.getResultTypes! ctx₃.raw = #[⟨.registerType ⟨none⟩, hIsReg'⟩])
    (hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast)
    (hCastOperands : castOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (ldOp.getResult 0)])
    (hCastResTypes : castOp.getResultTypes! ctx₃.raw = #[⟨.integerType ⟨bw⟩, hIsInt⟩])
    (hPtrVal' : state'.variables.getVar? ptr = some (.addr a))
    (hSem : Riscv.interpretOp' rop (ldOp.getProperties! ctx₃.raw (.riscv rop))
        (ldOp.getResultTypes! ctx₃.raw) #[.reg ⟨BitVec.ofNat 64 a.toNat⟩] (ldOp.getSuccessors! ctx₃.raw)
        state'.memory = some (.ok (#[.reg (Data.RISCV.Reg.mk bits)], state'.memory, none)))
    (hRefine : loadedVal ⊒ RuntimeValue.int bw (RISCV.Reg.toInt (Data.RISCV.Reg.mk bits) bw)) :
    ∃ newState', interpretOpList [pcastOp, ldOp, castOp] state'
        (by intro o ho; simp at ho; rcases ho with rfl | rfl | rfl <;> assumption)
        = some (.ok (newState', none)) ∧
      state'.memory = newState'.memory ∧
      ∃ targetValues,
        (#[ValuePtr.opResult (castOp.getResult 0)]).mapM (newState'.variables.getVar? ·)
          = some targetValues ∧
        #[loadedVal] ⊒ targetValues := by
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castAddrToReg_forward (state := state') (inBounds := hPcastIn)
      hPcastType hPcastOperands hPcastResTypes hPtrVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_riscv_load_forward (state := s₁) (inBounds := hLdIn) (bits := bits)
      (hMem₁ ▸ hSem) hLdType hLdOperands hLdResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := hCastIn)
      hCastType hCastOperands hCastResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, Interp]
  · refine ⟨#[RuntimeValue.int bw (RISCV.Reg.toInt (Data.RISCV.Reg.mk bits) bw)], ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr hRefine

/-!
## Correctness of `load_local`
-/

set_option maxHeartbeats 4000000 in
theorem load_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps load_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges load_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds load_local}
    {h₄ : LocalRewritePattern.ReturnValues load_local} :
    LocalRewritePattern.PreservesSemantics load_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, load_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp only [bind, pure] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchLoad op ctx.raw).isSome := by
    cases hM : matchLoad op ctx.raw with
    | some _ => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨ptr, lprops⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨hOpType, hNumResults, hOperands, _⟩ := matchLoad_implies hMatch
  -- Unfold the source interpretation: pointer value `.addr a`, result type, loaded value.
  obtain ⟨a, srcType, loadedVal, hRT, hPtrVal, hLoad, hMem, hRes, hCf⟩ :=
    matchLoad_interpretOp_unfold opInBounds hOpType hNumResults hOperands hinterp
  subst hCf
  have hSrcType : srcType = ((op.getResult 0).get! ctx.raw).type := by
    have hE := OperationPtr.getResultTypes!.getElem!_eq (ctx := ctx.raw) (op := op) (index := 0)
      (by omega)
    rw [hRT] at hE; simpa using hE
  -- The matched operand dominates the rewrite point.
  have hDomCtx : ptr.dominatesIp (InsertPoint.before op) ctx := by
    have : ptr ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
    grind [WfIRContext.Dom.operand_dominates_op]
  have vNotOp : ptr ∉ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the result-type guard: `type.val` must be an integer type.
  rw [← hSrcType] at hpattern
  split at hpattern
  · rename_i intType hStv
    -- Peel the bitwidth guard.
    peelSplittableCondition [hBw] hpattern
    -- Source value: `op`'s single result is `loadedVal`.
    rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
      at hsourceValues
    simp at hsourceValues
    simp [hRes] at hsourceValues
    subst sourceValues
    -- The pointer is non-null (else the source load would be UB).
    have hz : ¬ a.toNat = 0 := by
      intro h0
      rw [show a = 0 from UInt64.toNat_inj.mp (by simp [h0])] at hLoad
      simp [MemoryState.llvmLoad, Interp.ub, Interp] at hLoad
    -- Peel the pointer cast (shared across widths).
    peelOpCreation! hpattern ctx₁ pcastOp hPcast hDomCtx hDom₁
    have hBwCases : intType.bitwidth = 8 ∨ intType.bitwidth = 32 ∨ intType.bitwidth = 64 := by omega
    rcases hBwCases with hbw | hbw | hbw
    · -- i8 (`riscv.lb`)
      rw [if_pos hbw] at hpattern
      peelOpCreation! hpattern ctx₂ ldOp hLd hDom₁ hDom₂
      peelOpCreation! hpattern ctx₃ castOp hCast hDom₂ hDom₃
      cleanupHpattern hpattern
      have hPtrVal' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
        (by grind) hPtrVal hDomCtx hDom₃ vNotOp
      have hPcastType : pcastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
      have hLdType : ldOp.getOpType! ctx₃.raw = .riscv .lb := by grind
      have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
      have hPcastOperands : pcastOp.getOperands! ctx₃.raw = #[ptr] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hPcast (operation := pcastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hLd (operation := pcastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := pcastOp)]
      have hLdOperands : ldOp.getOperands! ctx₃.raw
          = #[ValuePtr.opResult (pcastOp.getResult 0)] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hLd (operation := ldOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := ldOp)]
      have hCastOperands : castOp.getOperands! ctx₃.raw
          = #[ValuePtr.opResult (ldOp.getResult 0)] := by grind
      have hPcastResTypes : pcastOp.getResultTypes! ctx₃.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hPcast (operation := pcastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hLd (operation := pcastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := pcastOp)]
      have hLdResTypes : ldOp.getResultTypes! ctx₃.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLd (operation := ldOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := ldOp)]
      have hCastResTypes : castOp.getResultTypes! ctx₃.raw = #[srcType] := by grind
      have hLdProps : ldOp.getProperties! ctx₃.raw (.riscv .lb)
          = { value := ⟨0, ⟨64⟩⟩ } := by
        grind [OperationPtr.getProperties!_WfRewriter_createOp hLd (operation := ldOp),
          OperationPtr.getProperties!_WfRewriter_createOp_ne hCast]
      have hbw' : intType = ⟨8⟩ := by obtain ⟨w⟩ := intType; simp_all
      have hSrcTypeE : srcType = ⟨.integerType ⟨8⟩, rfl⟩ := by
        apply Subtype.ext; rw [hStv, hbw']
      rw [hSrcTypeE] at hLoad
      obtain ⟨bits, hRiscvLoad, hRefine⟩ :=
        llvmLoad_i8_bridge state.memory a hz loadedVal hLoad
      have hSem : Riscv.interpretOp' .lb (ldOp.getProperties! ctx₃.raw (.riscv .lb))
          (ldOp.getResultTypes! ctx₃.raw) #[.reg ⟨BitVec.ofNat 64 a.toNat⟩]
          (ldOp.getSuccessors! ctx₃.raw) state'.memory
            = some (.ok (#[.reg (Data.RISCV.Reg.mk bits)], state'.memory, none)) := by
        rw [← memoryRefinement, hLdProps]
        simp only [Riscv.interpretOp', bind, pure]
        rw [hRiscvLoad]
      obtain ⟨ns', hIL, hMemEq, tv, htvMap, htvRef⟩ :=
        load_execute_chain (by grind) (by grind) (by grind)
          hPcastType hPcastOperands hPcastResTypes hLdType hLdOperands hLdResTypes
          hCastType hCastOperands (hCastResTypes.trans (by rw [hSrcTypeE])) hPtrVal' hSem
          hRefine
      refine ⟨ns', ?_, by grind, tv, htvMap, htvRef⟩
      simpa only [liftM, monadLift, MonadLift.monadLift] using hIL
    · -- i32 (`riscv.lw`)
      rw [if_neg (by omega), if_pos hbw] at hpattern
      peelOpCreation! hpattern ctx₂ ldOp hLd hDom₁ hDom₂
      peelOpCreation! hpattern ctx₃ castOp hCast hDom₂ hDom₃
      cleanupHpattern hpattern
      have hPtrVal' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
        (by grind) hPtrVal hDomCtx hDom₃ vNotOp
      have hPcastType : pcastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
      have hLdType : ldOp.getOpType! ctx₃.raw = .riscv .lw := by grind
      have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
      have hPcastOperands : pcastOp.getOperands! ctx₃.raw = #[ptr] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hPcast (operation := pcastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hLd (operation := pcastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := pcastOp)]
      have hLdOperands : ldOp.getOperands! ctx₃.raw
          = #[ValuePtr.opResult (pcastOp.getResult 0)] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hLd (operation := ldOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := ldOp)]
      have hCastOperands : castOp.getOperands! ctx₃.raw
          = #[ValuePtr.opResult (ldOp.getResult 0)] := by grind
      have hPcastResTypes : pcastOp.getResultTypes! ctx₃.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hPcast (operation := pcastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hLd (operation := pcastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := pcastOp)]
      have hLdResTypes : ldOp.getResultTypes! ctx₃.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLd (operation := ldOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := ldOp)]
      have hCastResTypes : castOp.getResultTypes! ctx₃.raw = #[srcType] := by grind
      have hLdProps : ldOp.getProperties! ctx₃.raw (.riscv .lw)
          = { value := ⟨0, ⟨64⟩⟩ } := by
        grind [OperationPtr.getProperties!_WfRewriter_createOp hLd (operation := ldOp),
          OperationPtr.getProperties!_WfRewriter_createOp_ne hCast]
      have hbw' : intType = ⟨32⟩ := by obtain ⟨w⟩ := intType; simp_all
      have hSrcTypeE : srcType = ⟨.integerType ⟨32⟩, rfl⟩ := by
        apply Subtype.ext; rw [hStv, hbw']
      rw [hSrcTypeE] at hLoad
      obtain ⟨bits, hRiscvLoad, hRefine⟩ :=
        llvmLoad_i32_bridge state.memory a hz loadedVal hLoad
      have hSem : Riscv.interpretOp' .lw (ldOp.getProperties! ctx₃.raw (.riscv .lw))
          (ldOp.getResultTypes! ctx₃.raw) #[.reg ⟨BitVec.ofNat 64 a.toNat⟩]
          (ldOp.getSuccessors! ctx₃.raw) state'.memory
            = some (.ok (#[.reg (Data.RISCV.Reg.mk bits)], state'.memory, none)) := by
        rw [← memoryRefinement, hLdProps]
        simp only [Riscv.interpretOp', bind, pure]
        rw [hRiscvLoad]
      obtain ⟨ns', hIL, hMemEq, tv, htvMap, htvRef⟩ :=
        load_execute_chain (by grind) (by grind) (by grind)
          hPcastType hPcastOperands hPcastResTypes hLdType hLdOperands hLdResTypes
          hCastType hCastOperands (hCastResTypes.trans (by rw [hSrcTypeE])) hPtrVal' hSem
          hRefine
      refine ⟨ns', ?_, by grind, tv, htvMap, htvRef⟩
      simpa only [liftM, monadLift, MonadLift.monadLift] using hIL
    · -- i64 (`riscv.ld`)
      rw [if_neg (by omega), if_neg (by omega)] at hpattern
      peelOpCreation! hpattern ctx₂ ldOp hLd hDom₁ hDom₂
      peelOpCreation! hpattern ctx₃ castOp hCast hDom₂ hDom₃
      cleanupHpattern hpattern
      -- Read the refined pointer in the target state.
      have hPtrVal' := LocalRewritePattern.exists_refined_addr_getVar? valueRefinement state'Dom
        (by grind) hPtrVal hDomCtx hDom₃ vNotOp
      -- Structural facts about the three created ops.
      have hPcastType : pcastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
      have hLdType : ldOp.getOpType! ctx₃.raw = .riscv .ld := by grind
      have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
      have hPcastOperands : pcastOp.getOperands! ctx₃.raw = #[ptr] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hPcast (operation := pcastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hLd (operation := pcastOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := pcastOp)]
      have hLdOperands : ldOp.getOperands! ctx₃.raw
          = #[ValuePtr.opResult (pcastOp.getResult 0)] := by
        grind [OperationPtr.getOperands!_WfRewriter_createOp hLd (operation := ldOp),
          OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := ldOp)]
      have hCastOperands : castOp.getOperands! ctx₃.raw
          = #[ValuePtr.opResult (ldOp.getResult 0)] := by grind
      have hPcastResTypes : pcastOp.getResultTypes! ctx₃.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hPcast (operation := pcastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hLd (operation := pcastOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := pcastOp)]
      have hLdResTypes : ldOp.getResultTypes! ctx₃.raw
          = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
        grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLd (operation := ldOp),
          OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := ldOp)]
      have hCastResTypes : castOp.getResultTypes! ctx₃.raw = #[srcType] := by grind
      have hLdProps : ldOp.getProperties! ctx₃.raw (.riscv .ld)
          = { value := ⟨0, ⟨64⟩⟩ } := by
        grind [OperationPtr.getProperties!_WfRewriter_createOp hLd (operation := ldOp),
          OperationPtr.getProperties!_WfRewriter_createOp_ne hCast]
      -- Apply the memory bridge.
      have hbw' : intType = ⟨64⟩ := by obtain ⟨w⟩ := intType; simp_all
      have hSrcTypeE : srcType = ⟨.integerType ⟨64⟩, rfl⟩ := by
        apply Subtype.ext; rw [hStv, hbw']
      rw [hSrcTypeE] at hLoad
      obtain ⟨bits, hRiscvLoad, hRefine⟩ :=
        llvmLoad_i64_bridge state.memory a hz loadedVal hLoad
      -- Build the RISC-V load semantics from the bridge.
      have hSem : Riscv.interpretOp' .ld (ldOp.getProperties! ctx₃.raw (.riscv .ld))
          (ldOp.getResultTypes! ctx₃.raw) #[.reg ⟨BitVec.ofNat 64 a.toNat⟩]
          (ldOp.getSuccessors! ctx₃.raw) state'.memory
            = some (.ok (#[.reg (Data.RISCV.Reg.mk bits)], state'.memory, none)) := by
        rw [← memoryRefinement, hLdProps]
        simp only [Riscv.interpretOp', bind, pure]
        rw [hRiscvLoad]
      -- Execute the chain.
      obtain ⟨ns', hIL, hMemEq, tv, htvMap, htvRef⟩ :=
        load_execute_chain (by grind) (by grind) (by grind)
          hPcastType hPcastOperands hPcastResTypes hLdType hLdOperands hLdResTypes
          hCastType hCastOperands (hCastResTypes.trans (by rw [hSrcTypeE])) hPtrVal' hSem
          hRefine
      refine ⟨ns', ?_, by grind, tv, htvMap, htvRef⟩
      simpa only [liftM, monadLift, MonadLift.monadLift] using hIL
  · exact absurd hpattern (by simp)

end Veir
