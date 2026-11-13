module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryLemmas
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Interpreter.Memory
import all Veir.ForLean
import all Init.Data.ByteArray.Basic
import all Std.Data.ByteSlice

namespace Veir

private theorem loadPoison_size {memory : MemoryState} {p : Data.Pointer} {size : UInt64}
    {bytes : ByteArray} (h : memory.loadPoison p size = .ok bytes) : bytes.size = size.toNat := by
  unfold MemoryState.loadPoison at h
  cases hc : memory.checkAccess p size <;> simp [hc] at h
  subst bytes
  simp [ByteArray.size]

private theorem hasPoison_mask_zero (memory : MemoryState) (p : Data.Pointer) (bytes : UInt64)
    (hbytes : bytes = 1 ∨ bytes = 2 ∨ bytes = 4 ∨ bytes = 8)
    (h : memory.hasPoison p bytes = .ok false) :
    ∃ mask, memory.loadPoison p bytes = .ok mask ∧ mask.toBitVecLE (8 * bytes.toNat) = 0 := by
  unfold MemoryState.hasPoison at h
  cases hp : memory.loadPoison p bytes <;> simp only [hp, Interp.bind_ok,
    Interp.bind_fail, Interp.bind_ub, reduceCtorEq] at h
  rename_i mask
  refine ⟨mask, rfl, ?_⟩
  have hs := loadPoison_size hp
  rcases hbytes with rfl | rfl | rfl | rfl
  all_goals simp [forIn, ByteArray.forIn, ByteArray.forIn.loop, hs] at h
  all_goals repeat' split at h <;> simp_all [-byteArray_toBitVecLE8, -byteArray_toBitVecLE64]
  all_goals simp_all -failIfUnchanged [ByteArray.toBitVecLE, ByteSlice.foldr, ByteSlice.foldrM,
    ByteSlice.foldrM.loop, ByteArray.toByteSlice, ByteSlice.size, ByteSlice.start,
    ByteSlice.stop, ByteSlice.byteArray, ByteSlice.instGetElemNatUInt8LtSize, ByteSlice.get,
    -byteArray_toBitVecLE8, -byteArray_toBitVecLE64]
  all_goals grind

private theorem hasPoison_mask_exists (memory : MemoryState) (p : Data.Pointer) (size : UInt64)
    (poison : Bool) (h : memory.hasPoison p size = .ok poison) :
    ∃ mask, memory.loadPoison p size = .ok mask := by
  unfold MemoryState.hasPoison at h
  cases hp : memory.loadPoison p size <;> simp only [hp, Interp.bind_ok,
    Interp.bind_fail, Interp.bind_ub, reduceCtorEq] at h
  exact ⟨_, rfl⟩

/-- Every resolution of a loaded byte refines a successful integer load. -/
theorem llvmLoad_integer_loadByte (memory : MemoryState) (p : Data.Pointer)
    (sign : IntegerType.Signedness) (bytes : Nat)
    (hbytes : bytes = 1 ∨ bytes = 2 ∨ bytes = 4 ∨ bytes = 8) (value : RuntimeValue)
    (h : memory.llvmLoad p (TypeAttr.of IntegerType ⟨8 * bytes, sign⟩) = .ok value) :
    ∃ b, memory.loadByte p (8 * bytes) = .ok b ∧
      ∀ choice, value ⊒ RuntimeValue.int (8 * bytes) (.val (b.val ||| (b.poison &&& choice))) := by
  rcases hbytes with rfl | rfl | rfl | rfl
  all_goals
    simp only [MemoryState.llvmLoad, TypeAttr.of_val, ←Attribute.integerType_eq_of] at h
    split at h
    · contradiction
    first
    | (cases hl : memory.load p 1 <;> simp only [hl, Interp.bind_ok,
        Interp.bind_ub, Interp.bind_fail, reduceCtorEq] at h)
    | (cases hl : memory.load p 2 <;> simp only [hl, Interp.bind_ok,
        Interp.bind_ub, Interp.bind_fail, reduceCtorEq] at h)
    | (cases hl : memory.load p 4 <;> simp only [hl, Interp.bind_ok,
        Interp.bind_ub, Interp.bind_fail, reduceCtorEq] at h)
    | (cases hl : memory.load p 8 <;> simp only [hl, Interp.bind_ok,
        Interp.bind_ub, Interp.bind_fail, reduceCtorEq] at h)
    rename_i data
    first
    | (cases hp : memory.hasPoison p 1 <;> simp only [hp, Interp.bind_ok,
        Interp.bind_ub, Interp.bind_fail, reduceCtorEq] at h)
    | (cases hp : memory.hasPoison p 2 <;> simp only [hp, Interp.bind_ok,
        Interp.bind_ub, Interp.bind_fail, reduceCtorEq] at h)
    | (cases hp : memory.hasPoison p 4 <;> simp only [hp, Interp.bind_ok,
        Interp.bind_ub, Interp.bind_fail, reduceCtorEq] at h)
    | (cases hp : memory.hasPoison p 8 <;> simp only [hp, Interp.bind_ok,
        Interp.bind_ub, Interp.bind_fail, reduceCtorEq] at h)
    rename_i poison
    obtain ⟨mask, hm⟩ := hasPoison_mask_exists memory p _ poison hp
    refine ⟨⟨data.toBitVecLE _ &&& ~~~mask.toBitVecLE _, mask.toBitVecLE _, by ext; simp⟩, ?_, ?_⟩
    · simp [MemoryState.loadByte, hm, hl]
    · cases poison <;> simp only [Bool.false_eq_true, ↓reduceIte, Interp.pure_eq,
        Interp.ok.injEq] at h <;> subst value
      · obtain ⟨mask', hm', hz⟩ := hasPoison_mask_zero memory p _ (by simp) hp
        rw [hm] at hm'
        cases hm'
        simp only [UInt64.reduceToNat, Nat.reduceMul] at hz
        have hs := MemoryState.load_size hl
        simp [hz, RuntimeValue.isRefinedBy, isRefinedBy, hs]
        veir_bv_decide
      · simp [RuntimeValue.isRefinedBy, isRefinedBy]

/-- Every resolution of a loaded pointer's bytes refines the source pointer. -/
theorem llvmLoad_pointer_loadByte (memory : MemoryState) (p : Data.Pointer)
    (pointer : LLVM.PointerType) (value : RuntimeValue)
    (h : memory.llvmLoad p (TypeAttr.of LLVM.PointerType pointer) = .ok value) :
    ∃ b, memory.loadByte p 64 = .ok b ∧ ∀ choice,
      value ⊒ RuntimeValue.addr (memory.ptrFromInt (.val (b.val ||| (b.poison &&& choice)))) := by
  simp only [MemoryState.llvmLoad, TypeAttr.of_val, ←Attribute.llvmPointerType_eq_of] at h
  split at h
  · contradiction
  cases hb : memory.loadByte p 64 <;> simp [hb] at h
  rename_i b
  subst value
  refine ⟨b, rfl, ?_⟩
  by_cases hz : b.poison = 0#64
  · simp [MemoryState.ptrOfByte, RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy,
      MemoryState.ptrFromInt, MemoryState.decode, Data.LLVM.Byte.toUInt64, hz]
  · simp [MemoryState.ptrOfByte, RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy,
      hz]

def loadResolvedBits (b : Data.LLVM.Byte w) (choice : BitVec w) (ext : LoadExtension) : BitVec 64 :=
  let bits := b.val ||| (b.poison &&& choice)
  match ext with
  | .signExt => bits.signExtend 64
  | .zeroExt => bits.setWidth 64

/-- Extending a resolved load preserves its low source bits. -/
@[simp]
theorem load_signExtend_low (bits : BitVec w) (hw : w ≤ 64) :
    (bits.signExtend 64).setWidth w = bits := by
  ext i hi
  simp [BitVec.getElem_signExtend, hi, Nat.lt_of_lt_of_le hi hw]

@[simp]
theorem loadResolvedBits_low (b : Data.LLVM.Byte w) (choice : BitVec w) (ext : LoadExtension)
    (hw : w ≤ 64) :
    (loadResolvedBits b choice ext).setWidth w = b.val ||| (b.poison &&& choice) := by
  cases ext <;> simp [loadResolvedBits, hw, BitVec.setWidth_setWidth_of_le _ hw]

end Veir
