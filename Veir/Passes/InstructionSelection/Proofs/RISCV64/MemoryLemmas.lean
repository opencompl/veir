module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Interpreter.Memory
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Data.Pointer.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.Casting
import all Veir.ForLean
import all Std.Data.ByteSlice
import all Init.Data.ByteArray.Extra
import all Veir.Interfaces.DataLayoutInterfaces
import all Veir.DataLayout.RISCV64

namespace Veir

-- The load and store proofs both bitblast successful alignment checks. Realize
-- the unit encoding here so their generated SAT helpers have a shared owner.
run_meta do
  discard <| Lean.Meta.Tactic.BVDecide.Normalize.getEnumToBitVecFor ``PUnit
  discard <| Lean.Meta.Tactic.BVDecide.Normalize.getEqIffEnumToBitVecEqFor ``PUnit
  discard <| Lean.Meta.Tactic.BVDecide.Normalize.getEnumToBitVecLeFor ``PUnit

/-- The memory-width matcher accepts only full-byte integers and 64-bit pointers. -/
theorem memAccessWidth_cases {type : TypeAttr} {bytes : Nat}
    (h : memAccessWidth? type = some bytes) :
    (∃ sign, type = TypeAttr.of IntegerType ⟨8 * bytes, sign⟩) ∨
    (∃ pointer : LLVM.PointerType, type = TypeAttr.of LLVM.PointerType pointer ∧ bytes = 8) := by
  rcases type with ⟨attr, ht⟩
  cases attr <;> simp only [memAccessWidth?] at h <;>
    simp only [Option.bind_eq_bind, Option.bind_none, Option.bind_some,
      Option.pure_def, Option.map_none, Option.map_some] at h <;> try contradiction
  case integerType t =>
    rcases t with ⟨w, sign⟩
    by_cases hm : w % 8 = 0
    · by_cases hz : w = 0
      · simp [failure, instAlternativeOption, guard, hm, hz, DataLayout.getTypeSize, DataLayout.riscv64,
          DataLayout.queryRISCV64, -Attribute.integerType_eq_of] at h
      · simp [failure, instAlternativeOption, guard, hm, hz, DataLayout.getTypeSize, DataLayout.riscv64,
          DataLayout.queryRISCV64, DataLayout.scalarInfo, -Attribute.integerType_eq_of] at h
        split at h
        · simp only [Option.bind_some, Option.some.injEq] at h
          have hw : w = 8 * bytes := by omega
          subst w
          exact .inl ⟨sign, rfl⟩
        · simp [failure, instAlternativeOption] at h
    · simp [failure, instAlternativeOption, guard, hm] at h
  case llvmPointerType p =>
    have hb : 8 = bytes := by
      simpa [DataLayout.getTypeSize, DataLayout.riscv64, DataLayout.queryRISCV64,
        DataLayout.scalarInfo, guard, failure, instAlternativeOption,
        -Attribute.llvmPointerType_eq_of] using h
    cases hb
    exact .inr ⟨p, rfl, rfl⟩

theorem byteArray_eq_singleton (bytes : ByteArray) (h : bytes.size = 1) :
    bytes = ⟨#[bytes[0]!]⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · exact h
  · intro i hi hj
    have : i = 0 := by simpa using hj
    subst i
    simp [getElem!_pos, ByteArray.getElem_eq_getElem_data, h]

private theorem pack8_eq (b : UInt8) : (ByteArray.mk #[b]).toBitVecLE 8 = b.toBitVec := by
  simp [ByteArray.toBitVecLE, ByteSlice.foldr, ByteSlice.foldrM, ByteSlice.foldrM.loop,
    ByteArray.toByteSlice, ByteSlice.size, ByteSlice.start, ByteSlice.stop, ByteArray.size]
  rfl

@[simp] theorem byteArray_toBitVecLE8 (bytes : ByteArray) (h : bytes.size = 1) :
    bytes.toBitVecLE 8 = bytes[0]!.toBitVec := by
  rw [byteArray_eq_singleton bytes h]
  exact pack8_eq _

theorem byteArray_eq_eight (bytes : ByteArray) (h : bytes.size = 8) :
    bytes = ⟨#[bytes[0]!, bytes[1]!, bytes[2]!, bytes[3]!,
      bytes[4]!, bytes[5]!, bytes[6]!, bytes[7]!]⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · exact h
  · intro i hi hj
    have hi8 : i < 8 := by simpa using hj
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [getElem!_pos, ByteArray.getElem_eq_getElem_data, h]

private theorem pack64_eq (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
 (ByteArray.mk #[b0,b1,b2,b3,b4,b5,b6,b7]).toBitVecLE 64 =
 BitVec.ofNat 64 (ByteArray.mk #[b0,b1,b2,b3,b4,b5,b6,b7]).toUInt64LE!.toNat := by
 conv => lhs; simp [ByteArray.toBitVecLE, ByteSlice.foldr, ByteSlice.foldrM, ByteSlice.foldrM.loop,
  ByteArray.toByteSlice, ByteSlice.size, ByteSlice.start, ByteSlice.stop, ByteArray.size]
 simp only [BitVec.ofNat_uInt64ToNat]
 change ((((((((((((((b7.toBitVec.setWidth 64) <<< 8 ||| b6.toBitVec.setWidth 64)) <<< 8 ||| b5.toBitVec.setWidth 64)) <<< 8 ||| b4.toBitVec.setWidth 64)) <<< 8 ||| b3.toBitVec.setWidth 64)) <<< 8 ||| b2.toBitVec.setWidth 64)) <<< 8 ||| b1.toBitVec.setWidth 64)) <<< 8 ||| b0.toBitVec.setWidth 64) = ((b7.toUInt64 <<< 56) ||| (b6.toUInt64 <<< 48) ||| (b5.toUInt64 <<< 40) ||| (b4.toUInt64 <<< 32) ||| (b3.toUInt64 <<< 24) ||| (b2.toUInt64 <<< 16) ||| (b1.toUInt64 <<< 8) ||| b0.toUInt64).toBitVec
 veir_bv_decide

@[simp] theorem byteArray_toBitVecLE64 (bytes : ByteArray) (h : bytes.size = 8) :
    bytes.toBitVecLE 64 = BitVec.ofNat 64 bytes.toUInt64LE!.toNat := by
  rw [byteArray_eq_eight bytes h]
  exact pack64_eq _ _ _ _ _ _ _ _

/-- Successful raw reads have exactly the requested number of bytes. -/
theorem MemoryState.load_size {memory : MemoryState} {p : Data.Pointer} {size : UInt64}
    {bytes : ByteArray} (h : memory.load p size = .ok bytes) : bytes.size = size.toNat := by
  unfold MemoryState.load at h
  cases hc : memory.checkAccess p size <;> simp [hc] at h
  subst bytes
  simp [ByteArray.size]

/-- A successful 16-bit LLVM load is refined by the low bits of the matching RISC-V load. -/
theorem llvmLoad16_riscvLoad (memory : MemoryState) (p : Data.Pointer)
    (sign : IntegerType.Signedness) (value : RuntimeValue)
    (h : memory.llvmLoad p (TypeAttr.of IntegerType ⟨16, sign⟩) = .ok value)
    (ext : LoadExtension) :
    ∃ bits : BitVec 64, riscvLoad memory p.address.toBitVec 2 ext = .ok (bits, memory) ∧
      value ⊒ RuntimeValue.int 16 (.val (bits.setWidth 16)) := by
  simp only [MemoryState.llvmLoad, TypeAttr.of_val, ←Attribute.integerType_eq_of] at h
  split at h
  · contradiction
  cases hl : memory.load p 2 <;> simp only [hl, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i bytes
  cases hp : memory.hasPoison p 2 <;>
    simp only [hp, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i poison
  cases poison <;> simp only [Bool.false_eq_true, ↓reduceIte, Interp.pure_eq, Interp.ok.injEq] at h <;>
    subst value
  all_goals refine ⟨(match ext with
      | .signExt => (bytes.toBitVecLE 16).signExtend 64
      | .zeroExt => (bytes.toBitVecLE 16).setWidth 64), ?_, ?_⟩
  all_goals try simp [riscvLoad, MemoryState.decode, hl]
  all_goals cases ext <;> simp [RuntimeValue.isRefinedBy, isRefinedBy]
  all_goals veir_bv_decide

/-- A successful 32-bit LLVM load is refined by the low bits of the matching RISC-V load. -/
theorem llvmLoad32_riscvLoad (memory : MemoryState) (p : Data.Pointer)
    (sign : IntegerType.Signedness) (value : RuntimeValue)
    (h : memory.llvmLoad p (TypeAttr.of IntegerType ⟨32, sign⟩) = .ok value)
    (ext : LoadExtension) :
    ∃ bits : BitVec 64, riscvLoad memory p.address.toBitVec 4 ext = .ok (bits, memory) ∧
      value ⊒ RuntimeValue.int 32 (.val (bits.setWidth 32)) := by
  simp only [MemoryState.llvmLoad, TypeAttr.of_val, ←Attribute.integerType_eq_of] at h
  split at h
  · contradiction
  cases hl : memory.load p 4 <;> simp only [hl, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i bytes
  cases hp : memory.hasPoison p 4 <;>
    simp only [hp, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i poison
  cases poison <;> simp only [Bool.false_eq_true, ↓reduceIte, Interp.pure_eq, Interp.ok.injEq] at h <;>
    subst value
  all_goals refine ⟨(match ext with
      | .signExt => (bytes.toBitVecLE 32).signExtend 64
      | .zeroExt => (bytes.toBitVecLE 32).setWidth 64), ?_, ?_⟩
  all_goals try simp [riscvLoad, MemoryState.decode, hl]
  all_goals cases ext <;> simp [RuntimeValue.isRefinedBy, isRefinedBy]
  all_goals veir_bv_decide

/-- A successful 8-bit LLVM load is refined by the low bits of the matching RISC-V load. -/
theorem llvmLoad8_riscvLoad (memory : MemoryState) (p : Data.Pointer)
    (sign : IntegerType.Signedness) (value : RuntimeValue)
    (h : memory.llvmLoad p (TypeAttr.of IntegerType ⟨8, sign⟩) = .ok value)
    (ext : LoadExtension) :
    ∃ bits : BitVec 64, riscvLoad memory p.address.toBitVec 1 ext = .ok (bits, memory) ∧
      value ⊒ RuntimeValue.int 8 (.val (bits.setWidth 8)) := by
  simp only [MemoryState.llvmLoad, TypeAttr.of_val, ←Attribute.integerType_eq_of] at h
  split at h
  · contradiction
  cases hl : memory.load p 1 <;> simp only [hl, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i bytes
  have hsize := MemoryState.load_size hl
  cases hp : memory.hasPoison p 1 <;>
    simp only [hp, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i poison
  cases poison <;> simp only [Bool.false_eq_true, ↓reduceIte, Interp.pure_eq, Interp.ok.injEq] at h <;>
    subst value
  all_goals refine ⟨(match ext with
      | .signExt => (bytes.toBitVecLE 8).signExtend 64
      | .zeroExt => (bytes.toBitVecLE 8).setWidth 64), ?_, ?_⟩
  all_goals try simp [riscvLoad, MemoryState.decode, hl]
  all_goals cases ext <;> simp [RuntimeValue.isRefinedBy, isRefinedBy, byteArray_toBitVecLE8 bytes hsize]
  all_goals veir_bv_decide

/-- A successful 64-bit LLVM load is refined by the low bits of the matching RISC-V load. -/
theorem llvmLoad64_riscvLoad (memory : MemoryState) (p : Data.Pointer)
    (sign : IntegerType.Signedness) (value : RuntimeValue)
    (h : memory.llvmLoad p (TypeAttr.of IntegerType ⟨64, sign⟩) = .ok value)
    (ext : LoadExtension) :
    ∃ bits : BitVec 64, riscvLoad memory p.address.toBitVec 8 ext = .ok (bits, memory) ∧
      value ⊒ RuntimeValue.int 64 (.val (bits.setWidth 64)) := by
  simp only [MemoryState.llvmLoad, TypeAttr.of_val, ←Attribute.integerType_eq_of] at h
  split at h
  · contradiction
  cases hl : memory.load p 8 <;> simp only [hl, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i bytes
  have hsize := MemoryState.load_size hl
  cases hp : memory.hasPoison p 8 <;>
    simp only [hp, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail] at h
  all_goals try contradiction
  rename_i poison
  cases poison <;> simp only [Bool.false_eq_true, ↓reduceIte, Interp.pure_eq, Interp.ok.injEq] at h <;>
    subst value
  all_goals refine ⟨(match ext with
      | .signExt => (bytes.toBitVecLE 64).signExtend 64
      | .zeroExt => (bytes.toBitVecLE 64).setWidth 64), ?_, ?_⟩
  all_goals try simp [riscvLoad, MemoryState.decode, hl]
  all_goals cases ext <;> simp [RuntimeValue.isRefinedBy, isRefinedBy, byteArray_toBitVecLE64 bytes hsize]
  all_goals veir_bv_decide

theorem llvmLoad_integer_riscvLoad (memory : MemoryState) (p : Data.Pointer)
    (bytes : Nat) (hb : bytes ∈ [1, 2, 4, 8]) (sign : IntegerType.Signedness)
    (value : RuntimeValue)
    (h : memory.llvmLoad p (TypeAttr.of IntegerType ⟨8 * bytes, sign⟩) = .ok value)
    (ext : LoadExtension) :
    ∃ bits : BitVec 64, riscvLoad memory p.address.toBitVec bytes ext = .ok (bits, memory) ∧
      value ⊒ RuntimeValue.int (8 * bytes) (.val (bits.setWidth (8 * bytes))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact llvmLoad8_riscvLoad memory p sign value h ext
  · exact llvmLoad16_riscvLoad memory p sign value h ext
  · exact llvmLoad32_riscvLoad memory p sign value h ext
  · exact llvmLoad64_riscvLoad memory p sign value h ext

/-- Pointer loads use the same physical bits; a poisoned source pointer permits any target. -/
theorem llvmLoad_pointer_riscvLoad (memory : MemoryState) (p : Data.Pointer)
    (pointer : LLVM.PointerType) (value : RuntimeValue)
    (h : memory.llvmLoad p (TypeAttr.of LLVM.PointerType pointer) = .ok value) :
    ∃ bits : BitVec 64, riscvLoad memory p.address.toBitVec 8 .zeroExt = .ok (bits, memory) ∧
      value ⊒ RuntimeValue.addr (memory.ptrFromInt (.val bits)) := by
  simp only [MemoryState.llvmLoad, TypeAttr.of_val, ←Attribute.llvmPointerType_eq_of] at h
  split at h
  · contradiction
  simp only [MemoryState.loadByte, Nat.reduceMod, ne_eq, not_true_eq_false, ↓reduceIte,
    Nat.reduceDiv] at h
  cases hp : memory.loadPoison p 8 <;> simp [hp] at h
  all_goals try contradiction
  rename_i mask
  cases hl : memory.load p 8 <;> simp [hl] at h
  all_goals try contradiction
  rename_i bytes
  subst value
  refine ⟨bytes.toBitVecLE 64, ?_, ?_⟩
  · simp [riscvLoad, MemoryState.decode, hl]
  · by_cases hm : mask.toBitVecLE 64 = 0#64
    all_goals simp [MemoryState.ptrOfByte, RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy,
      MemoryState.ptrFromInt, MemoryState.decode, Data.LLVM.Byte.toUInt64, hm]
    change (UInt64.ofBitVec (bytes.toBitVecLE 64)) =
      UInt64.ofBitVec (bytes.toBitVecLE 64) &&& (-1 : UInt64)
    simp only [UInt64.and_neg_one]

end Veir
