module

public import Veir.ForLean
public import Veir.RuntimeValue.Basic
public import Veir.Interpreter.Interp

public section

open Veir.Data
open Veir.Data (Pointer)
open Veir.Data.LLVM (Ptr)

namespace Veir

/--
  Memory state during interpretation.
  Set bits in the poison mask represent poison bits.
-/
@[ext]
structure MemoryState where
  contents : ByteArray
  poisonMask : ByteArray
  consistentSize : contents.size = poisonMask.size
  /-- The size of memory in bytes. Being a 64-bit value, it says that memory fits in the address space. -/
  size : UInt64
  size_eq : contents.size = size.toNat

def MemoryState.empty : MemoryState := {
  contents := (ByteArray.emptyWithCapacity 1024).extend 8 0xff,
  poisonMask := (ByteArray.emptyWithCapacity 1024).extend 8 0xff,
  consistentSize := (by grind)
  size := 8
  size_eq := (by grind)
}

/--
  The size of an `alloca` in bytes as a 64-bit value. An `alloca` has no way
  to report failure, so a size that does not fit in the address space is
  undefined behaviour.
-/
def memorySize (n : Nat) : Interp UInt64 :=
  if n < 2 ^ 64 then return n.toUInt64 else Interp.ub

/--
  Allocate `size` bytes and return a pointer to the start of the allocation.

  If there is insufficient memory, yield an interpretation failure. An
  out-of-memory event does not trigger UB, but it means that we cannot
  excecute this program.
-/
def MemoryState.alloc (mem : MemoryState) (size : UInt64) : Interp (MemoryState × Pointer) :=
  if h : mem.size.toNat + size.toNat ≥ 2 ^ 64 then Interp.fail else
  return ({ contents := mem.contents.extend size.toNat 0,
            poisonMask := mem.poisonMask.extend size.toNat 0xff,
            consistentSize := by simp [mem.consistentSize],
            size := mem.size + size,
            size_eq := by simp [mem.size_eq, UInt64.toNat_add]; omega },
    ⟨0, mem.size⟩)

/-- A size below 2^64 survives the conversion to a 64-bit value. -/
theorem Nat.toNat_toUInt64_of_lt {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The 64-bit bounds check implies the bound on the array indices. -/
theorem MemoryState.bound_of_le (mem : MemoryState) {off size : UInt64}
    (h : size ≤ mem.size ∧ off ≤ mem.size - size) :
    off.toNat + size.toNat ≤ mem.contents.size := by
  obtain ⟨h1, h2⟩ := h
  rw [UInt64.le_iff_toNat_le] at h1 h2
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h1)] at h2
  rw [mem.size_eq]
  omega

/--
  Whether an access of `size` bytes at `p` is allowed: it must stay inside
  memory. An access of no bytes is allowed anywhere. On success the check
  yields the bound on array indices that the accessors rely on. Later
  conditions on an access are added here.
-/
def MemoryState.checkAccess (mem : MemoryState) (p : Pointer) (size : UInt64)
    : Interp (PLift (size ≠ 0 → p.offset.toNat + size.toNat ≤ mem.contents.size)) :=
  /- The comparison is on 64-bit values and adds nothing, so it cannot wrap. -/
  if h0 : size = 0 then return ⟨fun h => absurd h0 h⟩
  else if h : size ≤ mem.size ∧ p.offset ≤ mem.size - size then return ⟨fun _ => mem.bound_of_le h⟩
  else Interp.ub

/--
  Store raw bytes to the given address in memory,
  and set the corresponding poison bits as requested (by default, unset).
  Yields UB if the access is out of bounds.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    : Interp MemoryState := do
  /- A value of 2^64 bytes or more cannot lie inside memory. -/
  if hv : val.size < 2 ^ 64 then
    let ⟨hb⟩ ← mem.checkAccess p val.size.toUInt64
    if h0 : val.size = 0 then return mem else
    have hb : p.offset.toNat + val.size ≤ mem.contents.size := by
      have := hb (fun e => h0 (by simpa [Nat.toNat_toUInt64_of_lt hv] using congrArg UInt64.toNat e))
      simpa [Nat.toNat_toUInt64_of_lt hv] using this
    return { mem with
      contents := val.copySlice 0 mem.contents p.offset.toNat val.size false,
      poisonMask := poison.copySlice 0 mem.poisonMask p.offset.toNat val.size false,
      consistentSize := by simp [ByteArray.copySlice_eq_append, mem.consistentSize, h],
      size_eq := by
        rw [← mem.size_eq]
        simp [ByteArray.copySlice_eq_append]
        omega }
  else
    Interp.ub

/--
  Poison the given number `n` of bytes, starting from the given address in memory.
  Yields UB if the access is out of bounds.
-/
def MemoryState.empoison (mem : MemoryState) (p : Pointer) (n : UInt64) : Interp MemoryState := do
  let ⟨hb⟩ ← mem.checkAccess p n
  if h0 : n = 0 then return mem else
  have h : p.offset.toNat + n.toNat ≤ mem.poisonMask.size := mem.consistentSize ▸ hb h0
  let mask := ByteArray.replicate n.toNat 0xff
  return { mem with
    poisonMask := mask.copySlice 0 mem.poisonMask p.offset.toNat n.toNat false,
    consistentSize := by
      have h' : min n.toNat mask.size = n.toNat := by grind
      have h'' : min p.offset.toNat mem.poisonMask.size = p.offset.toNat := by grind
      simp [ByteArray.copySlice_eq_append, mem.consistentSize, h', h'']
      grind }

/-- Store the 64 bits of `v`, poison bits included, at `p`. -/
def MemoryState.storeByte64 (mem : MemoryState) (p : Pointer) (v : Data.LLVM.Byte 64)
    : Interp MemoryState :=
  mem.store p (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE (by simp)

/--
  Store an LLVM value to memory.
  Yields UB if the access is out of bounds or the address is 0.
-/
def MemoryState.llvmStore (mem : MemoryState) (p : Pointer) (val : RuntimeValue)
    : Interp MemoryState :=
  if p.isNull then Interp.ub else
  match val with
  | .int 8 (.val v) => mem.store p (ByteArray.empty.push (UInt8.ofBitVec v))
  | .int 16 (.val v) => mem.store p (UInt16.ofBitVec v).toByteArrayLE
  | .int 32 (.val v) => mem.store p (UInt32.ofBitVec v).toByteArrayLE
  | .int 64 (.val v) => mem.store p (UInt64.ofBitVec v).toByteArrayLE
  | .byte 64 v => mem.storeByte64 p v
  | .int n .poison => mem.empoison p (n / 8).toUInt64
  | .addr q => mem.storeByte64 p q.toByte
  | _ => none

/--
  Load raw bytes from the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp ByteArray := do
  let _ ← mem.checkAccess p size
  return mem.contents.extract p.offset.toNat (p.offset.toNat + size.toNat)

/--
  Load bitwise poison status of the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.loadPoison (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp ByteArray := do
  let _ ← mem.checkAccess p size
  return mem.poisonMask.extract p.offset.toNat (p.offset.toNat + size.toNat)

/--
  Check if any of the `size` bytes at the given memory address `p` is poison.
  Yields UB if the access is out of bounds.
-/
def MemoryState.hasPoison (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp Bool := do
  let poisonMask ← mem.loadPoison p size
  let mut poison := false
  for b in poisonMask do
    if b ≠ 0 then
      poison := true
      break
  return poison

/-- Load the 64 bits at `p`, poison bits included. Yields UB if the access is out of bounds. -/
def MemoryState.loadByte64 (mem : MemoryState) (p : Pointer) : Interp (Data.LLVM.Byte 64) := do
  let ba ← mem.load p 8
  let baPoison ← mem.loadPoison p 8
  let poison := baPoison.toUInt64LE!.toBitVec
  return ⟨ba.toUInt64LE!.toBitVec &&& ~~~poison, poison, by bv_decide⟩

/--
  Load an LLVM value from the given memory address.
  Yields UB if access is out of bounds or the address is 0.

  An integer or pointer load with any poison bit is poison as a whole, and a
  `byte` load keeps poison per bit.

  Together with fresh memory being poison, this is the semantics proposed in
  "Towards Removing Undef Values from LLVM IR" (Lobo et al., PLDI 2026), not
  LangRef's, where uninitialized memory reads as `undef`.
  As Clang relies still on `undef` semantics, e.g., for a bitfield or an integer
  copy of a struct with uninitialized padding, we sometimes introduce UB where
  we should not. The solution is to introduce a freezing load to LLVM and VeIR
  and ensure that all frontends are using them.
-/
def MemoryState.llvmLoad (mem : MemoryState) (p : Pointer) (type : TypeAttr)
    : Interp RuntimeValue := do
  if p.isNull then Interp.ub else
  match type.val with
  | Attribute.integerType { bitwidth := 8 } =>
      let ba ← mem.load p 1
      if ← mem.hasPoison p 1 then return .int 8 .poison
      return .int 8 (.val ba[0]!.toNat)
  | Attribute.integerType { bitwidth := 16 } =>
      let ba ← mem.load p 2
      if ← mem.hasPoison p 2 then return .int 16 .poison
      return .int 16 (.val (ba.toBitVecLE 2))
  | Attribute.integerType { bitwidth := 32 } =>
      let ba ← mem.load p 4
      if ← mem.hasPoison p 4 then return .int 32 .poison
      return .int 32 (.val (ba.toBitVecLE 4))
  | Attribute.integerType { bitwidth := 64 } =>
      let ba ← mem.load p 8
      if ← mem.hasPoison p 8 then return .int 64 .poison
      return .int 64 (.val (BitVec.ofNat 64 ba.toUInt64LE!.toNat))
  | Attribute.byteType { bitwidth := 64 } =>
      return .byte 64 (← mem.loadByte64 p)
  | Attribute.llvmPointerType _ =>
      return .addr (Data.LLVM.Ptr.ofByte (← mem.loadByte64 p))
  | _ => none

end Veir
