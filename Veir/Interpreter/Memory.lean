module

public import Veir.ForLean
public import Veir.RuntimeValue.Basic
public import Veir.Interpreter.Interp

public section

open Veir.Data

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

def MemoryState.empty : MemoryState := {
  contents := (ByteArray.emptyWithCapacity 1024).extend 8 0xff,
  poisonMask := (ByteArray.emptyWithCapacity 1024).extend 8 0xff,
  consistentSize := (by grind)
}

/-- The pointer that the physical address `addr` denotes. -/
def MemoryState.decode (_mem : MemoryState) (addr : UInt64) : Pointer := ⟨0, addr⟩

/-- The physical address of `p`. -/
def MemoryState.address (_mem : MemoryState) (p : Pointer) : UInt64 := p.offset

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
  if mem.contents.size + size.toNat ≥ 2 ^ 64 then Interp.fail else
  return (⟨mem.contents.extend size.toNat 0,
    mem.poisonMask.extend size.toNat 0xff,
    by simp [mem.consistentSize]⟩, ⟨0, mem.contents.size.toUInt64⟩)

/--
  Check if an access of `size` bytes at `p` is allowed.
-/
def MemoryState.checkAccess (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp Unit := do
  -- An access of zero bytes is allowed anywhere.
  if size = 0 then return ()

  -- The `size` must fit into the size of the memory.
  let memSize := mem.contents.size.toUInt64
  if size ≤ memSize ∧ p.offset ≤ memSize - size then return ()

  Interp.ub

/--
  Store raw bytes to the given address in memory,
  and set the corresponding poison bits as requested (by default, unset).
  Yields UB if the access is out of bounds.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    : Interp MemoryState := do
  mem.checkAccess p val.size.toUInt64
  return ⟨val.copySlice 0 mem.contents p.offset.toNat val.size false,
    poison.copySlice 0 mem.poisonMask p.offset.toNat val.size false,
    by simp [ByteArray.copySlice_eq_append, mem.consistentSize, h]⟩

/--
  Poison the given number n of bytes, starting from the given address in memory.
  Yields UB if the access is out of bounds.
-/
def MemoryState.empoison (mem : MemoryState) (p : Pointer) (n : Nat) : Interp MemoryState :=
  mem.store p (ByteArray.replicate n 0) (ByteArray.replicate n 0xff) (by simp)

/-- The pointer whose bits are `b`. -/
def MemoryState.ptrOfByte (mem : MemoryState) (b : Data.LLVM.Byte 64) : Ptr :=
  if b.poison = 0 then .val (mem.decode b.toUInt64) else .poison

/-- The bits of a pointer, its physical address. -/
def MemoryState.byteOfPtr (mem : MemoryState) : Ptr → Data.LLVM.Byte 64
  | .val p => Data.LLVM.Byte.fromUInt64 (mem.address p)
  | .poison => Data.LLVM.Byte.allPoison

/-- The pointer at the address `i`. -/
def MemoryState.ptrFromInt (mem : MemoryState) : Data.LLVM.Int 64 → Ptr
  | .val v => .val (mem.decode (UInt64.ofBitVec v))
  | .poison => .poison

/-- The address of a pointer as a 64-bit integer. -/
def MemoryState.intFromPtr (mem : MemoryState) : Ptr → Data.LLVM.Int 64
  | .val p => .val (mem.address p).toBitVec
  | .poison => .poison

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
  if p = .null then Interp.ub else
  match val with
  | .int 8 (.val v) => mem.store p (ByteArray.empty.push (UInt8.ofBitVec v))
  | .int 16 (.val v) => mem.store p (UInt16.ofBitVec v).toByteArrayLE
  | .int 32 (.val v) => mem.store p (UInt32.ofBitVec v).toByteArrayLE
  | .int 64 (.val v) => mem.store p (UInt64.ofBitVec v).toByteArrayLE
  | .byte 64 v => mem.storeByte64 p v
  | .int n .poison => mem.empoison p (n / 8)
  | .addr q => mem.storeByte64 p (mem.byteOfPtr q)
  | _ => none

/--
  Load raw bytes from the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp ByteArray := do
  mem.checkAccess p size
  return mem.contents.extract p.offset.toNat (p.offset.toNat + size.toNat)

/--
  Load bitwise poison status of the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.loadPoison (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp ByteArray := do
  mem.checkAccess p size
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
  if p = .null then Interp.ub else
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
      return .addr (mem.ptrOfByte (← mem.loadByte64 p))
  | _ => none

end Veir
