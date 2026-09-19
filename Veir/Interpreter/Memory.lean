module

public import Veir.ForLean
public import Veir.RuntimeValue.Basic
public import Veir.Interpreter.Interp
public import Veir.Interpreter.MemoryModel

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

def MemoryState.empty : MemoryState := {
  contents := (ByteArray.emptyWithCapacity 1024).extend 8 0xff,
  poisonMask := (ByteArray.emptyWithCapacity 1024).extend 8 0xff,
  consistentSize := (by grind)
}

/--
  Allocate the given number of bytes of memory.
  Return the updated memory state and the freshly allocated address.
-/
def MemoryState.alloc (mem : MemoryState) (size : UInt64) : MemoryState × Pointer :=
  (⟨mem.contents.extend size.toNat 0,
    mem.poisonMask.extend size.toNat 0xff,
    by simp [mem.consistentSize]⟩, ⟨0, mem.contents.size.toUInt64⟩)

/--
  Store raw bytes to the given address in memory,
  and set the corresponding poison bits as requested (by default, unset).
  Yields UB if the access is out of bounds.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    : Interp MemoryState :=
  if p.offset.toNat + val.size ≤ mem.contents.size then
    return ⟨val.copySlice 0 mem.contents p.offset.toNat val.size false,
      poison.copySlice 0 mem.poisonMask p.offset.toNat val.size false,
      by
        simp [ByteArray.copySlice_eq_append, mem.consistentSize, h]
      ⟩
  else
    Interp.ub

/--
  Poison the given number n of bytes, starting from the given address in memory.
  Yields UB if the access is out of bounds.
-/
def MemoryState.empoison (mem : MemoryState) (p : Pointer) (n : Nat) : Interp MemoryState :=
  if h : p.offset.toNat + n ≤ mem.poisonMask.size then
    let mask := ByteArray.replicate n 0xff
    return ⟨mem.contents,
      mask.copySlice 0 mem.poisonMask p.offset.toNat n false,
      by
        have h' : min n mask.size = n := by grind
        have h'' : min p.offset.toNat mem.poisonMask.size = p.offset.toNat := by grind
        simp [ByteArray.copySlice_eq_append, mem.consistentSize, h', h'']
        grind

      ⟩
  else
    Interp.ub

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
  | .int n .poison => mem.empoison p (n / 8)
  | .addr q => mem.storeByte64 p q.toByte
  | _ => none

/--
  Load raw bytes from the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp ByteArray :=
  if p.offset.toNat + size.toNat ≤ mem.contents.size then
    return mem.contents.extract p.offset.toNat (p.offset + size).toNat
  else
    Interp.ub

/--
  Load bitwise poison status of the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.loadPoison (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp ByteArray :=
  if p.offset.toNat + size.toNat ≤ mem.poisonMask.size then
    return mem.poisonMask.extract p.offset.toNat (p.offset + size).toNat
  else
    Interp.ub

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

/-- The flat memory model: one byte array, addressed directly. -/
instance : MemoryModel MemoryState where
  name := "flat"
  initialMemState := MemoryState.empty
  allocateRegion state _align size := state.alloc size.toUInt64
  load state type p := state.llvmLoad p type
  store state p val := state.llvmStore p val
  validForDerefPtrval state p size := !p.isNull && p.offset.toNat + size ≤ state.contents.size
  arrayShiftPtrval p bytes := ⟨p.object, UInt64.ofNat (p.offset.toNat + bytes)⟩
  ptrFromInt _ i := Data.LLVM.Ptr.ofInt i
  intFromPtr _ p := p.toInt

end Veir
