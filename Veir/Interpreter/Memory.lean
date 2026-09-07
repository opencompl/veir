module

public import Veir.RuntimeValue
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

def MemoryState.ensureSize (mem : MemoryState) (size : Nat) : MemoryState :=
  if mem.contents.size < size then
    ⟨mem.contents.extend (size - mem.contents.size) 0,
      mem.poisonMask.extend (size - mem.contents.size) 0xff,
      (by simp [mem.consistentSize])⟩
  else
    mem

/--
  Allocate the given number of bytes of memory.
  Return the updated memory state and the freshly allocated address.
-/
def MemoryState.alloc (state : MemoryState) (size : UInt64)
    : MemoryState × UInt64 :=
  (⟨state.contents.extend size.toNat 0,
    state.poisonMask.extend size.toNat 0xff,
    by simp [state.consistentSize]⟩, state.contents.size.toUInt64)

/--
  Store raw bytes to the given address in memory,
  and set the corresponding poison bits as requested (by default, unset).
  Yields UB if the access is out of bounds.
-/
def MemoryState.store (state : MemoryState) (addr : UInt64) (val : ByteArray)
  (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    : Interp MemoryState :=
  if addr.toNat + val.size ≤ state.contents.size then
    return ⟨val.copySlice 0 state.contents addr.toNat val.size false,
      poison.copySlice 0 state.poisonMask addr.toNat val.size false,
      by
        simp [ByteArray.copySlice_eq_append, state.consistentSize, h]
      ⟩
  else
    Interp.ub

/--
  Poison the given number n of bytes, starting from the given address in memory.
  Yields UB if the access is out of bounds.
-/
def MemoryState.empoison (state : MemoryState) (addr : UInt64) (n : Nat)
    : Interp MemoryState :=
  if h : addr.toNat + n ≤ state.poisonMask.size then
    let mask := ByteArray.replicate n 0xff
    return ⟨state.contents,
      mask.copySlice 0 state.poisonMask addr.toNat n false,
      by
        have h' : min n mask.size = n := by grind
        have h'' : min addr.toNat state.poisonMask.size = addr.toNat := by grind
        simp [ByteArray.copySlice_eq_append, state.consistentSize, h', h'']
        grind

      ⟩
  else
    Interp.ub

/--
  Store an LLVM value to memory.
  Yields UB if the access is out of bounds or the address is 0.
-/
def MemoryState.llvmStore (state : MemoryState) (addr : UInt64) (val : RuntimeValue)
    : Interp MemoryState :=
  if addr.toNat == 0 then Interp.ub else
  match val with
  | .int 8 (.val v) => state.store addr (ByteArray.empty.push (UInt8.ofBitVec v))
  | .int 16 (.val v) => state.store addr (UInt16.ofBitVec v).toByteArrayLE
  | .int 32 (.val v) => state.store addr (UInt32.ofBitVec v).toByteArrayLE
  | .int 64 (.val v) => state.store addr (UInt64.ofBitVec v).toByteArrayLE
  | .byte 64 v => state.store addr (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE (by simp)
  | .int n .poison => state.empoison addr (n / 8)
  | .addr v => state.store addr v.toByteArrayLE
  | _ => none

/--
  Load raw bytes from the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.load (state : MemoryState) (addr size : UInt64)
    : Interp ByteArray :=
  if addr.toNat + size.toNat <= state.contents.size then
    return state.contents.extract addr.toNat (addr + size).toNat
  else
    Interp.ub

/--
  Load bitwise poison status of the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.loadPoison (state : MemoryState) (addr size : UInt64)
    : Interp ByteArray :=
  if addr.toNat + size.toNat <= state.poisonMask.size then
    return state.poisonMask.extract addr.toNat (addr + size).toNat
  else
    Interp.ub

/--
  Check if any of the `size` bytes at the given memory address `addr` is poison.
  Yields UB if the access is out of bounds.
-/
def MemoryState.hasPoison (state : MemoryState) (addr size : UInt64)
    : Interp Bool := do
  let poisonMask ← state.loadPoison addr size
  let mut poison := false
  for b in poisonMask do
    if b ≠ 0 then
      poison := true
      break
  return poison

/--
  Load an LLVM value from the given memory address.
  Yields UB if access is out of bounds or the address is 0.
-/
def MemoryState.llvmLoad (state : MemoryState) (addr : UInt64) (type : TypeAttr)
    : Interp RuntimeValue := do
  if addr == 0 then Interp.ub else
  match type.val with
  | Attribute.integerType { bitwidth := 8, .. } =>
      let ba ← state.load addr 1
      if ← state.hasPoison addr 1 then return .int 8 .poison
      return .int 8 (.val ba[0]!.toNat)
  | Attribute.integerType { bitwidth := 16, .. } =>
      let ba ← state.load addr 2
      if ← state.hasPoison addr 2 then return .int 16 .poison
      return .int 16 (.val (ba.toBitVecLE 2))
  | Attribute.integerType { bitwidth := 32, .. } =>
      let ba ← state.load addr 4
      if ← state.hasPoison addr 4 then return .int 32 .poison
      return .int 32 (.val (ba.toBitVecLE 4))
  | Attribute.integerType { bitwidth := 64, .. } =>
      let ba ← state.load addr 8
      if ← state.hasPoison addr 8 then return .int 64 .poison
      return .int 64 (.val (BitVec.ofNat 64 ba.toUInt64LE!.toNat))
  | Attribute.byteType { bitwidth := 64 } =>
      let ba ← state.load addr 8
      let baPoison ← state.loadPoison addr 8
      let poison := baPoison.toUInt64LE!.toBitVec
      return .byte 64 ⟨ba.toUInt64LE!.toBitVec &&& ~~~poison, poison, by bv_decide⟩
  | Attribute.llvmPointerType _ =>
      let ba ← state.load addr 8
      -- FIXME poison address
      if ← state.hasPoison addr 8 then return .addr 0
      return .addr ba.toUInt64LE!
  | _ => none

end Veir
