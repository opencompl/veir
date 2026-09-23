module

public import Veir.ForLean
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp

public section

open Veir.Data
open Veir.Data.LLVM (Ptr)

namespace Veir

/--
  A memory object.
  Set bits in the poison mask represent poison bits.
-/
@[ext]
structure MemoryObject where
  contents : ByteArray
  poisonMask : ByteArray
  consistentSize : contents.size = poisonMask.size
  /-- The physical address of the first byte of the object. -/
  base : UInt64

/-- An object of `size` bytes, all of them poison. -/
def MemoryObject.ofSize (base : UInt64) (size : Nat) : MemoryObject :=
  ⟨ByteArray.replicate size 0, ByteArray.replicate size 0xff, by grind, base⟩

instance : Inhabited MemoryObject := ⟨MemoryObject.ofSize 0 0⟩

def MemoryObject.size (obj : MemoryObject) : Nat := obj.contents.size

/--
  Memory state during interpretation.
-/
@[ext]
structure MemoryState where
  objects : Array MemoryObject

/--
  Object 0 is the null object at address 0. It holds no bytes, so every access
  through a null pointer is out of bounds.
-/
def MemoryState.empty : MemoryState := { objects := #[MemoryObject.ofSize 0 0] }

/-- Every object starts at a multiple of this many bytes. -/
def MemoryState.objectAlignment : UInt64 := 16

/--
  The low addresses below which no object is allocated, so that a small
  integer never denotes an object and the null object stays alone there.
-/
def MemoryState.arenaSize : UInt64 := 0x10000

/--
  The address of the next object: past the end of every object with a guard
  byte between them and past the arena, rounded up to `objectAlignment`.

  TODO: This is a simplification. Eventually, addresses should be
  non-deterministic.
-/
def MemoryState.nextBase (mem : MemoryState) : UInt64 :=
  let past := mem.objects.foldl (init := arenaSize) fun past obj =>
    max past (obj.base + obj.size.toUInt64 + 1)
  (past + objectAlignment - 1) / objectAlignment * objectAlignment

/--
  The object that `p` points into, or `none` if `p` indexes no object.

  No pointer should trigger the `none` case: every pointer the interpreter builds
  names an object contained in the state (currently only object 0) which `empty`
  creates and no operation ever removes. However, this is not enforced, so a
  bug may break this invariant.
-/
def MemoryState.getObject? (mem : MemoryState) (p : Pointer) : Option MemoryObject :=
  mem.objects[p.object]?

def MemoryState.setObject (mem : MemoryState) (p : Pointer) (obj : MemoryObject) : MemoryState :=
  { mem with objects := mem.objects.setIfInBounds p.object obj }

/--
  The index of the last object whose base is at most `addr`. Object 0 starts
  at address 0, so some object always qualifies.
-/
def MemoryState.objectOfAddress (mem : MemoryState) (addr : UInt64) : Nat :=
  let baseOf (i : Nat) : UInt64 := (mem.objects[i]?.map (·.base)).getD 0
  (List.range mem.objects.size).foldl (init := 0) fun best i =>
    if baseOf i ≤ addr ∧ baseOf best ≤ baseOf i then i else best

/-- The pointer that the physical address `addr` denotes. -/
def MemoryState.decode (mem : MemoryState) (addr : UInt64) : Pointer :=
  let i := mem.objectOfAddress addr
  ⟨i, addr - (mem.objects[i]?.map (·.base)).getD 0⟩

/-- The physical address of `p`. -/
def MemoryState.address (mem : MemoryState) (p : Pointer) : UInt64 :=
  (mem.objects[p.object]?.map (·.base)).getD 0 + p.offset

/--
  The size of an `alloca` in bytes as a 64-bit value. An `alloca` has no way
  to report failure, so a size that does not fit in the address space is
  undefined behaviour.
-/
def memorySize (n : Nat) : Interp UInt64 :=
  if n < 2 ^ 64 then return n.toUInt64 else Interp.ub none

/--
  Allocate `size` bytes and return a pointer to the start of the allocation.

  If there is insufficient memory, yield an interpretation failure. An
  out-of-memory event does not trigger UB, but it means that we cannot
  excecute this program.
-/
def MemoryState.alloc (mem : MemoryState) (size : UInt64) : Interp (MemoryState × Pointer) :=
  let base := mem.nextBase
  if base.toNat + size.toNat ≥ 2 ^ 64 then Interp.fail none else
  return ({ mem with objects := mem.objects.push (MemoryObject.ofSize base size.toNat) },
    ⟨mem.objects.size, 0⟩)

/--
  Check if an access of `size` bytes at `p` is allowed.
-/
def MemoryState.checkAccess (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp MemoryObject := do
  let some obj := mem.getObject? p | Interp.fail none

  -- An access of zero bytes is allowed at any offset, in bounds or not.
  if size = 0 then return obj

  -- The `size` must fit into the size of the object.
  let objSize := obj.contents.size.toUInt64
  if size ≤ objSize ∧ p.offset ≤ objSize - size then return obj

  Interp.ub none

/--
  Store raw bytes to the given address in memory,
  and set the corresponding poison bits as requested (by default, unset).
  Yields UB if the access is out of bounds.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    : Interp MemoryState := do
  let obj ← mem.checkAccess p val.size.toUInt64
  return mem.setObject p { obj with
    contents := val.copySlice 0 obj.contents p.offset.toNat val.size false,
    poisonMask := poison.copySlice 0 obj.poisonMask p.offset.toNat val.size false,
    consistentSize := by simp [ByteArray.copySlice_eq_append, obj.consistentSize, h] }

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
  if p = .null then Interp.ub none else
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
  let obj ← mem.checkAccess p size
  return obj.contents.extract p.offset.toNat (p.offset.toNat + size.toNat)

/--
  Load bitwise poison status of the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.loadPoison (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp ByteArray := do
  let obj ← mem.checkAccess p size
  return obj.poisonMask.extract p.offset.toNat (p.offset.toNat + size.toNat)

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
  if p = .null then Interp.ub none else
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
