module

public import Veir.ForLean
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
public import Std.Data.ExtHashMap
import Veir.Data.Casting

public section

open Veir.Data
open Veir.Data.LLVM (Ptr)

namespace Veir

/--
  A memory object: `size` bytes from `base`.
  Its bytes live in `MemoryState.bytes`.
-/
@[ext]
structure MemoryObject where
  /-- The physical address of the first byte of the object. -/
  base : UInt64
  size : Nat

/-- Whether the `size` bytes at `addr` lie inside `obj`. -/
def MemoryObject.holds (obj : MemoryObject) (addr : UInt64) (size : Nat) : Bool :=
  obj.base.toNat ≤ addr.toNat ∧ addr.toNat + size ≤ obj.base.toNat + obj.size

/-- A byte of memory and its poison bits; a set bit is poison. -/
structure MemoryByte where
  value : UInt8
  poison : UInt8

/-- The byte that memory holds before anything is stored to it. -/
def MemoryByte.poisoned : MemoryByte := ⟨0, 0xff⟩

/--
  Memory state during interpretation. Memory is one byte store keyed by
  physical address, and an object is a range of it; a byte nothing stored to
  is poison.

  Objects are disjoint, and each new one starts past every object already
  present, which `alloc` maintains but nothing here enforces.
-/
@[ext]
structure MemoryState where
  bytes : Std.ExtHashMap UInt64 MemoryByte
  objects : Array MemoryObject
  /-- The object of each global and function, by its symbol, such as `@g`. -/
  globals : Std.HashMap String Nat := {}

/--
  Object 0 is the null object at address 0. It holds no bytes, so every access
  through a null pointer is out of bounds.
-/
def MemoryState.empty : MemoryState := { bytes := {}, objects := #[⟨0, 0⟩] }

/-- The byte at `addr`. -/
def MemoryState.byte (mem : MemoryState) (addr : UInt64) : MemoryByte :=
  mem.bytes.getD addr .poisoned

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
def MemoryState.nextBase (mem : MemoryState) : Nat :=
  let past := mem.objects.foldl (init := arenaSize.toNat) fun past obj =>
    max past (obj.base.toNat + obj.size + 1)
  (past + objectAlignment.toNat - 1) / objectAlignment.toNat * objectAlignment.toNat

/--
  The object that `p` points into, or `none` if `p` indexes no object.

  No pointer should trigger the `none` case: every pointer the interpreter builds
  names an object contained in the state (currently only object 0) which `empty`
  creates and no operation ever removes. However, this is not enforced, so a
  bug may break this invariant.
-/
def MemoryState.getObject? (mem : MemoryState) (p : Pointer) : Option MemoryObject :=
  mem.objects[p.object]?

/--
  The index of the last object whose base is at most `addr`. Object 0 starts
  at address 0, so some object always qualifies.
-/
def MemoryState.objectOfAddress (mem : MemoryState) (addr : UInt64) : Nat :=
  let baseOf (i : Nat) : UInt64 := (mem.objects[i]?.map (·.base)).getD 0
  (List.range mem.objects.size).foldl (init := 0) fun best i =>
    if baseOf i ≤ addr ∧ baseOf best ≤ baseOf i then i else best

/--
  The pointer that the physical address `addr` denotes. Every address is mapped
  to a pointer object, as we just look for the closest object from below that a
  given address may belong to. If no other object matches, addresses are mapped
  to the null object. Yet, addresses outside of an object's boundaries may be
  out-of-bounds and will be rejected in `checkAccess`.
-/
def MemoryState.decode (mem : MemoryState) (addr : UInt64) : Pointer :=
  ⟨mem.objectOfAddress addr, addr⟩

/-- The pointer to the start of the object of the global `symbol`, if the memory has it. -/
def MemoryState.pointerToGlobal (mem : MemoryState) (symbol : String) : Option Pointer := do
  let i ← mem.globals[symbol]?
  let obj ← mem.objects[i]?
  return ⟨i, obj.base⟩

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
  execute this program. A failing source is refined by anything and a
  failing target refines nothing, so such a run is never really compared.
-/
def MemoryState.alloc (mem : MemoryState) (size : UInt64) : Interp (MemoryState × Pointer) :=
  let base := mem.nextBase
  if base + size.toNat + 1 > 2 ^ 64 then Interp.fail none else
  return ({ mem with objects := mem.objects.push ⟨base.toUInt64, size.toNat⟩ },
    ⟨mem.objects.size, base.toUInt64⟩)

/--
  Check if an access of `size` bytes at `p` is allowed.
-/
def MemoryState.checkAccess (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp Unit := do
  let some obj := mem.getObject? p | Interp.fail none

  -- An access of zero bytes is allowed at any offset, in bounds or not.
  if size = 0 then return ()

  -- The `size` bytes must lie inside the object.
  if obj.holds p.address size.toNat then return ()

  Interp.ub none

/--
  Check that `p` is aligned to `alignment` bytes.
  Yields UB if the address is not a multiple of the alignment.
-/
def Data.Pointer.checkAlignment (p : Pointer) (alignment : Nat) : Interp Unit :=
  if alignment = 0 ∨ p.address.toNat % alignment = 0 then return () else Interp.ub none

/--
  Store raw bytes to the given address in memory,
  and set the corresponding poison bits as requested (by default, unset).
  Yields UB if the access is out of bounds.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    : Interp MemoryState := do
  mem.checkAccess p val.size.toUInt64
  let mut bytes := mem.bytes
  for hi : i in [0:val.size] do
    bytes := bytes.insert (p.address + i.toUInt64) ⟨val[i], poison[i]'(h ▸ hi.upper)⟩
  return { mem with bytes }

/--
  Poison the given number n of bytes, starting from the given address in memory.
  Yields UB if the access is out of bounds.
-/
def MemoryState.empoison (mem : MemoryState) (p : Pointer) (n : Nat) : Interp MemoryState :=
  mem.store p (ByteArray.replicate n 0) (ByteArray.replicate n 0xff) (by simp)

/-- The pointer whose bits are `b`. -/
def MemoryState.ptrOfByte (mem : MemoryState) (b : Data.LLVM.Byte 64) : Ptr :=
  if b.poison = 0 then .val (mem.decode b.toUInt64) else .poison

/-- The pointer at the address `i`. -/
def MemoryState.ptrFromInt (mem : MemoryState) : Data.LLVM.Int 64 → Ptr
  | .val v => .val (mem.decode (UInt64.ofBitVec v))
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
  | .byte 8 v =>
      mem.store p (ByteArray.empty.push (UInt8.ofBitVec v.val))
        (ByteArray.empty.push (UInt8.ofBitVec v.poison)) (by simp)
  | .byte 64 v => mem.storeByte64 p v
  | .int n .poison => mem.empoison p (n / 8)
  | .addr q => mem.storeByte64 p q.toByte
  | _ => none

/--
  Load raw bytes from the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp ByteArray := do
  mem.checkAccess p size
  return ⟨Array.ofFn fun (i : Fin size.toNat) => (mem.byte (p.address + i.val.toUInt64)).value⟩

/--
  Load bitwise poison status of the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.loadPoison (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp ByteArray := do
  mem.checkAccess p size
  return ⟨Array.ofFn fun (i : Fin size.toNat) => (mem.byte (p.address + i.val.toUInt64)).poison⟩

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

/-- Load the `w` bits at `p`, poison bits included. Yields UB if the access is out of bounds. -/
def MemoryState.loadByte (mem : MemoryState) (p : Pointer) (w : Nat)
    : Interp (Data.LLVM.Byte w) := do
  if w % 8 ≠ 0 then none else
  let size := (w / 8).toUInt64
  let poison := (← mem.loadPoison p size).toBitVecLE w
  let val := (← mem.load p size).toBitVecLE w
  return ⟨val &&& ~~~poison, poison, by ext; simp⟩

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
  | Attribute.integerType { bitwidth := 8, .. } =>
      let ba ← mem.load p 1
      if ← mem.hasPoison p 1 then return .int 8 .poison
      return .int 8 (.val ba[0]!.toNat)
  | Attribute.integerType { bitwidth := 16, .. } =>
      let ba ← mem.load p 2
      if ← mem.hasPoison p 2 then return .int 16 .poison
      return .int 16 (.val (ba.toBitVecLE 16))
  | Attribute.integerType { bitwidth := 32, .. } =>
      let ba ← mem.load p 4
      if ← mem.hasPoison p 4 then return .int 32 .poison
      return .int 32 (.val (ba.toBitVecLE 32))
  | Attribute.integerType { bitwidth := 64, .. } =>
      let ba ← mem.load p 8
      if ← mem.hasPoison p 8 then return .int 64 .poison
      return .int 64 (.val (BitVec.ofNat 64 ba.toUInt64LE!.toNat))
  | Attribute.byteType { bitwidth := 8 } =>
      return .byte 8 (← mem.loadByte p 8)
  | Attribute.byteType { bitwidth := 64 } =>
      return .byte 64 (← mem.loadByte p 64)
  | Attribute.llvmPointerType _ =>
      return .addr (mem.ptrOfByte (← mem.loadByte p 64))
  | _ => none

/--
  Loads a `w`-bit integer from `p`, poison only if every bit is (see `LLVM.Byte.toFrozenInt`).
  Yields UB if the access is out of bounds or `p` is null.

  TODO: With CTrees, freeze the poison bits nondeterministically.
-/
def MemoryState.frozenLoad (mem : MemoryState) (p : Pointer) (w : Nat)
    : Interp (Data.LLVM.Int w) := do
  if p = .null then Interp.ub none else
  return LLVM.Byte.toFrozenInt (← mem.loadByte p w)

/-- The type `b8`, which keeps the poison bits of a byte loaded from memory. -/
def byte8Type : TypeAttr := TypeAttr.of LLVM.ByteType ⟨8⟩

/--
  `llvm.intr.memset`: store the `i8` value `val` to each of the `len` bytes at `p`,
  one byte at a time.
-/
def MemoryState.memset (mem : MemoryState) (p : Pointer) (val : RuntimeValue) (len : Nat)
    : Interp MemoryState := do
  let mut mem := mem
  for i in [0:len] do
    mem ← mem.llvmStore (p.addBytes i) val
  return mem

/--
  `llvm.intr.memcpy`: copy `len` bytes, poison bits included, from `src` to `dst`,
  one `b8` load and store at a time in increasing order. Either `dst` and `src`
  are the same pointer, or the `len` bytes at `dst` and at `src` do not overlap;
  any other overlap is UB.
-/
def MemoryState.memcpy (mem : MemoryState) (dst src : Pointer) (len : Nat)
    : Interp MemoryState := do
  let d := dst.address.toNat
  let s := src.address.toNat
  if dst.object = src.object ∧ d ≠ s ∧ d < s + len ∧ s < d + len then Interp.ub none
  let mut mem := mem
  for i in [0:len] do
    mem ← mem.llvmStore (dst.addBytes i) (← mem.llvmLoad (src.addBytes i) byte8Type)
  return mem

/--
  `llvm.intr.memmove`: copy `len` bytes, poison bits included, from `src` to `dst`.
  The regions may overlap, and afterwards `dst` holds what `src` held before the
  call. As in C's `memmove`, the bytes go through a temporary buffer.
-/
def MemoryState.memmove (mem : MemoryState) (dst src : Pointer) (len : Nat)
    : Interp MemoryState := do
  let mut bytes := #[]
  for i in [0:len] do
    bytes := bytes.push (← mem.llvmLoad (src.addBytes i) byte8Type)
  let mut mem := mem
  for i in [0:len] do
    mem ← mem.llvmStore (dst.addBytes i) bytes[i]!
  return mem

end Veir
