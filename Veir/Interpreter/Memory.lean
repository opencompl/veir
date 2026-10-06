module

public import Veir.ForLean
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
public import Std.Data.HashMap

public section

open Veir.Data
open Veir.Data.LLVM (Ptr)

namespace Veir

/-- An object of memory: `size` bytes from `base`. Its bytes live in `MemoryState.bytes`. -/
@[ext]
structure MemoryObject where
  /-- The address of the first byte of the object. -/
  base : UInt64
  size : Nat
deriving Inhabited, DecidableEq

/-- A byte of memory and its poison bits; a set bit is poison. -/
@[ext]
structure MemoryByte where
  value : UInt8
  poison : UInt8
deriving Inhabited, DecidableEq

/-- The byte that memory holds before anything is stored to it. -/
def MemoryByte.poisoned : MemoryByte := ⟨0, 0xff⟩

/--
  Memory state during interpretation: one byte store, addressed by physical
  address, and the objects laid out in it. An address outside every object
  cannot be accessed, and one inside an object that nothing stored to is poison.
-/
@[ext]
structure MemoryState where
  bytes : Std.HashMap UInt64 MemoryByte
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
  The allocation policy: the address of the next object, past the end of every
  object with a guard byte between them and past the arena, rounded up to
  `objectAlignment`. It is a `Nat`, so that an object near the top of the
  address space cannot wrap it around; `alloc` fails when it does not fit.
  Only `alloc` reads it, so another policy, or a choice among all admissible
  addresses, replaces it here.
-/
def MemoryState.nextBase (mem : MemoryState) : Nat :=
  let past := mem.objects.foldl (init := arenaSize.toNat) fun past obj =>
    max past (obj.base.toNat + obj.size + 1)
  (past + objectAlignment.toNat - 1) / objectAlignment.toNat * objectAlignment.toNat

/-- Whether `addr` lies in `obj`, its one-past-the-end included. -/
def MemoryObject.covers (obj : MemoryObject) (addr : UInt64) : Bool :=
  obj.base.toNat ≤ addr.toNat ∧ addr.toNat ≤ obj.base.toNat + obj.size

/-- Whether the `size` bytes at `addr` lie inside `obj`. -/
def MemoryObject.holds (obj : MemoryObject) (addr : UInt64) (size : Nat) : Bool :=
  obj.base.toNat ≤ addr.toNat ∧ addr.toNat + size ≤ obj.base.toNat + obj.size

/-- The object that holds `addr`, if one does. -/
def MemoryState.objectOfAddress? (mem : MemoryState) (addr : UInt64) : Option Nat :=
  mem.objects.findIdx? (·.covers addr)

/-- The pointer to the start of object `i`, if the memory has it. -/
def MemoryState.pointerTo (mem : MemoryState) (i : Nat) : Option Pointer :=
  mem.objects[i]?.map fun obj => ⟨i, obj.base, false⟩

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
  excecute this program. A failing source is refined by anything and a
  failing target refines nothing, so such a run is never really compared.
-/
def MemoryState.alloc (mem : MemoryState) (size : UInt64) : Interp (MemoryState × Pointer) :=
  let base := mem.nextBase
  -- The guard byte after the object must be an address too.
  if base + size.toNat + 1 ≥ 2 ^ 64 then Interp.fail none else
  return ({ mem with objects := mem.objects.push ⟨base.toUInt64, size.toNat⟩ },
    ⟨mem.objects.size, base.toUInt64, false⟩)

/--
  Check that an access of `size` bytes at `p` stays inside an object: the
  pointer's own, or any object at all if the pointer is wild. A pointer naming
  an object the memory lacks is a failure of the interpreter.
-/
def MemoryState.checkAccess (mem : MemoryState) (p : Pointer) (size : UInt64) : Interp Unit := do
  -- An access of zero bytes is allowed at any offset, in bounds or not.
  if p.wild then
    if size = 0 ∨ mem.objects.any (·.holds p.address size.toNat) then return () else Interp.ub none
  else
    let some obj := mem.objects[p.object]? | Interp.fail none
    if size = 0 ∨ obj.holds p.address size.toNat then return () else Interp.ub none

/--
  Store raw bytes to the given address in memory,
  and set the corresponding poison bits as requested (by default, unset).
  Yields UB if the access is out of bounds.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) : Interp MemoryState := do
  mem.checkAccess p val.size.toUInt64
  let mut bytes := mem.bytes
  for i in [0:val.size] do
    bytes := bytes.insert (p.address + i.toUInt64) ⟨val[i]!, poison[i]!⟩
  return { mem with bytes }

/--
  Poison the given number n of bytes, starting from the given address in memory.
  Yields UB if the access is out of bounds.
-/
def MemoryState.empoison (mem : MemoryState) (p : Pointer) (n : Nat) : Interp MemoryState :=
  mem.store p (ByteArray.replicate n 0) (ByteArray.replicate n 0xff)

/--
  The pointer whose bits are `b`: it names the object holding that address when
  it is loaded, or the null object if none does.
-/
def MemoryState.ptrOfByte (mem : MemoryState) (b : Data.LLVM.Byte 64) : Ptr :=
  if b.poison = 0 then .val ⟨(mem.objectOfAddress? b.toUInt64).getD 0, b.toUInt64, false⟩
  else .poison

/-- Store the 64 bits of `v`, poison bits included, at `p`. -/
def MemoryState.storeByte64 (mem : MemoryState) (p : Pointer) (v : Data.LLVM.Byte 64)
    : Interp MemoryState :=
  mem.store p (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE

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
        (ByteArray.empty.push (UInt8.ofBitVec v.poison))
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
  | Attribute.integerType { bitwidth := 8, .. } =>
      let ba ← mem.load p 1
      if ← mem.hasPoison p 1 then return .int 8 .poison
      return .int 8 (.val ba[0]!.toNat)
  | Attribute.integerType { bitwidth := 16, .. } =>
      let ba ← mem.load p 2
      if ← mem.hasPoison p 2 then return .int 16 .poison
      return .int 16 (.val (ba.toBitVecLE 2))
  | Attribute.integerType { bitwidth := 32, .. } =>
      let ba ← mem.load p 4
      if ← mem.hasPoison p 4 then return .int 32 .poison
      return .int 32 (.val (ba.toBitVecLE 4))
  | Attribute.integerType { bitwidth := 64, .. } =>
      let ba ← mem.load p 8
      if ← mem.hasPoison p 8 then return .int 64 .poison
      return .int 64 (.val (BitVec.ofNat 64 ba.toUInt64LE!.toNat))
  | Attribute.byteType { bitwidth := 8 } =>
      let ba ← mem.load p 1
      let poison := BitVec.ofNat 8 (← mem.loadPoison p 1)[0]!.toNat
      return .byte 8 ⟨BitVec.ofNat 8 ba[0]!.toNat &&& ~~~poison, poison, by bv_decide⟩
  | Attribute.byteType { bitwidth := 64 } =>
      return .byte 64 (← mem.loadByte64 p)
  | Attribute.llvmPointerType _ =>
      return .addr (mem.ptrOfByte (← mem.loadByte64 p))
  | _ => none

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
  if d ≠ s ∧ d < s + len ∧ s < d + len then Interp.ub none
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
