module

public import Veir.RuntimeValue
public import Veir.Interpreter.Interp

public section

open Veir.Data
open Veir.Data.LLVM (Pointer Ptr)

namespace Veir

/--
  One allocation during interpretation: its bytes, a poison mask in which set
  bits mark poison bits, and the physical address `base` at which the object
  starts, so that byte `i` of the object lives at address `base + i`.
-/
@[ext]
structure MemoryObject where
  contents : ByteArray
  poisonMask : ByteArray
  consistentSize : contents.size = poisonMask.size
  base : UInt64

/-- An object of `size` bytes at address `base`, all of them poison. -/
def MemoryObject.ofSize (base : UInt64) (size : Nat) : MemoryObject :=
  ⟨ByteArray.replicate size 0, ByteArray.replicate size 0xff, by grind, base⟩

instance : Inhabited MemoryObject := ⟨MemoryObject.ofSize 0 0⟩

def MemoryObject.size (obj : MemoryObject) : Nat := obj.contents.size

/-- Grow the object to at least `size` bytes; the new bytes are poison. -/
def MemoryObject.ensureSize (obj : MemoryObject) (size : Nat) : MemoryObject :=
  if obj.contents.size < size then
    { obj with
      contents := obj.contents.extend (size - obj.contents.size) 0,
      poisonMask := obj.poisonMask.extend (size - obj.contents.size) 0xff,
      consistentSize := by simp [obj.consistentSize] }
  else
    obj

/--
  Memory state during interpretation: one object per allocation, addressed by
  `Pointer`. The objects share one physical address space. They are laid out
  in allocation order, each starting past the end of the previous one with at
  least one guard byte in between, so a pointer converts to an address
  (`MemoryState.address`) and an address back to a pointer
  (`MemoryState.decode`). Object 0 is the null object at address 0. It holds
  no bytes, so every access through a null pointer is out of bounds, until
  machine code grows it into the arena below `arenaSize`.
-/
@[ext]
structure MemoryState where
  objects : Array MemoryObject

def MemoryState.empty : MemoryState := ⟨#[MemoryObject.ofSize 0 0]⟩

/-- Every object starts at a multiple of at least this many bytes. -/
def MemoryState.objectAlignment : UInt64 := 16

/--
  The low addresses below which no object is allocated. Machine code may
  address this arena freely: it belongs to the null object, which grows on
  demand under RISC-V accesses.
-/
def MemoryState.arenaSize : UInt64 := 0x10000

/--
  The address at which the next object is placed: past the end of the last
  object with a guard byte and past the arena, rounded up to `align` or
  `objectAlignment`, whichever is larger.
-/
def MemoryState.nextBase (state : MemoryState) (align : UInt64 := objectAlignment) : UInt64 :=
  let align := max align objectAlignment
  let last := state.objects.back?.getD (MemoryObject.ofSize 0 0)
  let past := max (last.base + last.size.toUInt64 + 1) arenaSize
  (past + align - 1) / align * align

def MemoryState.getObject? (state : MemoryState) (addr : Pointer) : Option MemoryObject :=
  state.objects[addr.object]?

def MemoryState.setObject (state : MemoryState) (addr : Pointer) (obj : MemoryObject) : MemoryState :=
  ⟨state.objects.setIfInBounds addr.object obj⟩

/--
  The index of the last object whose base is at most `address`, found by binary
  search. Objects are sorted by base and object 0 starts at address 0, so
  some object always qualifies.
-/
def MemoryState.objectOfAddress (state : MemoryState) (address : UInt64) : Nat := Id.run do
  let mut lo := 0
  let mut hi := state.objects.size
  /- Invariant: `objects[lo].base ≤ address`, and `address < objects[hi].base` when
     `hi < objects.size`. Each round halves `hi - lo`, so 64 rounds suffice. -/
  for _ in [0:64] do
    if hi - lo ≤ 1 then break
    let mid := (lo + hi) / 2
    if state.objects[mid]!.base ≤ address then lo := mid else hi := mid
  return lo

/--
  The pointer that the physical address `address` denotes: the object whose range
  contains it, or, when it falls into the gap after an object, a pointer past
  the end of that object. Accessing such a pointer is out of bounds.
-/
def MemoryState.decode (state : MemoryState) (address : UInt64) : Pointer :=
  let i := state.objectOfAddress address
  ⟨i, address - (state.objects[i]?.map (·.base)).getD 0⟩

/-- The physical address of `addr`. A pointer to no object has only its offset. -/
def MemoryState.address (state : MemoryState) (addr : Pointer) : UInt64 :=
  (state.objects[addr.object]?.map (·.base)).getD 0 + addr.offset

/--
  Grow the object `addr` points into so that `size` bytes at `addr` are in bounds,
  as far as the gap before the next object allows. The RISC-V interpreter
  uses this to give machine code a memory that does not fault; LLVM accesses
  are bounds-checked instead.
-/
def MemoryState.ensureSize (state : MemoryState) (addr : Pointer) (size : Nat) : MemoryState :=
  match state.getObject? addr with
  | none => state
  | some obj =>
    let wanted := addr.offset.toNat + size
    let wanted := match state.objects[addr.object + 1]? with
      | some next => min wanted (next.base - obj.base).toNat
      | none => wanted
    state.setObject addr (obj.ensureSize wanted)

/--
  Allocate a fresh object of `size` bytes, aligned to `align`, and return a
  pointer to its start.
-/
def MemoryState.alloc (state : MemoryState) (size : Nat) (align : UInt64 := objectAlignment)
    : MemoryState × Pointer :=
  let align := max align objectAlignment
  (⟨state.objects.push (MemoryObject.ofSize (state.nextBase align) size)⟩, ⟨state.objects.size, 0⟩)

/--
  The object that an access of `size` bytes at `addr` touches, if the access is
  allowed: the object must exist and the access must stay inside it. An access
  of no bytes is allowed anywhere, even through a pointer to nothing. Later
  conditions on an access are added here.
-/
def MemoryState.checkAccess (state : MemoryState) (addr : Pointer) (size : Nat)
    : Interp MemoryObject :=
  match state.getObject? addr with
  | none => Interp.ub
  | some obj =>
    if size = 0 then return obj
    else if addr.offset.toNat + size ≤ obj.contents.size then return obj
    else Interp.ub

/--
  Store raw bytes at `addr`, and set the corresponding poison bits as requested
  (by default, unset). Yields UB if the access leaves the object.
-/
def MemoryState.store (state : MemoryState) (addr : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    : Interp MemoryState := do
  let obj ← state.checkAccess addr val.size
  if addr.offset.toNat + val.size ≤ obj.contents.size then
    return state.setObject addr { obj with
      contents := val.copySlice 0 obj.contents addr.offset.toNat val.size false,
      poisonMask := poison.copySlice 0 obj.poisonMask addr.offset.toNat val.size false,
      consistentSize := by simp [ByteArray.copySlice_eq_append, obj.consistentSize, h] }
  else
    Interp.ub

/--
  Poison `n` bytes starting at `addr`. Yields UB if the access leaves the object.
-/
def MemoryState.empoison (state : MemoryState) (addr : Pointer) (n : Nat) : Interp MemoryState :=
  match state.getObject? addr with
  | none => Interp.ub
  | some obj =>
    if h : addr.offset.toNat + n ≤ obj.poisonMask.size then
      let mask := ByteArray.replicate n 0xff
      return state.setObject addr { obj with
        poisonMask := mask.copySlice 0 obj.poisonMask addr.offset.toNat n false,
        consistentSize := by
          have h' : min n mask.size = n := by grind
          have h'' : min addr.offset.toNat obj.poisonMask.size = addr.offset.toNat := by grind
          simp [ByteArray.copySlice_eq_append, obj.consistentSize, h', h'']
          grind }
    else
      Interp.ub

/--
  The pointer whose bits are `b`: poison if any bit is poison, otherwise the
  pointer at that physical address. This is the conversion a pointer load and
  a bitcast to a pointer apply to raw bytes, as `Byte.toInt` is for integers.
-/
def MemoryState.ptrOfByte (state : MemoryState) (b : Data.LLVM.Byte 64) : Ptr :=
  if b.poison = 0 then .val (state.decode b.toUInt64) else .poison

/-- The bits of a pointer, its physical address: all poison for a poison pointer. -/
def MemoryState.byteOfPtr (state : MemoryState) : Ptr → Data.LLVM.Byte 64
  | .val p => Data.LLVM.Byte.fromUInt64 (state.address p)
  | .poison => Data.LLVM.Byte.allPoison

/-- Store the 64 bits of `v`, poison bits included, at `addr`. Yields UB if the access leaves the object. -/
def MemoryState.storeByte64 (state : MemoryState) (addr : Pointer) (v : Data.LLVM.Byte 64)
    : Interp MemoryState :=
  state.store addr (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE (by simp)

/--
  Store an LLVM value at `addr`. A pointer is stored as its physical address.
  Yields UB if the access leaves the object or the pointer is null.
-/
def MemoryState.llvmStore (state : MemoryState) (addr : Pointer) (val : RuntimeValue)
    : Interp MemoryState :=
  if addr.isNull then Interp.ub else
  match val with
  | .int 8 (.val v) => state.store addr (ByteArray.empty.push (UInt8.ofBitVec v))
  | .int 16 (.val v) => state.store addr (UInt16.ofBitVec v).toByteArrayLE
  | .int 32 (.val v) => state.store addr (UInt32.ofBitVec v).toByteArrayLE
  | .int 64 (.val v) => state.store addr (UInt64.ofBitVec v).toByteArrayLE
  | .byte 64 v => state.storeByte64 addr v
  | .int n .poison => state.empoison addr (n / 8)
  | .addr p => state.storeByte64 addr (state.byteOfPtr p)
  | _ => none

/--
  Load `size` raw bytes at `addr`. Yields UB if the access leaves the object.
-/
def MemoryState.load (state : MemoryState) (addr : Pointer) (size : Nat) : Interp ByteArray := do
  let obj ← state.checkAccess addr size
  return obj.contents.extract addr.offset.toNat (addr.offset.toNat + size)

/--
  Load the poison mask of `size` bytes at `addr`. Yields UB if the access leaves the object.
-/
def MemoryState.loadPoison (state : MemoryState) (addr : Pointer) (size : Nat) : Interp ByteArray := do
  let obj ← state.checkAccess addr size
  return obj.poisonMask.extract addr.offset.toNat (addr.offset.toNat + size)

/--
  Check if any of the `size` bytes at `addr` is poison. Yields UB if the access leaves the object.
-/
def MemoryState.hasPoison (state : MemoryState) (addr : Pointer) (size : Nat) : Interp Bool := do
  let poisonMask ← state.loadPoison addr size
  let mut poison := false
  for b in poisonMask do
    if b ≠ 0 then
      poison := true
      break
  return poison

/-- Load the 64 bits at `addr`, poison bits included. Yields UB if the access leaves the object. -/
def MemoryState.loadByte64 (state : MemoryState) (addr : Pointer) : Interp (Data.LLVM.Byte 64) := do
  let ba ← state.load addr 8
  let baPoison ← state.loadPoison addr 8
  let poison := baPoison.toUInt64LE!.toBitVec
  return ⟨ba.toUInt64LE!.toBitVec &&& ~~~poison, poison, by bv_decide⟩

/--
  Load an LLVM value of type `type` from `addr`. A pointer is read back from the
  physical address stored in memory.
  Yields UB if the access leaves the object or the pointer is null.

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
def MemoryState.llvmLoad (state : MemoryState) (addr : Pointer) (type : TypeAttr)
    : Interp RuntimeValue := do
  if addr.isNull then Interp.ub else
  match type.val with
  | Attribute.integerType { bitwidth := 8 } =>
      let ba ← state.load addr 1
      if ← state.hasPoison addr 1 then return .int 8 .poison
      return .int 8 (.val ba[0]!.toNat)
  | Attribute.integerType { bitwidth := 16 } =>
      let ba ← state.load addr 2
      if ← state.hasPoison addr 2 then return .int 16 .poison
      return .int 16 (.val (ba.toBitVecLE 2))
  | Attribute.integerType { bitwidth := 32 } =>
      let ba ← state.load addr 4
      if ← state.hasPoison addr 4 then return .int 32 .poison
      return .int 32 (.val (ba.toBitVecLE 4))
  | Attribute.integerType { bitwidth := 64 } =>
      let ba ← state.load addr 8
      if ← state.hasPoison addr 8 then return .int 64 .poison
      return .int 64 (.val (BitVec.ofNat 64 ba.toUInt64LE!.toNat))
  | Attribute.byteType { bitwidth := 64 } =>
      return .byte 64 (← state.loadByte64 addr)
  | Attribute.llvmPointerType _ =>
      return .addr (state.ptrOfByte (← state.loadByte64 addr))
  | _ => none

end Veir
