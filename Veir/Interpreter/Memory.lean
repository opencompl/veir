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
def MemoryState.nextBase (mem : MemoryState) (align : UInt64 := objectAlignment) : UInt64 :=
  let align := max align objectAlignment
  let last := mem.objects.back?.getD (MemoryObject.ofSize 0 0)
  let past := max (last.base + last.size.toUInt64 + 1) arenaSize
  (past + align - 1) / align * align

def MemoryState.getObject? (mem : MemoryState) (p : Pointer) : Option MemoryObject :=
  mem.objects[p.object]?

def MemoryState.setObject (mem : MemoryState) (p : Pointer) (obj : MemoryObject) : MemoryState :=
  ⟨mem.objects.setIfInBounds p.object obj⟩

/--
  The index of the last object whose base is at most `addr`, found by binary
  search. Objects are sorted by base and object 0 starts at address 0, so
  some object always qualifies.
-/
def MemoryState.objectOfAddress (mem : MemoryState) (addr : UInt64) : Nat := Id.run do
  let mut lo := 0
  let mut hi := mem.objects.size
  /- Invariant: `objects[lo].base ≤ addr`, and `addr < objects[hi].base` when
     `hi < objects.size`. Each round halves `hi - lo`, so 64 rounds suffice. -/
  for _ in [0:64] do
    if hi - lo ≤ 1 then break
    let mid := (lo + hi) / 2
    if mem.objects[mid]!.base ≤ addr then lo := mid else hi := mid
  return lo

/--
  The pointer that the physical address `addr` denotes: the object whose range
  contains it, or, when it falls into the gap after an object, a pointer past
  the end of that object. Accessing such a pointer is out of bounds.
-/
def MemoryState.decode (mem : MemoryState) (addr : UInt64) : Pointer :=
  let i := mem.objectOfAddress addr
  ⟨i, addr - (mem.objects[i]?.map (·.base)).getD 0⟩

/-- The physical address of `p`. A pointer to no object has only its offset. -/
def MemoryState.address (mem : MemoryState) (p : Pointer) : UInt64 :=
  (mem.objects[p.object]?.map (·.base)).getD 0 + p.offset

/--
  Grow the object `p` points into so that `size` bytes at `p` are in bounds,
  as far as the gap before the next object allows. The RISC-V interpreter
  uses this to give machine code a memory that does not fault; LLVM accesses
  are bounds-checked instead.
-/
def MemoryState.ensureSize (mem : MemoryState) (p : Pointer) (size : Nat) : MemoryState :=
  match mem.getObject? p with
  | none => mem
  | some obj =>
    let wanted := p.offset.toNat + size
    let wanted := match mem.objects[p.object + 1]? with
      | some next => min wanted (next.base - obj.base).toNat
      | none => wanted
    mem.setObject p (obj.ensureSize wanted)

/--
  Allocate a fresh object of `size` bytes, aligned to `align`, and return a
  pointer to its start.
-/
def MemoryState.alloc (mem : MemoryState) (size : Nat) (align : UInt64 := objectAlignment)
    : MemoryState × Pointer :=
  let align := max align objectAlignment
  (⟨mem.objects.push (MemoryObject.ofSize (mem.nextBase align) size)⟩, ⟨mem.objects.size, 0⟩)

/--
  The object that an access of `size` bytes at `p` touches, if the access is
  allowed: the object must exist, the access must stay inside it, and the
  physical address must be a multiple of `align`. An access of no bytes is
  allowed anywhere, even through a pointer to nothing. Later conditions on an
  access are added here.
-/
def MemoryState.checkAccess (mem : MemoryState) (p : Pointer) (size : Nat)
    (align : Nat := 1) : Interp MemoryObject :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if size = 0 then return obj
    else if p.offset.toNat + size > obj.contents.size then Interp.ub
    else if 1 < align ∧ (mem.address p).toNat % align ≠ 0 then Interp.ub
    else return obj

/--
  Store raw bytes at `p`, and set the corresponding poison bits as requested
  (by default, unset). Yields UB if the access leaves the object.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    (align : Nat := 1) : Interp MemoryState := do
  let obj ← mem.checkAccess p val.size align
  if p.offset.toNat + val.size ≤ obj.contents.size then
    return mem.setObject p { obj with
      contents := val.copySlice 0 obj.contents p.offset.toNat val.size false,
      poisonMask := poison.copySlice 0 obj.poisonMask p.offset.toNat val.size false,
      consistentSize := by simp [ByteArray.copySlice_eq_append, obj.consistentSize, h] }
  else
    Interp.ub

/--
  Poison `n` bytes starting at `p`. Yields UB if the access leaves the object.
-/
def MemoryState.empoison (mem : MemoryState) (p : Pointer) (n : Nat) (align : Nat := 1)
    : Interp MemoryState := do
  let _ ← mem.checkAccess p n align
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if h : p.offset.toNat + n ≤ obj.poisonMask.size then
      let mask := ByteArray.replicate n 0xff
      return mem.setObject p { obj with
        poisonMask := mask.copySlice 0 obj.poisonMask p.offset.toNat n false,
        consistentSize := by
          have h' : min n mask.size = n := by grind
          have h'' : min p.offset.toNat obj.poisonMask.size = p.offset.toNat := by grind
          simp [ByteArray.copySlice_eq_append, obj.consistentSize, h', h'']
          grind }
    else
      Interp.ub

/--
  The pointer whose bits are `b`: poison if any bit is poison, otherwise the
  pointer at that physical address. This is the conversion a pointer load and
  a bitcast to a pointer apply to raw bytes, as `Byte.toInt` is for integers.
-/
def MemoryState.ptrOfByte (mem : MemoryState) (b : Data.LLVM.Byte 64) : Ptr :=
  if b.poison = 0 then .val (mem.decode b.toUInt64) else .poison

/-- The bits of a pointer, its physical address: all poison for a poison pointer. -/
def MemoryState.byteOfPtr (mem : MemoryState) : Ptr → Data.LLVM.Byte 64
  | .val p => Data.LLVM.Byte.fromUInt64 (mem.address p)
  | .poison => Data.LLVM.Byte.allPoison

/-- Store the 64 bits of `v`, poison bits included, at `p`. Yields UB if the access is not allowed. -/
def MemoryState.storeByte64 (mem : MemoryState) (p : Pointer) (v : Data.LLVM.Byte 64)
    (align : Nat := 1) : Interp MemoryState :=
  mem.store p (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE (by simp) align

/--
  Store an LLVM value at `p` with the access's `alignment` attribute, where 0
  stands for the value's natural alignment, its size. A pointer is stored as
  its physical address.
  Yields UB if the access is not allowed or the pointer is null.
-/
def MemoryState.llvmStore (mem : MemoryState) (p : Pointer) (val : RuntimeValue)
    (alignment : Nat := 0) : Interp MemoryState :=
  if p.isNull then Interp.ub else
  let alignFor (size : Nat) : Nat := if alignment = 0 then size else alignment
  match val with
  | .int 8 (.val v) => mem.store p (ByteArray.empty.push (UInt8.ofBitVec v)) (align := alignFor 1)
  | .int 16 (.val v) => mem.store p (UInt16.ofBitVec v).toByteArrayLE (align := alignFor 2)
  | .int 32 (.val v) => mem.store p (UInt32.ofBitVec v).toByteArrayLE (align := alignFor 4)
  | .int 64 (.val v) => mem.store p (UInt64.ofBitVec v).toByteArrayLE (align := alignFor 8)
  | .byte 64 v => mem.storeByte64 p v (alignFor 8)
  | .int n .poison => mem.empoison p (n / 8) (alignFor (n / 8))
  | .addr q => mem.storeByte64 p (mem.byteOfPtr q) (alignFor 8)
  | _ => none

/--
  Load `size` raw bytes at `p`. Yields UB if the access leaves the object.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : Nat) (align : Nat := 1)
    : Interp ByteArray := do
  let obj ← mem.checkAccess p size align
  return obj.contents.extract p.offset.toNat (p.offset.toNat + size)

/--
  Load the poison mask of `size` bytes at `p`. Yields UB if the access leaves the object.
-/
def MemoryState.loadPoison (mem : MemoryState) (p : Pointer) (size : Nat) (align : Nat := 1)
    : Interp ByteArray := do
  let obj ← mem.checkAccess p size align
  return obj.poisonMask.extract p.offset.toNat (p.offset.toNat + size)

/--
  Check if any of the `size` bytes at `p` is poison. Yields UB if the access leaves the object.
-/
def MemoryState.hasPoison (mem : MemoryState) (p : Pointer) (size : Nat) (align : Nat := 1)
    : Interp Bool := do
  let poisonMask ← mem.loadPoison p size align
  let mut poison := false
  for b in poisonMask do
    if b ≠ 0 then
      poison := true
      break
  return poison

/-- Load the 64 bits at `p`, poison bits included. Yields UB if the access is not allowed. -/
def MemoryState.loadByte64 (mem : MemoryState) (p : Pointer) (align : Nat := 1)
    : Interp (Data.LLVM.Byte 64) := do
  let ba ← mem.load p 8 align
  let baPoison ← mem.loadPoison p 8 align
  let poison := baPoison.toUInt64LE!.toBitVec
  return ⟨ba.toUInt64LE!.toBitVec &&& ~~~poison, poison, by bv_decide⟩

/--
  Load an LLVM value of type `type` from `p` with the access's `alignment`
  attribute, where 0 stands for the natural alignment of the type, its size.
  A pointer is read back from the physical address stored in memory.
  Yields UB if the access is not allowed or the pointer is null.

  An integer or pointer load with any poison bit is poison as a whole, and a
  `byte` load keeps poison per bit.

  Together with fresh memory being poison, this is the semantics proposed in
  "Towards Removing Undef Values from LLVM IR" (Lobo et al., PLDI 2026), not
  LangRef's, where uninitialized memory reads as `undef`.
  As Clang on still on poison, e.g., for a bitfield or an integer copy of a
  struct with uninitialized padding, we sometimes introduce UB where we should
  not. The solution is to introduce a freezing load to LLVM and VeIR and ensure
  that all frontends are using them.
-/
def MemoryState.llvmLoad (mem : MemoryState) (p : Pointer) (type : TypeAttr)
    (alignment : Nat := 0) : Interp RuntimeValue := do
  if p.isNull then Interp.ub else
  let alignFor (size : Nat) : Nat := if alignment = 0 then size else alignment
  match type.val with
  | Attribute.integerType { bitwidth := 8 } =>
      let ba ← mem.load p 1 (alignFor 1)
      if ← mem.hasPoison p 1 (alignFor 1) then return .int 8 .poison
      return .int 8 (.val ba[0]!.toNat)
  | Attribute.integerType { bitwidth := 16 } =>
      let ba ← mem.load p 2 (alignFor 2)
      if ← mem.hasPoison p 2 (alignFor 2) then return .int 16 .poison
      return .int 16 (.val (ba.toBitVecLE 2))
  | Attribute.integerType { bitwidth := 32 } =>
      let ba ← mem.load p 4 (alignFor 4)
      if ← mem.hasPoison p 4 (alignFor 4) then return .int 32 .poison
      return .int 32 (.val (ba.toBitVecLE 4))
  | Attribute.integerType { bitwidth := 64 } =>
      let ba ← mem.load p 8 (alignFor 8)
      if ← mem.hasPoison p 8 (alignFor 8) then return .int 64 .poison
      return .int 64 (.val (BitVec.ofNat 64 ba.toUInt64LE!.toNat))
  | Attribute.byteType { bitwidth := 64 } =>
      return .byte 64 (← mem.loadByte64 p (alignFor 8))
  | Attribute.llvmPointerType _ =>
      return .addr (mem.ptrOfByte (← mem.loadByte64 p (alignFor 8)))
  | _ => none

end Veir
