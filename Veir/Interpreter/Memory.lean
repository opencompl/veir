module

public import Veir.RuntimeValue
public import Veir.Interpreter.Interp

public section

open Veir.Data

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
  no bytes, so every access through a null pointer is out of bounds.
-/
@[ext]
structure MemoryState where
  objects : Array MemoryObject

def MemoryState.empty : MemoryState := ⟨#[MemoryObject.ofSize 0 0]⟩

/-- Every object starts at a multiple of this many bytes. -/
def MemoryState.objectAlignment : UInt64 := 16

/--
  The address at which the next object is placed: past the end of the last
  object with a guard byte, rounded up to `objectAlignment`.
-/
def MemoryState.nextBase (mem : MemoryState) : UInt64 :=
  let last := mem.objects.back?.getD (MemoryObject.ofSize 0 0)
  let past := last.base + last.size.toUInt64 + 1
  (past + objectAlignment - 1) / objectAlignment * objectAlignment

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

/-- Allocate a fresh object of `size` bytes and return a pointer to its start. -/
def MemoryState.alloc (mem : MemoryState) (size : Nat) : MemoryState × Pointer :=
  (⟨mem.objects.push (MemoryObject.ofSize mem.nextBase size)⟩, ⟨mem.objects.size, 0⟩)

/--
  Free the object `p` points to. Freeing the null pointer does nothing, as in
  C; freeing through an offset pointer or a pointer to no object is UB. The
  object is emptied rather than removed, so later accesses to it are UB and
  its address is never reused.
-/
def MemoryState.free (mem : MemoryState) (p : Pointer) : Interp MemoryState :=
  if p.isNull then return mem else
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if p.offset ≠ 0 then Interp.ub else return mem.setObject p (MemoryObject.ofSize obj.base 0)

/--
  Store raw bytes at `p`, and set the corresponding poison bits as requested
  (by default, unset). Yields UB if the access leaves the object.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    : Interp MemoryState :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
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
def MemoryState.empoison (mem : MemoryState) (p : Pointer) (n : Nat) : Interp MemoryState :=
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
  Store an LLVM value at `p`. A pointer is stored as its physical address.
  Yields UB if the access leaves the object or the pointer is null.
-/
def MemoryState.llvmStore (mem : MemoryState) (p : Pointer) (val : RuntimeValue)
    : Interp MemoryState :=
  if p.isNull then Interp.ub else
  match val with
  | .int 8 (.val v) => mem.store p (ByteArray.empty.push (UInt8.ofBitVec v))
  | .int 16 (.val v) => mem.store p (UInt16.ofBitVec v).toByteArrayLE
  | .int 32 (.val v) => mem.store p (UInt32.ofBitVec v).toByteArrayLE
  | .int 64 (.val v) => mem.store p (UInt64.ofBitVec v).toByteArrayLE
  | .byte 64 v => mem.store p (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE (by simp)
  | .int n .poison => mem.empoison p (n / 8)
  | .addr v => mem.store p (mem.address v).toByteArrayLE
  | _ => none

/--
  Load `size` raw bytes at `p`. Yields UB if the access leaves the object.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : Nat) : Interp ByteArray :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if p.offset.toNat + size ≤ obj.contents.size then
      return obj.contents.extract p.offset.toNat (p.offset.toNat + size)
    else
      Interp.ub

/--
  Load the poison mask of `size` bytes at `p`. Yields UB if the access leaves the object.
-/
def MemoryState.loadPoison (mem : MemoryState) (p : Pointer) (size : Nat) : Interp ByteArray :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if p.offset.toNat + size ≤ obj.poisonMask.size then
      return obj.poisonMask.extract p.offset.toNat (p.offset.toNat + size)
    else
      Interp.ub

/--
  Check if any of the `size` bytes at `p` is poison. Yields UB if the access leaves the object.
-/
def MemoryState.hasPoison (mem : MemoryState) (p : Pointer) (size : Nat) : Interp Bool := do
  let poisonMask ← mem.loadPoison p size
  let mut poison := false
  for b in poisonMask do
    if b ≠ 0 then
      poison := true
      break
  return poison

/--
  Load an LLVM value of type `type` from `p`. A pointer is read back from the
  physical address stored in memory.
  Yields UB if the access leaves the object or the pointer is null.
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
      let ba ← mem.load p 8
      let baPoison ← mem.loadPoison p 8
      let poison := baPoison.toUInt64LE!.toBitVec
      return .byte 64 ⟨ba.toUInt64LE!.toBitVec &&& ~~~poison, poison, by bv_decide⟩
  | Attribute.llvmPointerType _ =>
      let ba ← mem.load p 8
      -- FIXME poison address
      if ← mem.hasPoison p 8 then return .addr .null
      return .addr (mem.decode ba.toUInt64LE!)
  | _ => none

end Veir
