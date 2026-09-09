module

public import Veir.RuntimeValue
public import Veir.Interpreter.Interp

public section

open Veir.Data

namespace Veir

/--
  One allocation during interpretation: its bytes and a poison mask in which
  set bits mark poison bits.
-/
@[ext]
structure MemoryObject where
  contents : ByteArray
  poisonMask : ByteArray
  consistentSize : contents.size = poisonMask.size

/-- An object of `size` bytes, all of them poison. -/
def MemoryObject.ofSize (size : Nat) : MemoryObject :=
  ⟨ByteArray.replicate size 0, ByteArray.replicate size 0xff, by grind⟩

instance : Inhabited MemoryObject := ⟨MemoryObject.ofSize 0⟩

/-- Grow the object to at least `size` bytes; the new bytes are poison. -/
def MemoryObject.ensureSize (obj : MemoryObject) (size : Nat) : MemoryObject :=
  if obj.contents.size < size then
    ⟨obj.contents.extend (size - obj.contents.size) 0,
      obj.poisonMask.extend (size - obj.contents.size) 0xff,
      by simp [obj.consistentSize]⟩
  else
    obj

/--
  Memory state during interpretation: one object per allocation, addressed by
  `Pointer`. Object 0 is the null object. It holds no bytes, so it exists from
  the start and every access through a null pointer is out of bounds.
-/
@[ext]
structure MemoryState where
  objects : Array MemoryObject

def MemoryState.empty : MemoryState := ⟨#[MemoryObject.ofSize 0]⟩

def MemoryState.getObject? (mem : MemoryState) (p : Pointer) : Option MemoryObject :=
  mem.objects[p.object.toNat]?

def MemoryState.setObject (mem : MemoryState) (p : Pointer) (obj : MemoryObject) : MemoryState :=
  ⟨mem.objects.setIfInBounds p.object.toNat obj⟩

/--
  Grow the object `p` points into so that `size` bytes at `p` are in bounds.
  The RISC-V interpreter uses this to give machine code a memory that never
  faults; LLVM accesses are bounds-checked instead.
-/
def MemoryState.ensureSize (mem : MemoryState) (p : Pointer) (size : Nat) : MemoryState :=
  match mem.getObject? p with
  | some obj => mem.setObject p (obj.ensureSize (p.offset.toNat + size))
  | none => mem

/-- Allocate a fresh object of `size` bytes and return a pointer to its start. -/
def MemoryState.alloc (mem : MemoryState) (size : Nat) : MemoryState × Pointer :=
  (⟨mem.objects.push (MemoryObject.ofSize size)⟩, ⟨mem.objects.size.toUInt32, 0⟩)

/--
  Free the object `p` points to. Freeing the null pointer does nothing, as in
  C; freeing through an offset pointer or a pointer to no object is UB. The
  object is emptied rather than removed, so later accesses to it are UB.
-/
def MemoryState.free (mem : MemoryState) (p : Pointer) : Interp MemoryState :=
  if p.isNull then return mem else
  match mem.getObject? p with
  | none => Interp.ub
  | some _ => if p.offset ≠ 0 then Interp.ub else return mem.setObject p (MemoryObject.ofSize 0)

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
      return mem.setObject p ⟨val.copySlice 0 obj.contents p.offset.toNat val.size false,
        poison.copySlice 0 obj.poisonMask p.offset.toNat val.size false,
        by simp [ByteArray.copySlice_eq_append, obj.consistentSize, h]⟩
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
      return mem.setObject p ⟨obj.contents,
        mask.copySlice 0 obj.poisonMask p.offset.toNat n false,
        by
          have h' : min n mask.size = n := by grind
          have h'' : min p.offset.toNat obj.poisonMask.size = p.offset.toNat := by grind
          simp [ByteArray.copySlice_eq_append, obj.consistentSize, h', h'']
          grind⟩
    else
      Interp.ub

/--
  Store an LLVM value at `p`.
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
  | .addr v => mem.store p v.toUInt64.toByteArrayLE
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
  Load an LLVM value of type `type` from `p`.
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
      return .addr (Pointer.ofUInt64 ba.toUInt64LE!)
  | _ => none

end Veir
