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

def MemoryObject.size (obj : MemoryObject) : Nat := obj.contents.size

/--
  Memory state during interpretation: the memory objects, addressed by
  `Pointer` as an object and an offset into it. The flat model has a single
  object, 0, whose offsets are the addresses themselves. Its first eight bytes
  are never allocated, so that no allocation has address 0.
-/
@[ext]
structure MemoryState where
  objects : Array MemoryObject

def MemoryState.empty : MemoryState := { objects := #[MemoryObject.ofSize 8] }

def MemoryState.getObject? (mem : MemoryState) (p : Pointer) : Option MemoryObject :=
  mem.objects[p.object]?

def MemoryState.setObject (mem : MemoryState) (p : Pointer) (obj : MemoryObject) : MemoryState :=
  { mem with objects := mem.objects.setIfInBounds p.object obj }

/--
  Allocate `size` bytes past the end of memory, and return a pointer to their
  start. An allocation past the end of the address space is not a program
  error, so the run fails.
-/
def MemoryState.alloc (mem : MemoryState) (size : Nat) : Interp (MemoryState × Pointer) :=
  match mem.getObject? ⟨0, 0⟩ with
  | none => Interp.fail
  | some obj =>
    if obj.size + size ≥ 2 ^ 64 then Interp.fail else
    return (mem.setObject ⟨0, 0⟩ { obj with
        contents := obj.contents.extend size 0,
        poisonMask := obj.poisonMask.extend size 0xff,
        consistentSize := by simp [obj.consistentSize] },
      ⟨0, obj.size.toUInt64⟩)

/--
  The object that an access of `size` bytes at `p` touches, if the access is
  allowed: the object must exist and the access must stay inside it. An access
  of no bytes is allowed anywhere, even through a pointer to nothing. Later
  conditions on an access are added here.
-/
def MemoryState.checkAccess (mem : MemoryState) (p : Pointer) (size : Nat)
    : Interp MemoryObject :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if size = 0 then return obj
    else if p.offset.toNat + size ≤ obj.contents.size then return obj
    else Interp.ub

/--
  Store raw bytes at `p`, and set the corresponding poison bits as requested
  (by default, unset). Yields UB if the access leaves the object.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) (h : poison.size = val.size := by grind)
    : Interp MemoryState := do
  let obj ← mem.checkAccess p val.size
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

/-- Store the 64 bits of `v`, poison bits included, at `p`. Yields UB if the access leaves the object. -/
def MemoryState.storeByte64 (mem : MemoryState) (p : Pointer) (v : Data.LLVM.Byte 64)
    : Interp MemoryState :=
  mem.store p (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE (by simp)

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
  | .byte 64 v => mem.storeByte64 p v
  | .int n .poison => mem.empoison p (n / 8)
  | .addr q => mem.storeByte64 p q.toByte
  | _ => none

/--
  Load `size` raw bytes at `p`. Yields UB if the access leaves the object.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : Nat) : Interp ByteArray := do
  let obj ← mem.checkAccess p size
  return obj.contents.extract p.offset.toNat (p.offset.toNat + size)

/--
  Load the poison mask of `size` bytes at `p`. Yields UB if the access leaves the object.
-/
def MemoryState.loadPoison (mem : MemoryState) (p : Pointer) (size : Nat) : Interp ByteArray := do
  let obj ← mem.checkAccess p size
  return obj.poisonMask.extract p.offset.toNat (p.offset.toNat + size)

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

/-- Load the 64 bits at `p`, poison bits included. Yields UB if the access leaves the object. -/
def MemoryState.loadByte64 (mem : MemoryState) (p : Pointer) : Interp (Data.LLVM.Byte 64) := do
  let ba ← mem.load p 8
  let baPoison ← mem.loadPoison p 8
  let poison := baPoison.toUInt64LE!.toBitVec
  return ⟨ba.toUInt64LE!.toBitVec &&& ~~~poison, poison, by bv_decide⟩

/--
  Load an LLVM value of type `type` from `p`.
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

/--
  The flat memory model: one object whose offsets are the addresses, with
  every access checked against it.
-/
instance : MemoryModel MemoryState where
  name := "flat"
  initialMemState := MemoryState.empty
  allocateRegion state _align size := state.alloc size
  load state type addr := state.llvmLoad addr type
  store state addr val := state.llvmStore addr val
  validForDerefPtrval state addr size :=
    match state.checkAccess addr size with
    | .ok _ => true
    | _ => false
  arrayShiftPtrval addr bytes := ⟨addr.object, UInt64.ofNat (addr.offset.toNat + bytes)⟩
  ptrFromInt _ i := Data.LLVM.Ptr.ofInt i
  intFromPtr _ p := p.toInt

end Veir
