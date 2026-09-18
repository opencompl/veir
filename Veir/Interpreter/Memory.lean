module

public import Veir.RuntimeValue
public import Veir.Interpreter.Interp
public import Veir.Interpreter.MemoryModel

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
  each at the address the oracle names for it, or past every other object
  when it names none, always with at least one guard byte between any two
  objects, so a pointer converts to an address
  (`MemoryState.address`) and an address back to a pointer
  (`MemoryState.decode`). Object 0 is the null object at address 0. It holds
  no bytes, so every access through a null pointer is out of bounds, until
  machine code grows it into the arena below `arenaSize`.
-/
@[ext]
structure MemoryState where
  objects : Array MemoryObject
  /-- The objects in order of their base address. -/
  byAddress : Array Nat := #[0]
  oracle : MemoryOracle := {}
  /-- How many allocations were made so far, to index the oracle. -/
  allocations : Nat := 0

def MemoryState.empty : MemoryState := { objects := #[MemoryObject.ofSize 0 0] }

/-- Every object starts at a multiple of at least this many bytes. -/
def MemoryState.objectAlignment : UInt64 := 16

/--
  The low addresses below which no object is allocated. Machine code may
  address this arena freely: it belongs to the null object, which grows on
  demand under RISC-V accesses.
-/
def MemoryState.arenaSize : UInt64 := 0x10000

/--
  The address at which the model places the next object when the oracle
  names none: past the end of every object with a guard byte and past the
  arena, rounded up to `align` or `objectAlignment`, whichever is larger.
-/
def MemoryState.nextBase (mem : MemoryState) (align : UInt64 := objectAlignment) : UInt64 :=
  let align := max align objectAlignment
  let past := mem.objects.foldl (init := arenaSize) fun past obj =>
    max past (obj.base + obj.size.toUInt64 + 1)
  (past + align - 1) / align * align

/--
  Whether an object of `size` bytes may be placed at `base`: not at null,
  aligned to `align`, above the arena, not wrapping around the address space,
  and separated from every existing object by at least one byte.
-/
def MemoryState.validBase (mem : MemoryState) (base : UInt64) (size : Nat) (align : UInt64) : Bool :=
  base ≠ 0 && base % align == 0 && base ≥ arenaSize && base.toNat + size < 2 ^ 64 &&
  mem.objects.all fun obj =>
    obj.base.toNat + obj.size < base.toNat || base.toNat + size < obj.base.toNat

def MemoryState.getObject? (mem : MemoryState) (p : Pointer) : Option MemoryObject :=
  mem.objects[p.object]?

def MemoryState.setObject (mem : MemoryState) (p : Pointer) (obj : MemoryObject) : MemoryState :=
  { mem with objects := mem.objects.setIfInBounds p.object obj }

/--
  The index of the last object whose base is at most `addr`, found by binary
  search. Objects are sorted by base and object 0 starts at address 0, so
  some object always qualifies.
-/
def MemoryState.objectOfAddress (mem : MemoryState) (addr : UInt64) : Nat := Id.run do
  let baseAt (i : Nat) : UInt64 := (mem.objects[mem.byAddress[i]!]?.map (·.base)).getD 0
  let mut lo := 0
  let mut hi := mem.byAddress.size
  /- Invariant: `baseAt lo ≤ addr`, and `addr < baseAt hi` when
     `hi < byAddress.size`. Each round halves `hi - lo`, so 64 rounds suffice. -/
  for _ in [0:64] do
    if hi - lo ≤ 1 then break
    let mid := (lo + hi) / 2
    if baseAt mid ≤ addr then lo := mid else hi := mid
  return mem.byAddress[lo]!

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
    /- Growth stops at the next object by address. -/
    let wanted := mem.objects.foldl (init := wanted) fun wanted other =>
      if obj.base < other.base then min wanted (other.base - obj.base).toNat else wanted
    mem.setObject p (obj.ensureSize wanted)

/--
  Allocate a fresh object of `size` bytes, aligned to `align`, at the address
  the oracle names for this allocation or where the model would place it,
  and return a pointer to its start. An oracle that names an address the
  object cannot be placed at is not a program error, so the run fails.
-/
def MemoryState.alloc (mem : MemoryState) (size : Nat) (align : UInt64 := objectAlignment)
    : Interp (MemoryState × Pointer) :=
  let align := max align objectAlignment
  let n := mem.allocations
  let base := (mem.oracle.blockAddress n).getD (mem.nextBase align)
  if !mem.validBase base size align then Interp.fail else
  let i := mem.objects.size
  let byAddress :=
    let pos := mem.byAddress.findIdx? fun j => base < (mem.objects[j]?.map (·.base)).getD 0
    mem.byAddress.insertIdx! (pos.getD mem.byAddress.size) i
  return ({ mem with
      objects := mem.objects.push (MemoryObject.ofSize base size),
      byAddress, allocations := n + 1 },
    ⟨i, 0⟩)

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

/-- Store the 64 bits of `v`, poison bits included, at `p`. Yields UB if the access leaves the object. -/
def MemoryState.storeByte64 (mem : MemoryState) (p : Pointer) (v : Data.LLVM.Byte 64)
    : Interp MemoryState :=
  mem.store p (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE (by simp)

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
  | .byte 64 v => mem.storeByte64 p v
  | .int n .poison => mem.empoison p (n / 8)
  | .addr q => mem.storeByte64 p (mem.byteOfPtr q)
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
  Load an LLVM value of type `type` from `p`. A pointer is read back from the
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
      return .addr (mem.ptrOfByte (← mem.loadByte64 p))
  | _ => none

/--
  The block memory model: one object per allocation, sharing an address
  space, with every access checked against its own object.
-/
instance : MemoryModel MemoryState where
  name := "blocks"
  initialMemState oracle := { MemoryState.empty with oracle }
  allocateRegion state align size := state.alloc size align.toUInt64
  load state type addr := state.llvmLoad addr type
  store state addr val := state.llvmStore addr val
  validForDerefPtrval state addr size :=
    match state.checkAccess addr size with
    | .ok _ => true
    | _ => false
  arrayShiftPtrval addr bytes := ⟨addr.object, UInt64.ofNat (addr.offset.toNat + bytes)⟩
  ptrFromInt state
    | .val v => .val (state.decode (UInt64.ofBitVec v))
    | .poison => .poison
  intFromPtr state
    | .val addr => .val (state.address addr).toBitVec
    | .poison => .poison

end Veir
