module

public import Veir.RuntimeValue
public import Veir.Interpreter.Interp

public section

open Veir.Data

namespace Veir

/--
  One byte of interpreter memory. A byte either holds a value, with set bits
  of `poison` marking poison bits, or one of the eight bytes of a pointer that
  was stored to memory, which remembers the pointer so that loading it back
  keeps its provenance.
-/
inductive MemoryByte where
  | value (bits poison : UInt8)
  | fragment (ptr : Pointer) (index : Fin 8)
deriving Inhabited, Repr, DecidableEq

namespace MemoryByte

/-- A byte all of whose bits are poison. -/
def poison : MemoryByte := .value 0 0xff

/-- The eight bytes that a stored pointer occupies. -/
def fragmentsOf (p : Pointer) : Array MemoryByte := Array.ofFn fun i => .fragment p i

/-- Value bytes for `val`, with the poison mask `poisonMask` (by default, none). -/
def ofByteArray (val : ByteArray) (poisonMask : ByteArray := ByteArray.replicate val.size 0)
    : Array MemoryByte :=
  Array.ofFn fun (i : Fin val.size) => .value val[i] (poisonMask.getD i 0)

/-- Whether `bytes` are, in order, the eight fragments of one pointer. -/
def pointerOf? (bytes : Array MemoryByte) : Option Pointer :=
  match bytes[0]? with
  | some (MemoryByte.fragment p _) => if bytes = fragmentsOf p then some p else none
  | _ => none

end MemoryByte

/--
  One allocation during interpretation: its bytes and the physical address
  `base` at which the object starts, so that byte `i` of the object lives at
  address `base + i`.
-/
@[ext]
structure MemoryObject where
  bytes : Array MemoryByte
  base : UInt64

/-- An object of `size` bytes at address `base`, all of them poison. -/
def MemoryObject.ofSize (base : UInt64) (size : Nat) : MemoryObject :=
  ⟨Array.replicate size .poison, base⟩

instance : Inhabited MemoryObject := ⟨MemoryObject.ofSize 0 0⟩

def MemoryObject.size (obj : MemoryObject) : Nat := obj.bytes.size

/-- Grow the object to at least `size` bytes; the new bytes are poison. -/
def MemoryObject.ensureSize (obj : MemoryObject) (size : Nat) : MemoryObject :=
  if obj.bytes.size < size then
    { obj with bytes := obj.bytes ++ Array.replicate (size - obj.bytes.size) .poison }
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
  The value of a byte as seen by an integer load: a pointer fragment reads as
  the corresponding byte of the pointer's physical address, so pointers leak
  into integers through memory as they do in LLVM.
-/
def MemoryState.byteValue (mem : MemoryState) (b : MemoryByte) : UInt8 × UInt8 :=
  match b with
  | .value bits poison => (bits, poison)
  | .fragment p i => ((mem.address p).toByteArrayLE.getD i 0, 0)

/-- The contents and poison mask of `bytes` as seen by an integer load. -/
def MemoryState.valueBytes (mem : MemoryState) (bytes : Array MemoryByte) : ByteArray × ByteArray :=
  bytes.foldl (init := (ByteArray.emptyWithCapacity bytes.size, ByteArray.emptyWithCapacity bytes.size))
    fun (val, poison) b =>
      let (v, p) := mem.byteValue b
      (val.push v, poison.push p)

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

/-- Store `bytes` at `p`. Yields UB if the access leaves the object. -/
def MemoryState.storeBytes (mem : MemoryState) (p : Pointer) (bytes : Array MemoryByte)
    : Interp MemoryState :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if p.offset.toNat + bytes.size ≤ obj.bytes.size then
      let stored := (bytes.size.fold (init := obj.bytes) fun i _ acc =>
        acc.setIfInBounds (p.offset.toNat + i) bytes[i]!)
      return mem.setObject p { obj with bytes := stored }
    else
      Interp.ub

/--
  Store raw bytes at `p`, and set the corresponding poison bits as requested
  (by default, unset). Yields UB if the access leaves the object.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) : Interp MemoryState :=
  mem.storeBytes p (MemoryByte.ofByteArray val poison)

/--
  Poison `n` bytes starting at `p`. Yields UB if the access leaves the object.
-/
def MemoryState.empoison (mem : MemoryState) (p : Pointer) (n : Nat) : Interp MemoryState :=
  mem.storeBytes p (Array.replicate n .poison)

/-- Load `size` bytes at `p`. Yields UB if the access leaves the object. -/
def MemoryState.loadBytes (mem : MemoryState) (p : Pointer) (size : Nat) : Interp (Array MemoryByte) :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if p.offset.toNat + size ≤ obj.bytes.size then
      return obj.bytes.extract p.offset.toNat (p.offset.toNat + size)
    else
      Interp.ub

/--
  Load `size` raw bytes at `p` as an integer load sees them.
  Yields UB if the access leaves the object.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : Nat) : Interp ByteArray := do
  return (mem.valueBytes (← mem.loadBytes p size)).1

/--
  Load the poison mask of `size` bytes at `p`. Yields UB if the access leaves the object.
-/
def MemoryState.loadPoison (mem : MemoryState) (p : Pointer) (size : Nat) : Interp ByteArray := do
  return (mem.valueBytes (← mem.loadBytes p size)).2

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
  Store an LLVM value at `p`. A pointer is stored as eight fragments that
  remember it. Yields UB if the access leaves the object or the pointer is null.
-/
def MemoryState.llvmStore (mem : MemoryState) (p : Pointer) (val : RuntimeValue)
    : Interp MemoryState :=
  if p.isNull then Interp.ub else
  match val with
  | .int 8 (.val v) => mem.store p (ByteArray.empty.push (UInt8.ofBitVec v))
  | .int 16 (.val v) => mem.store p (UInt16.ofBitVec v).toByteArrayLE
  | .int 32 (.val v) => mem.store p (UInt32.ofBitVec v).toByteArrayLE
  | .int 64 (.val v) => mem.store p (UInt64.ofBitVec v).toByteArrayLE
  | .byte 64 v => mem.store p (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE
  | .int n .poison => mem.empoison p (n / 8)
  | .addr v => mem.storeBytes p (MemoryByte.fragmentsOf v)
  | _ => none

/--
  The pointer that eight bytes of memory denote: the pointer whose fragments
  they are, or, when they are all defined value bytes, the pointer at that
  physical address. Any other mix stands for a poison pointer, which the
  interpreter cannot represent yet and reads as null.
-/
def MemoryState.pointerOfBytes (mem : MemoryState) (bytes : Array MemoryByte) : Pointer :=
  match MemoryByte.pointerOf? bytes with
  | some p => p
  | none =>
    let (val, poison) := mem.valueBytes bytes
    if bytes.all (· matches .value _ _) ∧ poison.toList.all (· == 0) then
      mem.decode val.toUInt64LE!
    else
      -- FIXME poison pointer
      .null

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
      return .addr (mem.pointerOfBytes (← mem.loadBytes p 8))
  | _ => none

end Veir
