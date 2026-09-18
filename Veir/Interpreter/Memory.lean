module

public import Veir.RuntimeValue
public import Veir.Interpreter.Interp
public import Veir.Interpreter.MemoryModel
public import Std.Data.HashMap

public section

open Veir.Data
open Veir.Data.LLVM (Pointer Ptr)

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

/-- The bytes an LLVM value occupies in memory. A pointer is eight fragments that remember it. -/
def ofValue (val : RuntimeValue) : Option (Array MemoryByte) :=
  match val with
  | .int 8 (.val v) => some (ofByteArray (ByteArray.empty.push (UInt8.ofBitVec v)))
  | .int 16 (.val v) => some (ofByteArray (UInt16.ofBitVec v).toByteArrayLE)
  | .int 32 (.val v) => some (ofByteArray (UInt32.ofBitVec v).toByteArrayLE)
  | .int 64 (.val v) => some (ofByteArray (UInt64.ofBitVec v).toByteArrayLE)
  | .byte 64 v =>
      some (ofByteArray (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE)
  | .int n .poison => some (Array.replicate (n / 8) poison)
  | .addr (.val v) => some (fragmentsOf v)
  /- A poison pointer is eight poison bytes: reading a pointer back out of
     them finds no fragment run and no defined value, so it is poison again,
     and reading an integer out of them is poison too. -/
  | .addr .poison => some (Array.replicate 8 poison)
  | _ => none

end MemoryByte

/-- How an object was allocated, which decides how it may be freed and when it dies. -/
inductive ObjectKind where
  /-- The null object, and whatever machine code reaches in the arena. -/
  | null
  /-- `alloca`: dies at `llvm.intr.lifetime.end` and when its function returns. -/
  | stack
  /-- `malloc` and friends: dies at `free`. -/
  | heap
  /-- `llvm.mlir.global` and functions: lives for the whole run. -/
  | global
deriving Inhabited, Repr, DecidableEq

/--
  One allocation during interpretation: its bytes and the physical address
  `base` at which the object starts, so that byte `i` of the object lives at
  address `base + i`, together with how it was allocated, the alignment it
  was given, whether it is still alive, whether it may be written, and
  whether its address has escaped: been stored to memory, converted to an
  integer, passed to a call or returned. Only escaped objects can be reached
  by code the interpreter does not see. Globals are escaped from the start.
-/
@[ext]
structure MemoryObject where
  bytes : Array MemoryByte
  base : UInt64
  kind : ObjectKind := .stack
  align : UInt64 := 16
  /-- Whether the object is still alive: not yet killed. -/
  alive : Bool := true
  isConst : Bool := false
  escaped : Bool := false

/-- An object of `size` bytes at address `base`, all of them poison. -/
def MemoryObject.ofSize (base : UInt64) (size : Nat) (kind : ObjectKind := .stack)
    (align : UInt64 := 16) (isConst : Bool := false) : MemoryObject :=
  { bytes := Array.replicate size .poison, base, kind, align, isConst,
    escaped := kind = .global }

instance : Inhabited MemoryObject := ⟨MemoryObject.ofSize 0 0 .null⟩

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
  /-- `globals` maps a symbol such as `@g` to the object that holds it. -/
  globals : Std.HashMap String Nat := {}
  oracle : MemoryOracle := {}
  /-- How many allocations were made so far, to index the oracle. -/
  allocations : Nat := 0
  /-- How many heap allocations were requested so far, to index the oracle. -/
  heapAllocs : Nat := 0
  /-- How many unknown calls were made so far, to index the oracle. -/
  unknownCalls : Nat := 0

def MemoryState.empty : MemoryState := { objects := #[MemoryObject.ofSize 0 0 .null] }

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
  bytes.foldl
    (init := (ByteArray.emptyWithCapacity bytes.size, ByteArray.emptyWithCapacity bytes.size))
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
    /- Growth stops at the next object by address. -/
    let wanted := mem.objects.foldl (init := wanted) fun wanted other =>
      if obj.base < other.base then min wanted (other.base - obj.base).toNat else wanted
    mem.setObject p (obj.ensureSize wanted)

/--
  Allocate a fresh object of `size` bytes and kind `kind`, aligned to `align`,
  at the address the oracle names for this allocation or where the model
  would place it, and return a pointer to its start. An oracle that names an
  address the object cannot be placed at is not a program error, so the run
  fails.
-/
def MemoryState.alloc (mem : MemoryState) (size : Nat) (kind : ObjectKind := .stack)
    (align : UInt64 := objectAlignment) (isConst : Bool := false) : Interp (MemoryState × Pointer) :=
  let align := max align objectAlignment
  let n := mem.allocations
  let base := (mem.oracle.blockAddress n).getD (mem.nextBase align)
  if !mem.validBase base size align then Interp.fail else
  let i := mem.objects.size
  let byAddress :=
    let pos := mem.byAddress.findIdx? fun j => base < (mem.objects[j]?.map (·.base)).getD 0
    mem.byAddress.insertIdx! (pos.getD mem.byAddress.size) i
  return ({ mem with
      objects := mem.objects.push (MemoryObject.ofSize base size kind align isConst),
      byAddress, allocations := n + 1 },
    ⟨i, 0⟩)

/--
  Allocate `size` bytes on the heap, as `malloc` does. The oracle decides
  whether the allocation fails, in which case the result is null.
-/
def MemoryState.heapAlloc (mem : MemoryState) (size : Nat) (align : UInt64 := objectAlignment)
    : Interp (MemoryState × Pointer) :=
  let n := mem.heapAllocs
  let mem := { mem with heapAllocs := n + 1 }
  if mem.oracle.allocFails n then return (mem, .null) else mem.alloc size .heap align

/-- Kill every stack object allocated since there were `n` objects: they belong to a frame that returns. -/
def MemoryState.killStackObjectsFrom (mem : MemoryState) (n : Nat) : MemoryState :=
  { mem with objects := mem.objects.mapIdx fun i obj =>
      if n ≤ i ∧ obj.kind = .stack then { obj with alive := false } else obj }

/--
  `llvm.intr.lifetime.start`: the stack object `p` points to becomes alive
  again with poison contents. Anything but the start of a stack object is UB.
-/
def MemoryState.lifetimeStart (mem : MemoryState) (p : Pointer) : Interp MemoryState :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if p.offset ≠ 0 ∨ obj.kind ≠ .stack then Interp.ub
    else
      return mem.setObject p
        { obj with alive := true, bytes := Array.replicate obj.bytes.size .poison }

/-- `llvm.intr.lifetime.end`: the stack object `p` points to dies. Anything but the start of a stack object is UB. -/
def MemoryState.lifetimeEnd (mem : MemoryState) (p : Pointer) : Interp MemoryState :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if p.offset ≠ 0 ∨ obj.kind ≠ .stack then Interp.ub
    else return mem.setObject p { obj with alive := false }

/--
  The object that an access of `size` bytes at `p` touches, if the access is
  allowed: the object must exist, an access of at least one byte must stay
  inside an object that is alive, a write must not target a constant object,
  and the physical address must be a multiple of `align`. An access of no
  bytes is allowed anywhere, even through a dangling pointer.
-/
def MemoryState.checkAccess (mem : MemoryState) (p : Pointer) (size : Nat) (write : Bool)
    (align : Nat := 1) : Interp MemoryObject :=
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if size = 0 then return obj
    else if !obj.alive ∨ (write ∧ obj.isConst) then Interp.ub
    else if p.offset.toNat + size > obj.bytes.size then Interp.ub
    else if 1 < align ∧ (mem.address p).toNat % align ≠ 0 then Interp.ub
    else return obj

/-- Store `bytes` at `p`. Yields UB if the access is not allowed (`checkAccess`). -/
def MemoryState.storeBytes (mem : MemoryState) (p : Pointer) (bytes : Array MemoryByte)
    (align : Nat := 1) : Interp MemoryState := do
  let obj ← mem.checkAccess p bytes.size true align
  let stored := bytes.size.fold (init := obj.bytes) fun i _ acc =>
    acc.setIfInBounds (p.offset.toNat + i) bytes[i]!
  return mem.setObject p { obj with bytes := stored }

/--
  Store raw bytes at `p`, and set the corresponding poison bits as requested
  (by default, unset). Yields UB if the access is not allowed.
-/
def MemoryState.store (mem : MemoryState) (p : Pointer) (val : ByteArray)
    (poison : ByteArray := ByteArray.replicate val.size 0) : Interp MemoryState :=
  mem.storeBytes p (MemoryByte.ofByteArray val poison)

/-- Load `size` bytes at `p`. Yields UB if the access is not allowed (`checkAccess`). -/
def MemoryState.loadBytes (mem : MemoryState) (p : Pointer) (size : Nat) (align : Nat := 1)
    : Interp (Array MemoryByte) := do
  let obj ← mem.checkAccess p size false align
  return obj.bytes.extract p.offset.toNat (p.offset.toNat + size)

/--
  Load `size` raw bytes at `p` as an integer load sees them.
  Yields UB if the access is not allowed.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : Nat) : Interp ByteArray := do
  return (mem.valueBytes (← mem.loadBytes p size)).1

/-- Mark the object `p` points into as escaped: its address is now known outside the interpreted code. -/
def MemoryState.escape (mem : MemoryState) (p : Pointer) : MemoryState :=
  match mem.getObject? p with
  | some obj => mem.setObject p { obj with escaped := true }
  | none => mem

/-- Mark the objects that the pointers among `vals` point into as escaped. -/
def MemoryState.escapeValues (mem : MemoryState) (vals : Array RuntimeValue) : MemoryState :=
  vals.foldl (init := mem) fun mem v =>
    match v with
    | .addr (.val p) => mem.escape p
    | _ => mem

/--
  The effect of a call the interpreter knows nothing about: every live,
  writable object whose address has escaped gets the contents the oracle
  chooses, since the callee may have written anything to it.
-/
def MemoryState.havoc (mem : MemoryState) : MemoryState :=
  let n := mem.unknownCalls
  { mem with
    unknownCalls := n + 1,
    objects := mem.objects.mapIdx fun i obj =>
      if obj.escaped ∧ obj.alive ∧ !obj.isConst then
        { obj with bytes := obj.bytes.mapIdx fun k _ =>
            let vp := mem.oracle.havocByte n i k; MemoryByte.value vp.1 vp.2 }
      else obj }

/--
  The pointer whose bits are `b`: poison if any bit is poison, otherwise the
  pointer at that physical address. This is the conversion a bitcast to a
  pointer applies to raw bits, as `Byte.toInt` is for integers.
-/
def MemoryState.ptrOfByte (mem : MemoryState) (b : Data.LLVM.Byte 64) : Ptr :=
  if b.poison = 0 then .val (mem.decode b.toUInt64) else .poison

/-- The bits of a pointer, its physical address: all poison for a poison pointer. -/
def MemoryState.byteOfPtr (mem : MemoryState) : Ptr → Data.LLVM.Byte 64
  | .val p => Data.LLVM.Byte.fromUInt64 (mem.address p)
  | .poison => Data.LLVM.Byte.allPoison

/--
  Store an LLVM value at `p` with the access's `alignment` attribute, where 0
  stands for the value's natural alignment, its size. A pointer is stored as
  eight fragments that remember it.
  Yields UB if the access is not allowed or the pointer is null.
-/
def MemoryState.llvmStore (mem : MemoryState) (p : Pointer) (val : RuntimeValue)
    (alignment : Nat := 0) : Interp MemoryState := do
  if p.isNull then Interp.ub else
  let some bytes := MemoryByte.ofValue val | none
  /- A pointer written to memory has escaped. -/
  let mem := mem.escapeValues #[val]
  mem.storeBytes p bytes (if alignment = 0 then bytes.size else alignment)

/--
  The pointer that eight bytes of memory denote: the pointer whose fragments
  they are, or, when they are all defined value bytes, the pointer at that
  physical address. Any other mix, including a partly overwritten run of
  fragments and a stored poison pointer, is poison.
-/
def MemoryState.pointerOfBytes (mem : MemoryState) (bytes : Array MemoryByte) : Ptr :=
  match MemoryByte.pointerOf? bytes with
  | some p => .val p
  | none =>
    let (val, poison) := mem.valueBytes bytes
    if bytes.all (· matches .value _ _) ∧ poison.toList.all (· == 0) then
      .val (mem.decode val.toUInt64LE!)
    else
      .poison

/-- The size in bytes of an LLVM value of type `type` in memory, for the types loads support. -/
def MemoryState.loadSize? (type : TypeAttr) : Option Nat :=
  match type.val with
  | Attribute.integerType { bitwidth := 8 } => some 1
  | Attribute.integerType { bitwidth := 16 } => some 2
  | Attribute.integerType { bitwidth := 32 } => some 4
  | Attribute.integerType { bitwidth := 64 } => some 8
  | Attribute.byteType { bitwidth := 64 } => some 8
  | Attribute.llvmPointerType _ => some 8
  | _ => none

/--
  Load an LLVM value of type `type` from `p` with the access's `alignment`
  attribute, where 0 stands for the natural alignment of the type, its size.
  An integer or pointer load with any poison bit is poison as a whole, and a
  `byte` load keeps poison per bit. Yields UB if the access is not allowed or
  the pointer is null.

  Together with fresh memory being poison, this is the semantics proposed in
  "Towards Removing Undef Values from LLVM IR" (Lobo et al., PLDI 2026), not
  LangRef's, where uninitialized memory reads as `undef`.
  As Clang relies still on `undef` semantics, e.g., for a bitfield or an integer
  copy of a struct with uninitialized padding, we sometimes introduce UB where
  we should not. The solution is to introduce a freezing load to LLVM and VeIR
  and ensure that all frontends are using them.
-/
def MemoryState.llvmLoad (mem : MemoryState) (p : Pointer) (type : TypeAttr)
    (alignment : Nat := 0) : Interp RuntimeValue := do
  if p.isNull then Interp.ub else
  let some size := loadSize? type | none
  let bytes ← mem.loadBytes p size (if alignment = 0 then size else alignment)
  let (ba, poisonMask) := mem.valueBytes bytes
  let hasPoison := poisonMask.toList.any (· ≠ 0)
  match type.val with
  | Attribute.integerType { bitwidth := 8 } =>
      if hasPoison then return .int 8 .poison
      return .int 8 (.val ba[0]!.toNat)
  | Attribute.integerType { bitwidth := 16 } =>
      if hasPoison then return .int 16 .poison
      return .int 16 (.val (ba.toBitVecLE 2))
  | Attribute.integerType { bitwidth := 32 } =>
      if hasPoison then return .int 32 .poison
      return .int 32 (.val (ba.toBitVecLE 4))
  | Attribute.integerType { bitwidth := 64 } =>
      if hasPoison then return .int 64 .poison
      return .int 64 (.val (BitVec.ofNat 64 ba.toUInt64LE!.toNat))
  | Attribute.byteType { bitwidth := 64 } =>
      let poison := poisonMask.toUInt64LE!.toBitVec
      return .byte 64 ⟨ba.toUInt64LE!.toBitVec &&& ~~~poison, poison, by bv_decide⟩
  | Attribute.llvmPointerType _ =>
      return .addr (mem.pointerOfBytes bytes)
  | _ => none

/--
  The block memory model: one object per allocation, sharing an address
  space, with every access checked against its own object.
-/
instance : MemoryModel MemoryState where
  name := "blocks"
  initialMemState oracle := { MemoryState.empty with oracle }
  allocateObject state align size := state.alloc size .stack align.toUInt64
  allocateRegion state align size := state.heapAlloc size align.toUInt64
  load state type addr align := state.llvmLoad addr type align
  store state addr val align := state.llvmStore addr val align
  validForDerefPtrval state addr size :=
    match state.checkAccess addr size false with
    | .ok _ => true
    | _ => false
  arrayShiftPtrval addr bytes := ⟨addr.object, UInt64.ofNat (addr.offset.toNat + bytes)⟩
  ptrFromInt state
    | .val v => .val (state.decode (UInt64.ofBitVec v))
    | .poison => .poison
  intFromPtr state
    | .val addr => .val (state.address addr).toBitVec
    | .poison => .poison
  memcpy state dst src n := do
    let bytes ← state.loadBytes src n
    state.storeBytes dst bytes
  /- Killing null does nothing, as `free(NULL)` does. Killing through an
     offset pointer, a pointer to no object, an object not on the heap, or
     an object already dead is undefined behaviour. The object dies but
     keeps its address, which is never reused. -/
  kill state p :=
    if p.isNull then return state else
    match state.getObject? p with
    | none => Interp.ub
    | some obj =>
      if p.offset ≠ 0 ∨ obj.kind ≠ .heap ∨ !obj.alive then Interp.ub
      else return state.setObject p { obj with alive := false }
  realloc state align size old := do
    let some obj := state.getObject? old | Interp.ub
    if obj.kind ≠ .heap ∨ !obj.alive then Interp.ub
    let (state, ptr) ← state.alloc size .heap align.toUInt64
    let kept := obj.bytes.extract old.offset.toNat (old.offset.toNat + min (obj.bytes.size - old.offset.toNat) size)
    let state ← state.storeBytes ptr kept
    return (state, ptr)

end Veir
