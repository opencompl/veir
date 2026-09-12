module

public import Veir.RuntimeValue
public import Veir.Interpreter.Interp
public import Std.Data.HashMap

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

/-- How an object was allocated, which decides how it may be freed and when it dies. -/
inductive ObjectKind where
  /-- The null object, and objects machine code conjures at unallocated addresses. -/
  | null
  /-- `alloca`: dies at `llvm.intr.lifetime.end` and when its function returns. -/
  | stack
  /-- `malloc` and friends: dies at `free`. -/
  | heap
  /-- `llvm.mlir.global` and functions: lives forever. -/
  | global
deriving Inhabited, Repr, DecidableEq

/--
  One allocation during interpretation: its bytes and the physical address
  `base` at which the object starts, so that byte `i` of the object lives at
  address `base + i`, together with how it was allocated, its alignment,
  whether it is still alive, whether it may be written, and whether its
  address has escaped: been stored to memory, converted to an integer,
  passed to a call or returned. Only escaped objects can be reached by code
  the interpreter does not see, such as an unknown call. Globals are escaped
  from the start.
-/
@[ext]
structure MemoryObject where
  bytes : Array MemoryByte
  base : UInt64
  kind : ObjectKind := .stack
  align : UInt64 := 16
  alive : Bool := true
  isConst : Bool := false
  escaped : Bool := false

/-- An object of `size` bytes at address `base`, all of them poison. -/
def MemoryObject.ofSize (base : UInt64) (size : Nat) (kind : ObjectKind := .stack)
    (align : UInt64 := 16) (isConst : Bool := false) : MemoryObject :=
  { bytes := Array.replicate size .poison, base, kind, align, isConst, escaped := kind = .global }

instance : Inhabited MemoryObject := ⟨MemoryObject.ofSize 0 0 .null⟩

def MemoryObject.size (obj : MemoryObject) : Nat := obj.bytes.size

/-- Grow the object to at least `size` bytes; the new bytes are poison. -/
def MemoryObject.ensureSize (obj : MemoryObject) (size : Nat) : MemoryObject :=
  if obj.bytes.size < size then
    { obj with bytes := obj.bytes ++ Array.replicate (size - obj.bytes.size) .poison }
  else
    obj

/--
  The choices the interpreter makes where the memory model is nondeterministic.
  The interpreter is a function, so every such choice is drawn from the
  oracle, indexed by how many choices of that kind were made before. Refining
  programs are compared under the same oracle.
-/
structure MemoryOracle where
  /-- Whether the `n`-th heap allocation fails and yields null. -/
  allocFails : Nat → Bool := fun _ => false
  /-- The byte the `n`-th unknown call leaves at offset `k` of the escaped object `i`. -/
  havocByte : (n i k : Nat) → MemoryByte := fun _ _ _ => .poison

instance : Inhabited MemoryOracle := ⟨{}⟩

/--
  Memory state during interpretation: one object per allocation, addressed by
  `Pointer`. The objects share one physical address space. They are laid out
  in allocation order, each starting past the end of the previous one with at
  least one guard byte in between, so a pointer converts to an address
  (`MemoryState.address`) and an address back to a pointer
  (`MemoryState.decode`). Object 0 is the null object at address 0. It holds
  no bytes, so every access through a null pointer is out of bounds, until
  machine code grows it into the arena below `arenaSize`.
  `globals` maps a symbol such as `@g` to the object that holds it.
-/
@[ext]
structure MemoryState where
  objects : Array MemoryObject
  globals : Std.HashMap String Nat := {}
  oracle : MemoryOracle := {}
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
  { mem with objects := mem.objects.setIfInBounds p.object obj }

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

/--
  Allocate a fresh object of `size` bytes, aligned to `align`, and return a
  pointer to its start.
-/
def MemoryState.alloc (mem : MemoryState) (size : Nat) (kind : ObjectKind := .stack)
    (align : UInt64 := objectAlignment) (isConst : Bool := false) : MemoryState × Pointer :=
  let align := max align objectAlignment
  ({ mem with objects := mem.objects.push (MemoryObject.ofSize (mem.nextBase align) size kind align isConst) },
   ⟨mem.objects.size, 0⟩)

/--
  Allocate `size` bytes on the heap, as `malloc` does. The oracle decides
  whether the allocation fails, in which case the result is null.
-/
def MemoryState.heapAlloc (mem : MemoryState) (size : Nat) (align : UInt64 := objectAlignment)
    : MemoryState × Pointer :=
  let n := mem.heapAllocs
  let mem := { mem with heapAllocs := n + 1 }
  if mem.oracle.allocFails n then (mem, .null) else mem.alloc size .heap align

/--
  Free the heap object `p` points to. Freeing the null pointer does nothing,
  as in C. Freeing through an offset pointer, a pointer to no object, an
  object that is not on the heap, or an object that is already freed is UB.
  The object dies but keeps its address, which is never reused.
-/
def MemoryState.free (mem : MemoryState) (p : Pointer) : Interp MemoryState :=
  if p.isNull then return mem else
  match mem.getObject? p with
  | none => Interp.ub
  | some obj =>
    if p.offset ≠ 0 ∨ obj.kind ≠ .heap ∨ !obj.alive then Interp.ub
    else return mem.setObject p { obj with alive := false }

/-- Mark the object `p` points into as escaped: its address is now known outside the interpreted code. -/
def MemoryState.escape (mem : MemoryState) (p : Pointer) : MemoryState :=
  match mem.getObject? p with
  | some obj => mem.setObject p { obj with escaped := true }
  | none => mem

/-- Mark the objects that the pointers among `vals` point into as escaped. -/
def MemoryState.escapeValues (mem : MemoryState) (vals : Array RuntimeValue) : MemoryState :=
  vals.foldl (init := mem) fun mem v =>
    match v with
    | .addr p => mem.escape p
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
        { obj with bytes := obj.bytes.mapIdx fun k _ => mem.oracle.havocByte n i k }
      else obj }

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
    else return mem.setObject p { obj with alive := true, bytes := Array.replicate obj.bytes.size .poison }

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
  inside an object that is alive, a write must not target a constant
  object, and the physical address must be a multiple of `align`. An access
  of no bytes is allowed anywhere, even through a dangling pointer.
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
  let stored := (bytes.size.fold (init := obj.bytes) fun i _ acc =>
    acc.setIfInBounds (p.offset.toNat + i) bytes[i]!)
  return mem.setObject p { obj with bytes := stored }

/--
  Store raw bytes at `p`, and set the corresponding poison bits as requested
  (by default, unset). Yields UB if the access leaves the object.
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
  Yields UB if the access leaves the object.
-/
def MemoryState.load (mem : MemoryState) (p : Pointer) (size : Nat) : Interp ByteArray := do
  return (mem.valueBytes (← mem.loadBytes p size)).1

/-- The bytes an LLVM value occupies in memory. A pointer is eight fragments that remember it. -/
def MemoryByte.ofValue (val : RuntimeValue) : Option (Array MemoryByte) :=
  match val with
  | .int 8 (.val v) => some (ofByteArray (ByteArray.empty.push (UInt8.ofBitVec v)))
  | .int 16 (.val v) => some (ofByteArray (UInt16.ofBitVec v).toByteArrayLE)
  | .int 32 (.val v) => some (ofByteArray (UInt32.ofBitVec v).toByteArrayLE)
  | .int 64 (.val v) => some (ofByteArray (UInt64.ofBitVec v).toByteArrayLE)
  | .byte 64 v => some (ofByteArray (UInt64.ofBitVec v.val).toByteArrayLE (UInt64.ofBitVec v.poison).toByteArrayLE)
  | .int n .poison => some (Array.replicate (n / 8) .poison)
  | .addr v => some (fragmentsOf v)
  | _ => none

/--
  Store an LLVM value at `p` with the access's `alignment` attribute, where
  0 stands for the value's natural alignment, its size. Yields UB if the
  access is not allowed (`checkAccess`) or the pointer is null.
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
  An integer load with any poison bit is poison; a `byte` load keeps poison
  per bit. Yields UB if the access is not allowed (`checkAccess`) or the
  pointer is null.
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

end Veir
