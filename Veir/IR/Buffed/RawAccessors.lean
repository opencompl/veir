module

public import ExArray.Basic
public import Std.Data.HashMap
public import Veir.IR.Buffed.Layout

open Std (HashMap)

public section

axiom admitted_bounds : P
axiom admitted_sim {α} (_ : α) : P

@[grind =]
theorem _root_UInt64.toNat_UInt64_ofNat_of_lt {n : Nat} (h : n < UInt64.size) : UInt64.toNat (UInt64.ofNat n) = n := by
  simp_all

-- TODO: move
abbrev _root_.UInt64.toInt (x : UInt64) : Int := x.toNat
abbrev _root_.UInt32.toInt64 (x : UInt32) : Int64 := .ofUInt64 x.toUInt64

attribute [grind =] UInt32.toNat_toUInt64 UInt64.toNat_sub_of_le UInt64.ofNat_toNat
attribute [local grind! .] UInt64.toNat_lt

namespace Veir.Buffed

/-! ## Low-level pointers.
The `MPtr` point to objects, whereas `OPtr` are nullable, with sentinel value `-1`. -/

abbrev ValueImplMPtr := UInt64
abbrev ValueImplOPtr := UInt64
abbrev ValueImplOPtr.none : ValueImplOPtr := -1
@[grind =] theorem ValueImplOPtr.toNat_none : UInt64.toNat ValueImplOPtr.none = 18446744073709551615 := rfl

abbrev OpResultMPtr := UInt64
abbrev OpResultOPtr := UInt64
abbrev OpResultOPtr.none : OpResultOPtr := -1
@[grind =] theorem OpResultOPtr.toNat_none : UInt64.toNat OpResultOPtr.none = 18446744073709551615 := rfl

abbrev BlockArgumentMPtr := UInt64
abbrev BlockArgumentOPtr := UInt64
abbrev BlockArgumentOPtr.none : BlockArgumentOPtr := -1
@[grind =] theorem BlockArgumentOPtr.toNat_none : UInt64.toNat BlockArgumentOPtr.none = 18446744073709551615 := rfl

abbrev OpOperandMPtr := UInt64
abbrev OpOperandOPtr := UInt64
abbrev OpOperandOPtr.none : OpOperandOPtr := -1
@[grind =] theorem OpOperandOPtr.toNat_none : UInt64.toNat OpOperandOPtr.none = 18446744073709551615 := rfl

abbrev BlockOperandMPtr := UInt64
abbrev BlockOperandOPtr := UInt64
abbrev BlockOperandOPtr.none : BlockOperandOPtr := -1
@[grind =] theorem BlockOperandOPtr.toNat_none : UInt64.toNat BlockOperandOPtr.none = 18446744073709551615 := rfl

abbrev OperationMPtr := UInt64
abbrev OperationOPtr := UInt64
abbrev OperationOPtr.none : OperationOPtr := -1
@[grind =] theorem OperationOPtr.toNat_none : UInt64.toNat OperationOPtr.none = 18446744073709551615 := rfl


def OperationOPtr.fromOption (x : Option OperationMPtr) : OperationOPtr :=
  match x with
  | .none => OperationOPtr.none
  | .some ptr => ptr

abbrev BlockMPtr := UInt64
abbrev BlockOPtr := UInt64
abbrev BlockOPtr.none : BlockOPtr := -1
@[grind =] theorem BlockOPtr.toNat_none : UInt64.toNat BlockOPtr.none = 18446744073709551615 := rfl

abbrev RegionMPtr := UInt64
abbrev RegionOPtr := UInt64
abbrev RegionOPtr.none : RegionOPtr := -1
@[grind =] theorem RegionOPtr.toNat_none : UInt64.toNat RegionOPtr.none = 18446744073709551615 := rfl

abbrev OpOperandPtrMPtr := UInt64
abbrev OpOperandPtrOPtr := UInt64
abbrev OpOperandPtrOPtr.none : OpOperandPtrOPtr := -1
@[grind =] theorem OpOperandPtrOPtr.toNat_none : UInt64.toNat OpOperandPtrOPtr.none = 18446744073709551615 := rfl

abbrev BlockOperandPtrMPtr := UInt64
abbrev BlockOperandPtrOPtr := UInt64
abbrev BlockOperandPtrOPtr.none : BlockOperandPtrOPtr := -1
@[grind =] theorem BlockOperandPtrOPtr.toNat_none : UInt64.toNat BlockOperandPtrOPtr.none = 18446744073709551615 := rfl

abbrev GenericMPtr := UInt64
abbrev GenericOPtr := UInt64
abbrev GenericOPtr.none : GenericOPtr := -1
@[grind =] theorem GenericOPtr.toNat_none : UInt64.toNat GenericOPtr.none = 18446744073709551615 := rfl

structure IRBufContext OpInfo [HasOpInfo OpInfo] where
  mem : ExArray
  attributes : Array Attribute
deriving Inhabited

/-! ## Raw accessors -/

variable [HasOpInfo OpInfo] (bctx : IRBufContext OpInfo)

@[inline]
def IRBufContext.size (bctx : IRBufContext OpInfo) : Nat := bctx.mem.size

@[grind =_]
theorem IRBufContext.size_def (bctx : IRBufContext OpInfo) : bctx.size = bctx.mem.size := by rfl

@[grind, inline]
def IRBufContext.usize (bctx : IRBufContext OpInfo) : UInt64 := bctx.mem.usize

@[grind, inline]
def IRBufContext.insertAttrs (bctx : IRBufContext OpInfo) (attrs : Attribute) :
    Option (IRBufContext OpInfo × UInt64) := do
  let idx := bctx.attributes.size
  if idx < UInt64.size then
    let newBctx := { bctx with attributes := bctx.attributes.push attrs }
    some (newBctx, idx.toUInt64)
  else
    none

@[inline] def noOverflowsAdd (x y : UInt64) : Bool := x ≤ x + y

@[inline]
def IRBufContext.alloc (bctx : IRBufContext OpInfo) (size : UInt64) : Option (IRBufContext OpInfo) :=
  if _ : noOverflowsAdd bctx.usize size then
    let mem := bctx.mem.extend size admitted_bounds
    some { bctx with mem }
  else
    none

/-- When `alloc` succeeds it grows the buffer by exactly `size` bytes. -/
@[grind ←]
theorem IRBufContext.alloc_size {bctx bctx' : IRBufContext OpInfo} {size : UInt64}
    (h : bctx.alloc size = some bctx') : bctx'.size = bctx.size + size.toNat := by
  simp only [alloc] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [size_def, ExArray.extend_size]
  · exact absurd h (by simp)

/-- The next allocation pointer `bctx.usize` has `toNat` equal to the current buffer size.
This is the pointer an `alloc` hands back, so it lets alloc-time bounds proofs relate the
pointer address to the buffer size. -/
@[grind =]
theorem IRBufContext.usize_toNat (bctx : IRBufContext OpInfo) :
    bctx.usize.toNat = bctx.size := by
  simp [usize, size_def, ExArray.usize_size_toNat]

/-! ## Raw accessors for `ValueImpl` -/

@[inline]
def ValueImplMPtr.readType (ptr : ValueImplMPtr) (h : ptr.toNat + ValueImpl.Sizes.type.toNat ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 ptr (by grind)

@[inline]
def ValueImplMPtr.writeType (ptr : ValueImplMPtr) (val : UInt64)
    (h : ptr.toNat + ValueImpl.Sizes.type.toNat ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 ptr val (by grind) }

@[inline]
def ValueImplMPtr.readType! (ptr : ValueImplMPtr) : UInt64 :=
  bctx.mem.read64! ptr

@[simp, grind =]
theorem ValueImplMPtr.readType_eq_readType! {ptr : ValueImplMPtr} {h} :
    ptr.readType bctx h = ptr.readType! bctx := by
  simp [ValueImplMPtr.readType, ValueImplMPtr.readType!]

@[inline]
def ValueImplMPtr.readFirstUse (ptr : ValueImplMPtr)
    (h : (ptr + ValueImpl.Offsets.firstUse).toInt + ValueImpl.Sizes.firstUse.toInt ≤ bctx.size) : OpOperandOPtr :=
  bctx.mem.read64 (ptr + ValueImpl.Offsets.firstUse) (by
    constructor
    · grind
    · simp
      grind
  )

@[inline]
def ValueImplMPtr.writeFirstUse (ptr : ValueImplMPtr) (val : OpOperandOPtr)
    (h : (ptr + ValueImpl.Offsets.firstUse).toInt + ValueImpl.Sizes.firstUse.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + ValueImpl.Offsets.firstUse) val (by grind) }

@[inline]
def ValueImplMPtr.readFirstUse! (ptr : ValueImplMPtr) : OpOperandOPtr :=
  bctx.mem.read64! (ptr + ValueImpl.Offsets.firstUse)

@[simp, grind =]
theorem ValueImplMPtr.readFirstUse_eq_readFirstUse! {ptr : ValueImplMPtr} {h} :
    ptr.readFirstUse bctx h = ptr.readFirstUse! bctx := by
  simp [ValueImplMPtr.readFirstUse, ValueImplMPtr.readFirstUse!]

/-! ## Raw accessors for `OpResult` -/

@[inline]
def OpResultMPtr.readType (ptr : OpResultMPtr)
    (h : ptr.toNat + ValueImpl.Sizes.type.toNat ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 ptr (by grind)

@[inline]
def OpResultMPtr.writeType (ptr : OpResultMPtr) (val : UInt64)
    (h : ptr.toNat + ValueImpl.Sizes.type.toNat ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 ptr val (by grind) }

@[inline]
def OpResultMPtr.readType! (ptr : OpResultMPtr) : UInt64 :=
  bctx.mem.read64! ptr

@[simp, grind =]
theorem OpResultMPtr.readType_eq_readType! {ptr : OpResultMPtr} {h} :
    ptr.readType bctx h = ptr.readType! bctx := by
  simp [OpResultMPtr.readType, OpResultMPtr.readType!]

@[inline]
def OpResultMPtr.readFirstUse (ptr : OpResultMPtr)
    (h : (ptr + ValueImpl.Offsets.firstUse).toInt + ValueImpl.Sizes.firstUse.toInt ≤ bctx.size) : OpOperandOPtr :=
  bctx.mem.read64 (ptr + ValueImpl.Offsets.firstUse) (by grind)

@[inline]
def OpResultMPtr.writeFirstUse (ptr : OpResultMPtr) (val : OpOperandOPtr)
    (h : (ptr + ValueImpl.Offsets.firstUse).toInt + ValueImpl.Sizes.firstUse.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + ValueImpl.Offsets.firstUse) val (by grind) }

@[inline]
def OpResultMPtr.readFirstUse! (ptr : OpResultMPtr) : OpOperandOPtr :=
  bctx.mem.read64! (ptr + ValueImpl.Offsets.firstUse)

@[simp, grind =]
theorem OpResultMPtr.readFirstUse_eq_readFirstUse! {ptr : OpResultMPtr} {h} :
    ptr.readFirstUse bctx h = ptr.readFirstUse! bctx := by
  simp [OpResultMPtr.readFirstUse, OpResultMPtr.readFirstUse!]

@[inline]
def OpResultMPtr.readIndex (ptr : OpResultMPtr)
    (h : (ptr + OpResult.Offsets.index).toInt + OpResult.Sizes.index.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + OpResult.Offsets.index) (by grind)

@[inline]
def OpResultMPtr.writeIndex (ptr : OpResultMPtr) (val : UInt64)
    (h : (ptr + OpResult.Offsets.index).toInt + OpResult.Sizes.index.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + OpResult.Offsets.index) val (by grind) }

@[inline]
def OpResultMPtr.readIndex! (ptr : OpResultMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + OpResult.Offsets.index)

@[simp, grind =]
theorem OpResultMPtr.readIndex_eq_readIndex! {ptr : OpResultMPtr} {h} :
    ptr.readIndex bctx h = ptr.readIndex! bctx := by
  simp [OpResultMPtr.readIndex, OpResultMPtr.readIndex!]

@[inline]
def OpResultMPtr.readOwner (ptr : OpResultMPtr)
    (h : (ptr + OpResult.Offsets.owner).toInt + OpResult.Sizes.owner.toInt ≤ bctx.size) : OperationMPtr :=
  bctx.mem.read64 (ptr + OpResult.Offsets.owner) (by grind)

@[inline]
def OpResultMPtr.writeOwner (ptr : OpResultMPtr) (val : OperationMPtr)
    (h : (ptr + OpResult.Offsets.owner).toInt + OpResult.Sizes.owner.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + OpResult.Offsets.owner) val (by grind) }

@[inline]
def OpResultMPtr.readOwner! (ptr : OpResultMPtr) : OperationMPtr :=
  bctx.mem.read64! (ptr + OpResult.Offsets.owner)

@[simp, grind =]
theorem OpResultMPtr.readOwner_eq_readOwner! {ptr : OpResultMPtr} {h} :
    ptr.readOwner bctx h = ptr.readOwner! bctx := by
  simp [OpResultMPtr.readOwner, OpResultMPtr.readOwner!]

/-! ## Raw accessors for `BlockArgument` -/

@[inline]
def BlockArgumentMPtr.readType (ptr : BlockArgumentMPtr)
    (h : ptr.toNat + ValueImpl.Sizes.type.toNat ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 ptr (by grind)

@[inline]
def BlockArgumentMPtr.writeType (ptr : BlockArgumentMPtr) (val : UInt64)
    (h : ptr.toNat + ValueImpl.Sizes.type.toNat ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 ptr val (by grind) }

@[inline]
def BlockArgumentMPtr.readType! (ptr : BlockArgumentMPtr) : UInt64 :=
  bctx.mem.read64! ptr

@[simp, grind =]
theorem BlockArgumentMPtr.readType_eq_readType! {ptr : BlockArgumentMPtr} {h} :
    ptr.readType bctx h = ptr.readType! bctx := by
  simp [BlockArgumentMPtr.readType, BlockArgumentMPtr.readType!]

@[inline]
def BlockArgumentMPtr.readFirstUse (ptr : BlockArgumentMPtr)
    (h : (ptr + ValueImpl.Offsets.firstUse).toInt + ValueImpl.Sizes.firstUse.toInt ≤ bctx.size) : OpOperandOPtr :=
  bctx.mem.read64 (ptr + ValueImpl.Offsets.firstUse) (by grind)

@[inline]
def BlockArgumentMPtr.writeFirstUse (ptr : BlockArgumentMPtr) (val : OpOperandOPtr)
    (h : (ptr + ValueImpl.Offsets.firstUse).toInt + ValueImpl.Sizes.firstUse.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + ValueImpl.Offsets.firstUse) val (by grind) }

@[inline]
def BlockArgumentMPtr.readFirstUse! (ptr : BlockArgumentMPtr) : OpOperandOPtr :=
  bctx.mem.read64! (ptr + ValueImpl.Offsets.firstUse)

@[simp, grind =]
theorem BlockArgumentMPtr.readFirstUse_eq_readFirstUse! {ptr : BlockArgumentMPtr} {h} :
    ptr.readFirstUse bctx h = ptr.readFirstUse! bctx := by
  simp [BlockArgumentMPtr.readFirstUse, BlockArgumentMPtr.readFirstUse!]

@[inline]
def BlockArgumentMPtr.readIndex (ptr : BlockArgumentMPtr)
    (h : (ptr + BlockArgument.Offsets.index).toInt + BlockArgument.Sizes.index.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + BlockArgument.Offsets.index) (by grind)

@[inline]
def BlockArgumentMPtr.writeIndex (ptr : BlockArgumentMPtr) (val : UInt64)
    (h : (ptr + BlockArgument.Offsets.index).toInt + BlockArgument.Sizes.index.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + BlockArgument.Offsets.index) val (by grind) }

@[inline]
def BlockArgumentMPtr.readIndex! (ptr : BlockArgumentMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + BlockArgument.Offsets.index)

@[simp, grind =]
theorem BlockArgumentMPtr.readIndex_eq_readIndex! {ptr : BlockArgumentMPtr} {h} :
    ptr.readIndex bctx h = ptr.readIndex! bctx := by
  simp [BlockArgumentMPtr.readIndex, BlockArgumentMPtr.readIndex!]

@[inline]
def BlockArgumentMPtr.readOwner (ptr : BlockArgumentMPtr)
    (h : (ptr + BlockArgument.Offsets.owner).toInt + BlockArgument.Sizes.owner.toInt ≤ bctx.size) : BlockMPtr :=
  bctx.mem.read64 (ptr + BlockArgument.Offsets.owner) (by grind)

@[inline]
def BlockArgumentMPtr.writeOwner (ptr : BlockArgumentMPtr) (val : BlockMPtr)
    (h : (ptr + BlockArgument.Offsets.owner).toInt + BlockArgument.Sizes.owner.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + BlockArgument.Offsets.owner) val (by grind) }

@[inline]
def BlockArgumentMPtr.readOwner! (ptr : BlockArgumentMPtr) : BlockMPtr :=
  bctx.mem.read64! (ptr + BlockArgument.Offsets.owner)

@[simp, grind =]
theorem BlockArgumentMPtr.readOwner_eq_readOwner! {ptr : BlockArgumentMPtr} {h} :
    ptr.readOwner bctx h = ptr.readOwner! bctx := by
  simp [BlockArgumentMPtr.readOwner, BlockArgumentMPtr.readOwner!]

/-! ## Raw accessors for `OpOperand` -/

@[inline]
def OpOperandMPtr.readNextUse (ptr : OpOperandMPtr)
    (h : (ptr + OpOperand.Offsets.nextUse).toInt + OpOperand.Sizes.nextUse.toInt ≤ bctx.size) : OpOperandOPtr :=
  bctx.mem.read64 (ptr + OpOperand.Offsets.nextUse) (by grind)

@[inline]
def OpOperandMPtr.writeNextUse (ptr : OpOperandMPtr) (val : OpOperandOPtr)
    (h : (ptr + OpOperand.Offsets.nextUse).toInt + OpOperand.Sizes.nextUse.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + OpOperand.Offsets.nextUse) val (by grind) }

@[inline]
def OpOperandMPtr.readNextUse! (ptr : OpOperandMPtr) : OpOperandOPtr :=
  bctx.mem.read64! (ptr + OpOperand.Offsets.nextUse)

@[simp, grind =]
theorem OpOperandMPtr.readNextUse_eq_readNextUse! {ptr : OpOperandMPtr} {h} :
    ptr.readNextUse bctx h = ptr.readNextUse! bctx := by
  simp [OpOperandMPtr.readNextUse, OpOperandMPtr.readNextUse!]

@[inline]
def OpOperandMPtr.readBack (ptr : OpOperandMPtr)
    (h : (ptr + OpOperand.Offsets.back).toInt + OpOperand.Sizes.back.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + OpOperand.Offsets.back) (by grind)

@[inline]
def OpOperandMPtr.writeBack (ptr : OpOperandMPtr) (val : UInt64)
    (h : (ptr + OpOperand.Offsets.back).toInt + OpOperand.Sizes.back.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + OpOperand.Offsets.back) val (by grind) }

@[inline]
def OpOperandMPtr.readBack! (ptr : OpOperandMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + OpOperand.Offsets.back)

@[simp, grind =]
theorem OpOperandMPtr.readBack_eq_readBack! {ptr : OpOperandMPtr} {h} :
    ptr.readBack bctx h = ptr.readBack! bctx := by
  simp [OpOperandMPtr.readBack, OpOperandMPtr.readBack!]

@[inline]
def OpOperandMPtr.readOwner (ptr : OpOperandMPtr)
    (h : (ptr + OpOperand.Offsets.owner).toInt + OpOperand.Sizes.owner.toInt ≤ bctx.size) : OperationMPtr :=
  bctx.mem.read64 (ptr + OpOperand.Offsets.owner) (by grind)

@[inline]
def OpOperandMPtr.writeOwner (ptr : OpOperandMPtr) (val : OperationMPtr)
    (h : (ptr + OpOperand.Offsets.owner).toInt + OpOperand.Sizes.owner.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + OpOperand.Offsets.owner) val (by grind) }

@[inline]
def OpOperandMPtr.readOwner! (ptr : OpOperandMPtr) : OperationMPtr :=
  bctx.mem.read64! (ptr + OpOperand.Offsets.owner)

@[simp, grind =]
theorem OpOperandMPtr.readOwner_eq_readOwner! {ptr : OpOperandMPtr} {h} :
    ptr.readOwner bctx h = ptr.readOwner! bctx := by
  simp [OpOperandMPtr.readOwner, OpOperandMPtr.readOwner!]

@[inline]
def OpOperandMPtr.readValue (ptr : OpOperandMPtr)
    (h : (ptr + OpOperand.Offsets.value).toInt + OpOperand.Sizes.value.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + OpOperand.Offsets.value) (by grind)

@[inline]
def OpOperandMPtr.writeValue (ptr : OpOperandMPtr) (val : UInt64)
    (h : (ptr + OpOperand.Offsets.value).toInt + OpOperand.Sizes.value.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + OpOperand.Offsets.value) val (by grind) }

@[inline]
def OpOperandMPtr.readValue! (ptr : OpOperandMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + OpOperand.Offsets.value)

@[simp, grind =]
theorem OpOperandMPtr.readValue_eq_readValue! {ptr : OpOperandMPtr} {h} :
    ptr.readValue bctx h = ptr.readValue! bctx := by
  simp [OpOperandMPtr.readValue, OpOperandMPtr.readValue!]

/-! ## Raw accessors for `BlockOperand` -/

@[inline]
def BlockOperandMPtr.readNextUse (ptr : BlockOperandMPtr)
    (h : (ptr + BlockOperand.Offsets.nextUse).toInt + BlockOperand.Sizes.nextUse.toInt ≤ bctx.size) : BlockOperandOPtr :=
  bctx.mem.read64 (ptr + BlockOperand.Offsets.nextUse) (by grind)

@[inline]
def BlockOperandMPtr.writeNextUse (ptr : BlockOperandMPtr) (val : BlockOperandOPtr)
    (h : (ptr + BlockOperand.Offsets.nextUse).toInt + BlockOperand.Sizes.nextUse.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + BlockOperand.Offsets.nextUse) val (by grind) }

@[inline]
def BlockOperandMPtr.readNextUse! (ptr : BlockOperandMPtr) : BlockOperandOPtr :=
  bctx.mem.read64! (ptr + BlockOperand.Offsets.nextUse)

@[simp, grind =]
theorem BlockOperandMPtr.readNextUse_eq_readNextUse! {ptr : BlockOperandMPtr} {h} :
    ptr.readNextUse bctx h = ptr.readNextUse! bctx := by
  simp [BlockOperandMPtr.readNextUse, BlockOperandMPtr.readNextUse!]

@[inline]
def BlockOperandMPtr.readBack (ptr : BlockOperandMPtr)
    (h : (ptr + BlockOperand.Offsets.back).toInt + BlockOperand.Sizes.back.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + BlockOperand.Offsets.back) (by grind)

@[inline]
def BlockOperandMPtr.writeBack (ptr : BlockOperandMPtr) (val : UInt64)
    (h : (ptr + BlockOperand.Offsets.back).toInt + BlockOperand.Sizes.back.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + BlockOperand.Offsets.back) val (by grind) }

@[inline]
def BlockOperandMPtr.readBack! (ptr : BlockOperandMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + BlockOperand.Offsets.back)

@[simp, grind =]
theorem BlockOperandMPtr.readBack_eq_readBack! {ptr : BlockOperandMPtr} {h} :
    ptr.readBack bctx h = ptr.readBack! bctx := by
  simp [BlockOperandMPtr.readBack, BlockOperandMPtr.readBack!]

@[inline]
def BlockOperandMPtr.readOwner (ptr : BlockOperandMPtr)
    (h : (ptr + BlockOperand.Offsets.owner).toInt + BlockOperand.Sizes.owner.toInt ≤ bctx.size) : OperationMPtr :=
  bctx.mem.read64 (ptr + BlockOperand.Offsets.owner) (by grind)

@[inline]
def BlockOperandMPtr.writeOwner (ptr : BlockOperandMPtr) (val : OperationMPtr)
    (h : (ptr + BlockOperand.Offsets.owner).toInt + BlockOperand.Sizes.owner.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + BlockOperand.Offsets.owner) val (by grind) }

@[inline]
def BlockOperandMPtr.readOwner! (ptr : BlockOperandMPtr) : OperationMPtr :=
  bctx.mem.read64! (ptr + BlockOperand.Offsets.owner)

@[simp, grind =]
theorem BlockOperandMPtr.readOwner_eq_readOwner! {ptr : BlockOperandMPtr} {h} :
    ptr.readOwner bctx h = ptr.readOwner! bctx := by
  simp [BlockOperandMPtr.readOwner, BlockOperandMPtr.readOwner!]

@[inline]
def BlockOperandMPtr.readValue (ptr : BlockOperandMPtr)
    (h : (ptr + BlockOperand.Offsets.value).toInt + BlockOperand.Sizes.value.toInt ≤ bctx.size) : BlockMPtr :=
  bctx.mem.read64 (ptr + BlockOperand.Offsets.value) (by grind)

@[inline]
def BlockOperandMPtr.writeValue (ptr : BlockOperandMPtr) (val : BlockMPtr)
    (h : (ptr + BlockOperand.Offsets.value).toInt + BlockOperand.Sizes.value.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + BlockOperand.Offsets.value) val (by grind) }

@[inline]
def BlockOperandMPtr.readValue! (ptr : BlockOperandMPtr) : BlockMPtr :=
  bctx.mem.read64! (ptr + BlockOperand.Offsets.value)

@[simp, grind =]
theorem BlockOperandMPtr.readValue_eq_readValue! {ptr : BlockOperandMPtr} {h} :
    ptr.readValue bctx h = ptr.readValue! bctx := by
  simp [BlockOperandMPtr.readValue, BlockOperandMPtr.readValue!]

/-! ## Raw accessors for `Operation` -/

@[inline]
def OperationMPtr.readNumResults (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numResults).toInt + Operation.Sizes.numResults.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.numResults) (by grind)

@[inline]
def OperationMPtr.writeNumResults (ptr : OperationMPtr) (val : UInt64)
    (h : (ptr + Operation.Offsets.numResults).toInt + Operation.Sizes.numResults.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Operation.Offsets.numResults) val (by grind) }

@[inline]
def OperationMPtr.readNumResults! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.numResults)

@[simp, grind =]
theorem OperationMPtr.readNumResults_eq_readNumResults! {ptr : OperationMPtr} {h} :
    ptr.readNumResults bctx h = ptr.readNumResults! bctx := by
  simp [OperationMPtr.readNumResults, OperationMPtr.readNumResults!]

@[inline]
def OperationMPtr.readPrev (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.prev).toInt + Operation.Sizes.prev.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Operation.Offsets.prev) (by grind)

@[inline]
def OperationMPtr.writePrev (ptr : OperationMPtr) (val : OperationOPtr)
    (h : (ptr + Operation.Offsets.prev).toInt + Operation.Sizes.prev.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Operation.Offsets.prev) val (by grind) }

@[inline]
def OperationMPtr.readPrev! (ptr : OperationMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Operation.Offsets.prev)

@[simp, grind =]
theorem OperationMPtr.readPrev_eq_readPrev! {ptr : OperationMPtr} {h} :
    ptr.readPrev bctx h = ptr.readPrev! bctx := by
  simp [OperationMPtr.readPrev, OperationMPtr.readPrev!]

@[inline]
def OperationMPtr.readNext (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.next).toInt + Operation.Sizes.next.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Operation.Offsets.next) (by grind)

@[inline]
def OperationMPtr.writeNext (ptr : OperationMPtr) (val : OperationOPtr)
    (h : (ptr + Operation.Offsets.next).toInt + Operation.Sizes.next.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Operation.Offsets.next) val (by grind) }

@[inline]
def OperationMPtr.readNext! (ptr : OperationMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Operation.Offsets.next)

@[simp, grind =]
theorem OperationMPtr.readNext_eq_readNext! {ptr : OperationMPtr} {h} :
    ptr.readNext bctx h = ptr.readNext! bctx := by
  simp [OperationMPtr.readNext, OperationMPtr.readNext!]

@[inline]
def OperationMPtr.readParent (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.parent).toInt + Operation.Sizes.parent.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Operation.Offsets.parent) (by grind)

@[inline]
def OperationMPtr.writeParent (ptr : OperationMPtr) (val : BlockOPtr)
    (h : (ptr + Operation.Offsets.parent).toInt + Operation.Sizes.parent.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Operation.Offsets.parent) val (by grind) }

@[inline]
def OperationMPtr.readParent! (ptr : OperationMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Operation.Offsets.parent)

@[simp, grind =]
theorem OperationMPtr.readParent_eq_readParent! {ptr : OperationMPtr} {h} :
    ptr.readParent bctx h = ptr.readParent! bctx := by
  simp [OperationMPtr.readParent, OperationMPtr.readParent!]

@[inline]
def OperationMPtr.readOpType (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤ bctx.size) : UInt32 :=
  bctx.mem.read32 (ptr + Operation.Offsets.opType) (by grind)

@[inline]
def OperationMPtr.writeOpType (ptr : OperationMPtr) (val : UInt32)
    (h : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit32 (ptr + Operation.Offsets.opType) val (by grind) }

@[inline]
def OperationMPtr.readOpType! (ptr : OperationMPtr) : UInt32 :=
  bctx.mem.read32! (ptr + Operation.Offsets.opType)

@[simp, grind =]
theorem OperationMPtr.readOpType_eq_readOpType! {ptr : OperationMPtr} {h} :
    ptr.readOpType bctx h = ptr.readOpType! bctx := by
  simp [OperationMPtr.readOpType, OperationMPtr.readOpType!]

@[inline]
def OperationMPtr.readNumBlockOperands (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numBlockOperands).toInt + Operation.Sizes.numBlockOperands.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.numBlockOperands) (by grind)

@[inline]
def OperationMPtr.writeNumBlockOperands (ptr : OperationMPtr) (val : UInt64)
    (h : (ptr + Operation.Offsets.numBlockOperands).toInt + Operation.Sizes.numBlockOperands.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Operation.Offsets.numBlockOperands) val (by grind) }

@[inline]
def OperationMPtr.readNumBlockOperands! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.numBlockOperands)

@[simp, grind =]
theorem OperationMPtr.readNumBlockOperands_eq_readNumBlockOperands! {ptr : OperationMPtr} {h} :
    ptr.readNumBlockOperands bctx h = ptr.readNumBlockOperands! bctx := by
  simp [OperationMPtr.readNumBlockOperands, OperationMPtr.readNumBlockOperands!]

@[inline]
def OperationMPtr.readNumRegions (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numRegions).toInt + Operation.Sizes.numRegions.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.numRegions) (by grind)

@[inline]
def OperationMPtr.writeNumRegions (ptr : OperationMPtr) (val : UInt64)
    (h : (ptr + Operation.Offsets.numRegions).toInt + Operation.Sizes.numRegions.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Operation.Offsets.numRegions) val (by grind) }

@[inline]
def OperationMPtr.readNumRegions! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.numRegions)

@[simp, grind =]
theorem OperationMPtr.readNumRegions_eq_readNumRegions! {ptr : OperationMPtr} {h} :
    ptr.readNumRegions bctx h = ptr.readNumRegions! bctx := by
  simp [OperationMPtr.readNumRegions, OperationMPtr.readNumRegions!]

@[inline]
def OperationMPtr.readNumOperands (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.numOperands) (by grind)

@[inline]
def OperationMPtr.writeNumOperands (ptr : OperationMPtr) (val : UInt64)
    (h : (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Operation.Offsets.numOperands) val (by grind) }

@[inline]
def OperationMPtr.readNumOperands! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.numOperands)

@[simp, grind =]
theorem OperationMPtr.readNumOperands_eq_readNumOperands! {ptr : OperationMPtr} {h} :
    ptr.readNumOperands bctx h = ptr.readNumOperands! bctx := by
  simp [OperationMPtr.readNumOperands, OperationMPtr.readNumOperands!]

@[inline]
def OperationMPtr.readAttrs (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.attrs).toInt + Operation.Sizes.attrs.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Operation.Offsets.attrs) (by grind)

@[inline]
def OperationMPtr.writeAttrs (ptr : OperationMPtr) (val : UInt64)
    (h : (ptr + Operation.Offsets.attrs).toInt + Operation.Sizes.attrs.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Operation.Offsets.attrs) val (by grind) }

@[inline]
def OperationMPtr.readAttrs! (ptr : OperationMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Operation.Offsets.attrs)

@[simp, grind =]
theorem OperationMPtr.readAttrs_eq_readAttrs! {ptr : OperationMPtr} {h} :
    ptr.readAttrs bctx h = ptr.readAttrs! bctx := by
  simp [OperationMPtr.readAttrs, OperationMPtr.readAttrs!]

@[inline]
def OperationMPtr.computeOperandsOffset (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤ bctx.size) : Int64 :=
  let prop := ptr.readOpType bctx h
  Operation.Offsets.properties + (Operation.propertySize (OpInfo := OpInfo) (Operation.decodeOpInfo prop))

@[inline]
def OperationMPtr.computeOperandsOffset! (ptr : OperationMPtr) : Int64 :=
  let prop := ptr.readOpType! bctx
  Operation.Offsets.properties + (Operation.propertySize (OpInfo := OpInfo) (Operation.decodeOpInfo prop))

@[simp, grind =]
theorem OperationMPtr.computeOperandsOffset_eq_computeOperandsOffset! {ptr : OperationMPtr} {h} :
    ptr.computeOperandsOffset bctx h = ptr.computeOperandsOffset! bctx := by
  simp [OperationMPtr.computeOperandsOffset, OperationMPtr.computeOperandsOffset!]

@[inline]
def OperationMPtr.computeOperandOffset (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤ bctx.size) : Int64 :=
  let offset := ptr.computeOperandsOffset bctx h
  offset + (OpOperand.size * idx)

@[inline]
def OperationMPtr.computeOperandOffset! (ptr : OperationMPtr) (idx : UInt64) : Int64 :=
  let offset := ptr.computeOperandsOffset! bctx
  offset + (OpOperand.size * idx)

@[simp, grind =]
theorem OperationMPtr.computeOperandOffset_eq_computeOperandOffset! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.computeOperandOffset bctx idx h = ptr.computeOperandOffset! bctx idx := by
  simp [OperationMPtr.computeOperandOffset, OperationMPtr.computeOperandOffset!]

@[inline]
def OperationMPtr.computeResultsOffset (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numResults).toInt + Operation.Sizes.numResults.toInt ≤ bctx.size) : Int64 :=
  let res := ptr.readNumResults bctx h
  (- res.toInt64 * OpResult.size.toInt64)

@[inline]
def OperationMPtr.computeResultsOffset! (ptr : OperationMPtr) : Int64 :=
  let res := ptr.readNumResults! bctx
  (- res.toInt64 * OpResult.size.toInt64)

@[simp, grind =]
theorem OperationMPtr.computeResultsOffset_eq_computeResultsOffset! {ptr : OperationMPtr} {h} :
    ptr.computeResultsOffset bctx h = ptr.computeResultsOffset! bctx := by
  simp [OperationMPtr.computeResultsOffset, OperationMPtr.computeResultsOffset!]

@[inline]
def OperationMPtr.computeResultOffset (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.numResults).toInt + Operation.Sizes.numResults.toInt ≤ bctx.size) : Int64 :=
  let offset := ptr.computeResultsOffset bctx h
  offset + (OpOperand.size * idx)

@[inline]
def OperationMPtr.computeResultOffset! (ptr : OperationMPtr) (idx : UInt64) : Int64 :=
  let offset := ptr.computeResultsOffset! bctx
  offset + (OpResult.size * idx)

@[simp, grind =]
theorem OperationMPtr.computeResultOffset_eq_computeResultOffset! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.computeResultOffset bctx idx h = ptr.computeResultOffset! bctx idx := by
  simp [OperationMPtr.computeResultOffset, OperationMPtr.computeResultOffset!]

@[inline]
def OperationMPtr.readNthResult (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.numResults).toInt + Operation.Sizes.numResults.toInt ≤ bctx.size) : OpResultMPtr :=
  ptr + ptr.computeResultOffset bctx idx h

@[inline]
def OperationMPtr.readNthResult! (ptr : OperationMPtr) (idx : UInt64) : OpResultMPtr :=
  ptr + ptr.computeResultOffset! bctx idx

@[simp, grind =]
theorem OperationMPtr.readNthResult_eq_readNthResult! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.readNthResult bctx idx h = ptr.readNthResult! bctx idx := by
  simp [readNthResult, readNthResult!]

@[inline]
def OperationMPtr.getResultPtr (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.numResults).toInt + Operation.Sizes.numResults.toInt ≤ bctx.size) : OpResultMPtr :=
  ptr + ptr.computeResultOffset bctx idx h

@[inline]
def OperationMPtr.getResultPtr! (ptr : OperationMPtr) (idx : UInt64) : OpResultMPtr :=
  ptr + ptr.computeResultOffset! bctx idx

@[simp, grind =]
theorem OperationMPtr.getResultPtr_eq_getResultPtr! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.getResultPtr bctx idx h = ptr.getResultPtr! bctx idx := by
  simp [OperationMPtr.getResultPtr, OperationMPtr.getResultPtr!]

@[inline]
def OperationMPtr.computeBlockOperandsOffset (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ bctx.size) : Int64 :=
  have : (Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤
    (Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt := by cbv; constructor
  have : (ptr + Operation.Offsets.opType).toInt + Operation.Sizes.opType.toInt ≤
    (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt := admitted_bounds
  let offset := ptr.computeOperandsOffset bctx (by grind)
  let count := ptr.readNumOperands bctx (by grind)
  offset + (OpOperand.size * count)

@[inline]
def OperationMPtr.computeBlockOperandsOffset! (ptr : OperationMPtr) : Int64 :=
  let offset := ptr.computeOperandsOffset! bctx
  let count := ptr.readNumOperands! bctx
  offset + (OpOperand.size * count)

@[simp, grind =]
theorem OperationMPtr.computeBlockOperandsOffset_eq_computeBlockOperandsOffset! {ptr : OperationMPtr} {h} :
    ptr.computeBlockOperandsOffset bctx h = ptr.computeBlockOperandsOffset! bctx := by
  simp [computeBlockOperandsOffset!, computeBlockOperandsOffset]

@[inline]
def OperationMPtr.computeBlockOperandOffset (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ bctx.size) : Int64 :=
  let offset := ptr.computeBlockOperandsOffset bctx h
  offset + (BlockOperand.size * idx)

@[inline]
def OperationMPtr.computeBlockOperandOffset! (ptr : OperationMPtr) (idx : UInt64) : Int64 :=
  let offset := ptr.computeBlockOperandsOffset! bctx
  offset + (BlockOperand.size * idx)

@[simp, grind =]
theorem OperationMPtr.computeBlockOperandOffset_eq_computeBlockOperandOffset! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.computeBlockOperandOffset bctx idx h = ptr.computeBlockOperandOffset! bctx idx := by
  simp [computeBlockOperandOffset!, computeBlockOperandOffset]

@[inline]
def BlockMPtr.computeBlockSize (numArgs : UInt64) : Int64 :=
  Block.sizeBase + (BlockArgument.size * numArgs) |>.toInt64

/-- As long as `numArgs` fits in a `UInt32` (`countCard = 2^32`), the block size does not
overflow, so its `Nat` value is exactly the base size plus the arguments array. In
particular it is at least `Block.sizeBaseNat`, which is what the field-write bounds need. -/
theorem BlockMPtr.computeBlockSize_toNat (numArgs : UInt64) (h : numArgs.toNat ≤ countCard) :
    (computeBlockSize numArgs).toUInt64.toNat = Block.sizeBaseNat + numArgs.toNat * BlockArgument.sizeNat := by
  have hlt : numArgs.toNat < 2 ^ 64 := UInt64.toNat_lt numArgs
  simp only [computeBlockSize, UInt64.toUInt64_toInt64, countCard, UInt32.size] at *
  rw [UInt64.toNat_add, UInt64.toNat_mul,
    show Block.sizeBase.toNat = 56 from rfl, show BlockArgument.size.toNat = 32 from rfl,
    show Block.sizeBaseNat = 56 from rfl, show BlockArgument.sizeNat = 32 from rfl]
  omega

/-- The number of bytes needed by an operation with the given array sizes and property size. -/
@[inline]
def OperationMPtr.computeOperationSize (numResults numOperands numBlockOperands numRegions propSize : UInt64) : UInt64 :=
    Operation.sizeBase + propSize +
    (OpResult.size * numResults) + (OpOperand.size * numOperands) +
    (BlockOperand.size * numBlockOperands) + (ptrSize * numRegions)

/-- As long as every count and the property size fit in a `UInt32` (`countCard = 2^32`), the
operation size does not overflow, so its `Nat` value is exactly the sum of the base size, the
property size and each array. This is the analogue of `computeBlockSize_toNat` for operations. -/
theorem OperationMPtr.computeOperationSize_toNat
    (numResults numOperands numBlockOperands numRegions propSize : UInt64)
    (hr : numResults.toNat ≤ countCard) (ho : numOperands.toNat ≤ countCard)
    (hbo : numBlockOperands.toNat ≤ countCard) (hreg : numRegions.toNat ≤ countCard)
    (hp : propSize.toNat ≤ countCard) :
    (computeOperationSize numResults numOperands numBlockOperands numRegions propSize).toNat =
      Operation.sizeBase.toNat + propSize.toNat +
      numResults.toNat * OpResult.size.toNat + numOperands.toNat * OpOperand.size.toNat +
      numBlockOperands.toNat * BlockOperand.size.toNat + numRegions.toNat * ptrSize.toNat := by
  have := UInt64.toNat_lt numResults
  have := UInt64.toNat_lt numOperands
  have := UInt64.toNat_lt numBlockOperands
  have := UInt64.toNat_lt numRegions
  have := UInt64.toNat_lt propSize
  simp only [computeOperationSize, countCard, UInt32.size] at *
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add,
    UInt64.toNat_mul, UInt64.toNat_mul, UInt64.toNat_mul, UInt64.toNat_mul,
    show Operation.sizeBase.toNat = 72 from rfl, show OpResult.size.toNat = 32 from rfl,
    show ptrSize.toNat = 8 from rfl]
  omega

@[inline]
def OperationMPtr.readNthBlockOperand (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.numOperands).toInt + Operation.Sizes.numOperands.toInt ≤ bctx.size) : BlockOperandMPtr :=
  ptr + ptr.computeBlockOperandOffset bctx idx h

@[inline]
def OperationMPtr.readNthBlockOperand! (ptr : OperationMPtr) (idx : UInt64) : BlockOperandMPtr :=
  ptr + ptr.computeBlockOperandOffset! bctx idx

@[simp, grind =]
theorem OperationMPtr.readNthBlockOperand_eq_readNthBlockOperand! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.readNthBlockOperand bctx idx h = ptr.readNthBlockOperand! bctx idx := by
  simp [readNthBlockOperand!, readNthBlockOperand]

@[inline]
def OperationMPtr.computeRegionsOffset (ptr : OperationMPtr)
    (h : (ptr + Operation.Offsets.numOperands).toInt +
      Operation.Sizes.numOperands.toInt ≤ bctx.size) : Int64 :=
  let offset := ptr.computeBlockOperandsOffset bctx (by grind)
  let count := ptr.readNumBlockOperands bctx admitted_bounds
  offset + (BlockOperand.size * count)

@[inline]
def OperationMPtr.computeRegionsOffset! (ptr : OperationMPtr) : Int64 :=
  let offset := ptr.computeBlockOperandsOffset! bctx
  let count := ptr.readNumBlockOperands! bctx
  offset + (BlockOperand.size * count)

@[simp, grind =]
theorem OperationMPtr.computeRegionsOffset_eq_computeRegionsOffset! {ptr : OperationMPtr} {h} :
    ptr.computeRegionsOffset bctx h = ptr.computeRegionsOffset! bctx := by
  simp [computeRegionsOffset!, computeRegionsOffset]

@[inline]
def OperationMPtr.computeRegionOffset (ptr : OperationMPtr) (idx : UInt64)
    (h : (ptr + Operation.Offsets.numOperands).toInt +
      Operation.Sizes.numOperands.toInt ≤ bctx.size) : Int64 :=
  let offset := ptr.computeRegionsOffset bctx h
  offset + (ptrSize * idx)

@[inline]
def OperationMPtr.computeRegionOffset! (ptr : OperationMPtr) (idx : UInt64) : Int64 :=
  let offset := ptr.computeRegionsOffset! bctx
  offset + (ptrSize * idx)

@[simp, grind =]
theorem OperationMPtr.computeRegionOffset_eq_computeRegionOffset! {ptr : OperationMPtr} {idx : UInt64} {h} :
    ptr.computeRegionOffset bctx idx h = ptr.computeRegionOffset! bctx idx := by
  simp [computeRegionOffset, computeRegionOffset!]

@[inline]
def OperationMPtr.readNthRegion (ptr : OperationMPtr) (idx : UInt64)
    (h₁ : (ptr + Operation.Offsets.numOperands).toInt +
      Operation.Sizes.numOperands.toInt ≤ bctx.size)
    (h₂ : (ptr + ptr.computeRegionOffset bctx idx h₁).toInt + ptrSize.toInt ≤ bctx.size) : RegionMPtr :=
  bctx.mem.read64 (ptr + ptr.computeRegionOffset bctx idx h₁) (by grind)

@[inline]
def OperationMPtr.writeNthRegion (ptr : OperationMPtr) (idx : UInt64) (val : RegionMPtr)
    (h₁ : (ptr + Operation.Offsets.numOperands).toInt +
      Operation.Sizes.numOperands.toInt ≤ bctx.size)
    (h₂ : (ptr + ptr.computeRegionOffset bctx idx h₁).toInt + ptrSize.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + ptr.computeRegionOffset bctx idx h₁) val (by grind) }

@[inline]
def OperationMPtr.readNthRegion! (ptr : OperationMPtr) (idx : UInt64) : RegionMPtr :=
  bctx.mem.read64! (ptr + ptr.computeRegionOffset! bctx idx)

@[simp, grind =]
theorem OperationMPtr.readNthRegion_eq_readNthRegion! {ptr : OperationMPtr} {idx : UInt64} {h₁ h₂} :
    ptr.readNthRegion bctx idx h₁ h₂ = ptr.readNthRegion! bctx idx := by
  simp [readNthRegion, readNthRegion!]

/-! ## Raw accessors for `Block` -/

@[inline]
def BlockMPtr.readFirstUse (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.firstUse).toInt + Block.Sizes.firstUse.toInt ≤ bctx.size) : BlockOperandOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.firstUse) (by grind)

@[inline]
def BlockMPtr.writeFirstUse (ptr : BlockMPtr) (val : BlockOperandOPtr)
    (h : (ptr + Block.Offsets.firstUse).toInt + Block.Sizes.firstUse.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Block.Offsets.firstUse) val (by grind) }

@[inline]
def BlockMPtr.readFirstUse! (ptr : BlockMPtr) : BlockOperandOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.firstUse)

@[simp, grind =]
theorem BlockMPtr.readFirstUse_eq_readFirstUse! {ptr : BlockMPtr} {h} :
    ptr.readFirstUse bctx h = ptr.readFirstUse! bctx := by
  simp [BlockMPtr.readFirstUse, BlockMPtr.readFirstUse!]

@[inline]
def BlockMPtr.readPrev (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.prev).toInt + Block.Sizes.prev.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.prev) (by grind)

@[inline]
def BlockMPtr.writePrev (ptr : BlockMPtr) (val : BlockOPtr)
    (h : (ptr + Block.Offsets.prev).toInt + Block.Sizes.prev.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Block.Offsets.prev) val (by grind) }

@[inline]
def BlockMPtr.readPrev! (ptr : BlockMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.prev)

@[simp, grind =]
theorem BlockMPtr.readPrev_eq_readPrev! {ptr : BlockMPtr} {h} :
    ptr.readPrev bctx h = ptr.readPrev! bctx := by
  simp [BlockMPtr.readPrev, BlockMPtr.readPrev!]

@[inline]
def BlockMPtr.readNext (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.next).toInt + Block.Sizes.next.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.next) (by grind)

@[inline]
def BlockMPtr.writeNext (ptr : BlockMPtr) (val : BlockOPtr)
    (h : (ptr + Block.Offsets.next).toInt + Block.Sizes.next.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Block.Offsets.next) val (by grind) }

@[inline]
def BlockMPtr.readNext! (ptr : BlockMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.next)

@[simp, grind =]
theorem BlockMPtr.readNext_eq_readNext! {ptr : BlockMPtr} {h} :
    ptr.readNext bctx h = ptr.readNext! bctx := by
  simp [BlockMPtr.readNext, BlockMPtr.readNext!]

@[inline]
def BlockMPtr.readParent (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.parent).toInt + Block.Sizes.parent.toInt ≤ bctx.size) : RegionOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.parent) (by grind)

@[inline]
def BlockMPtr.writeParent (ptr : BlockMPtr) (val : RegionOPtr)
    (h : (ptr + Block.Offsets.parent).toInt + Block.Sizes.parent.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Block.Offsets.parent) val (by grind) }

@[inline]
def BlockMPtr.readParent! (ptr : BlockMPtr) : RegionOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.parent)

@[simp, grind =]
theorem BlockMPtr.readParent_eq_readParent! {ptr : BlockMPtr} {h} :
    ptr.readParent bctx h = ptr.readParent! bctx := by
  simp [BlockMPtr.readParent, BlockMPtr.readParent!]

@[inline]
def BlockMPtr.readFirstOp (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.firstOp).toInt + Block.Sizes.firstOp.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.firstOp) (by grind)

@[inline]
def BlockMPtr.writeFirstOp (ptr : BlockMPtr) (val : OperationOPtr)
    (h : (ptr + Block.Offsets.firstOp).toInt + Block.Sizes.firstOp.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Block.Offsets.firstOp) val (by grind) }

@[inline]
def BlockMPtr.readFirstOp! (ptr : BlockMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.firstOp)

@[simp, grind =]
theorem BlockMPtr.readFirstOp_eq_readFirstOp! {ptr : BlockMPtr} {h} :
    ptr.readFirstOp bctx h = ptr.readFirstOp! bctx := by
  simp [BlockMPtr.readFirstOp, BlockMPtr.readFirstOp!]

@[inline]
def BlockMPtr.readLastOp (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.lastOp).toInt + Block.Sizes.lastOp.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Block.Offsets.lastOp) (by grind)

@[inline]
def BlockMPtr.writeLastOp (ptr : BlockMPtr) (val : OperationOPtr)
    (h : (ptr + Block.Offsets.lastOp).toInt + Block.Sizes.lastOp.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Block.Offsets.lastOp) val (by grind) }

@[inline]
def BlockMPtr.readLastOp! (ptr : BlockMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Block.Offsets.lastOp)

@[simp, grind =]
theorem BlockMPtr.readLastOp_eq_readLastOp! {ptr : BlockMPtr} {h} :
    ptr.readLastOp bctx h = ptr.readLastOp! bctx := by
  simp [BlockMPtr.readLastOp, BlockMPtr.readLastOp!]

@[inline]
def BlockMPtr.readNumArguments (ptr : BlockMPtr)
    (h : (ptr + Block.Offsets.numArguments).toInt + Block.Sizes.numArguments.toInt ≤ bctx.size) : UInt64 :=
  bctx.mem.read64 (ptr + Block.Offsets.numArguments) (by grind)

@[inline]
def BlockMPtr.writeNumArguments (ptr : BlockMPtr) (val : UInt64)
    (h : (ptr + Block.Offsets.numArguments).toInt + Block.Sizes.numArguments.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Block.Offsets.numArguments) val (by grind) }

@[inline]
def BlockMPtr.readNumArguments! (ptr : BlockMPtr) : UInt64 :=
  bctx.mem.read64! (ptr + Block.Offsets.numArguments)

@[simp, grind =]
theorem BlockMPtr.readNumArguments_eq_readNumArguments! {ptr : BlockMPtr} {h} :
    ptr.readNumArguments bctx h = ptr.readNumArguments! bctx := by
  simp [BlockMPtr.readNumArguments, BlockMPtr.readNumArguments!]

@[inline]
def BlockMPtr.computeArgumentOffset (ptr : BlockMPtr) (idx : UInt64)
    (_h : (ptr + Block.Offsets.arguments).toInt + Block.Sizes.numArguments.toInt ≤ bctx.size) : Int64 :=
  Block.Offsets.arguments + (BlockArgument.size * idx)

@[inline]
def BlockMPtr.computeArgumentOffset! (idx : UInt64) : Int64 :=
  Block.Offsets.arguments + (BlockArgument.size * idx)

@[simp, grind =]
theorem BlockMPtr.computeArgumentOffset_eq_computeArgumentOffset! {ptr : BlockMPtr} {idx : UInt64} {h} :
    ptr.computeArgumentOffset bctx idx h = BlockMPtr.computeArgumentOffset! idx := by
  simp [BlockMPtr.computeArgumentOffset, BlockMPtr.computeArgumentOffset!]

@[inline]
def BlockMPtr.getArgumentPtr (ptr : BlockMPtr) (idx : UInt64)
    (h : (ptr + Block.Offsets.arguments).toInt + Block.Sizes.numArguments.toInt ≤ bctx.size) : BlockArgumentMPtr :=
  ptr + ptr.computeArgumentOffset bctx idx h

@[inline]
def BlockMPtr.getArgumentPtr! (ptr : BlockMPtr) (idx : UInt64) : BlockArgumentMPtr :=
  ptr + BlockMPtr.computeArgumentOffset! idx

@[simp, grind =]
theorem BlockMPtr.getArgumentPtr_eq_getArgumentPtr! {ptr : BlockMPtr} {idx : UInt64} {h} :
    ptr.getArgumentPtr bctx idx h = ptr.getArgumentPtr! idx := by
  simp [BlockMPtr.getArgumentPtr, BlockMPtr.getArgumentPtr!]

/-! ## Raw accessors for `Region` -/

@[inline]
def RegionMPtr.readFirstBlock (ptr : RegionMPtr)
    (h : (ptr + Region.Offsets.firstBlock).toInt + Region.Sizes.firstBlock.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Region.Offsets.firstBlock) (by grind)

@[inline]
def RegionMPtr.writeFirstBlock (ptr : RegionMPtr) (val : BlockOPtr)
    (h : (ptr + Region.Offsets.firstBlock).toInt + Region.Sizes.firstBlock.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Region.Offsets.firstBlock) val (by grind) }

@[inline]
def RegionMPtr.readFirstBlock! (ptr : RegionMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Region.Offsets.firstBlock)

@[simp, grind =]
theorem RegionMPtr.readFirstBlock_eq_readFirstBlock! {ptr : RegionMPtr} {h} :
    ptr.readFirstBlock bctx h = ptr.readFirstBlock! bctx := by
  simp [RegionMPtr.readFirstBlock, RegionMPtr.readFirstBlock!]

@[inline]
def RegionMPtr.readLastBlock (ptr : RegionMPtr)
    (h : (ptr + Region.Offsets.lastBlock).toInt + Region.Sizes.lastBlock.toInt ≤ bctx.size) : BlockOPtr :=
  bctx.mem.read64 (ptr + Region.Offsets.lastBlock) (by grind)

@[inline]
def RegionMPtr.writeLastBlock (ptr : RegionMPtr) (val : BlockOPtr)
    (h : (ptr + Region.Offsets.lastBlock).toInt + Region.Sizes.lastBlock.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Region.Offsets.lastBlock) val (by grind) }

@[inline]
def RegionMPtr.readLastBlock! (ptr : RegionMPtr) : BlockOPtr :=
  bctx.mem.read64! (ptr + Region.Offsets.lastBlock)

@[simp, grind =]
theorem RegionMPtr.readLastBlock_eq_readLastBlock! {ptr : RegionMPtr} {h} :
    ptr.readLastBlock bctx h = ptr.readLastBlock! bctx := by
  simp [RegionMPtr.readLastBlock, RegionMPtr.readLastBlock!]

@[inline]
def RegionMPtr.readParent (ptr : RegionMPtr)
    (h : (ptr + Region.Offsets.parent).toInt + Region.Sizes.parent.toInt ≤ bctx.size) : OperationOPtr :=
  bctx.mem.read64 (ptr + Region.Offsets.parent) (by grind)

@[inline]
def RegionMPtr.writeParent (ptr : RegionMPtr) (val : OperationOPtr)
    (h : (ptr + Region.Offsets.parent).toInt + Region.Sizes.parent.toInt ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 (ptr + Region.Offsets.parent) val (by grind) }

@[inline]
def RegionMPtr.readParent! (ptr : RegionMPtr) : OperationOPtr :=
  bctx.mem.read64! (ptr + Region.Offsets.parent)

@[simp, grind =]
theorem RegionMPtr.readParent_eq_readParent! {ptr : RegionMPtr} {h} :
    ptr.readParent bctx h = ptr.readParent! bctx := by
  simp [RegionMPtr.readParent, RegionMPtr.readParent!]

@[inline]
def OpOperandPtrMPtr.write (operandPtr : OpOperandPtrMPtr) (val : OpOperandOPtr)
    (h : operandPtr.toNat + Buffed.ptrSize.toNat ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 operandPtr val (by grind) }

@[inline]
def BlockOperandPtrMPtr.write (operandPtr : BlockOperandPtrMPtr) (val : BlockOperandOPtr)
    (h : operandPtr.toNat + Buffed.ptrSize.toNat ≤ bctx.size) : IRBufContext OpInfo :=
  { bctx with mem := bctx.mem.blit64 operandPtr val (by grind) }


/-! ## Debugging utilities -/

def printO (ptr : UInt64) : String :=
  if ptr = -1 then "null" else s!"0x{ptr.toNat}"

def OperationMPtr.dump (ptr : OperationMPtr) (bctx : IRBufContext OpInfo) : String := Id.run do
  let memSize := bctx.mem.size
  let opType := ptr.readOpType bctx admitted_bounds
  let prev := ptr.readPrev bctx admitted_bounds
  let next := ptr.readNext bctx admitted_bounds
  let parent := ptr.readParent bctx admitted_bounds
  let numResults := ptr.readNumResults bctx admitted_bounds
  let numOperands := ptr.readNumOperands bctx admitted_bounds
  let numBlockOperands := ptr.readNumBlockOperands bctx admitted_bounds
  let numRegions := ptr.readNumRegions bctx admitted_bounds
  let size := Buffed.OperationMPtr.computeOperationSize numResults numOperands numBlockOperands numRegions (Operation.propertySize (OpInfo := OpInfo) (Operation.decodeOpInfo opType))
  let mut regions := ""
  for i in [0: numRegions.toNat] do
    let region := ptr.readNthRegion bctx i.toUInt64 admitted_bounds admitted_bounds
    regions := regions ++ s!"{i} = {printO region}, "
  s!"Operation(opType={opType}, next={printO next}, prev={printO prev}, parent={printO parent}, numResults={numResults}, numOperands={numOperands}, numBlockOperands={numBlockOperands}, numRegions={numRegions}[{regions}]) [Note: addr={ptr}, size={size}, memSize={memSize}, regionsOffset={ptr.computeRegionsOffset bctx admitted_bounds}, blockOperandsOffset={ptr.computeBlockOperandsOffset bctx admitted_bounds}, operandsOffset={ptr.computeOperandsOffset bctx admitted_bounds}]"

def RegionMPtr.dump (ptr : RegionMPtr) (bctx : IRBufContext OpInfo) : String :=
  let memSize := bctx.mem.size
  let firstBlock := ptr.readFirstBlock bctx admitted_bounds
  let lastBlock := ptr.readLastBlock bctx admitted_bounds
  let parent := ptr.readParent bctx admitted_bounds
  s!"Region(firstBlock={printO firstBlock}, lastBlock={printO lastBlock}, parent={printO parent}) [Note: addr={ptr}, memSize={memSize}]"

def BlockMPtr.dump (ptr : BlockMPtr) (bctx : IRBufContext OpInfo) : String :=
  let memSize := bctx.mem.size
  let firstUse := ptr.readFirstUse bctx admitted_bounds
  let prev := ptr.readPrev bctx admitted_bounds
  let next := ptr.readNext bctx admitted_bounds
  let parent := ptr.readParent bctx admitted_bounds
  let firstOp := ptr.readFirstOp bctx admitted_bounds
  let lastOp := ptr.readLastOp bctx admitted_bounds
  let numArguments := ptr.readNumArguments bctx admitted_bounds
  s!"Block(firstUse={printO firstUse}, prev={printO prev}, next={printO next}, parent={printO parent}, firstOp={printO firstOp}, lastOp={printO lastOp}, numArguments={numArguments}) [Note: addr={ptr}, memSize={memSize}]"

def ValueImplMPtr.dump (ptr : ValueImplMPtr) (bctx : IRBufContext OpInfo) : String :=
  let memSize := bctx.mem.size
  let type := ptr.readType bctx admitted_bounds
  let firstUse := ptr.readFirstUse bctx admitted_bounds
  s!"ValueImpl(type={type}, firstUse={printO firstUse}) [Note: addr={ptr}, memSize={memSize}]"

def OpResultMPtr.dump (ptr : OpResultMPtr) (bctx : IRBufContext OpInfo) : String :=
  let memSize := bctx.mem.size
  let type := ptr.readType bctx admitted_bounds
  let firstUse := ptr.readFirstUse bctx admitted_bounds
  let index := ptr.readIndex bctx admitted_bounds
  let owner := ptr.readOwner bctx admitted_bounds
  s!"OpResult(type={type}, firstUse={printO firstUse}, index={index}, owner={printO owner}) [Note: addr={ptr}, memSize={memSize}]"

def BlockArgumentMPtr.dump (ptr : BlockArgumentMPtr) (bctx : IRBufContext OpInfo) : String :=
  let memSize := bctx.mem.size
  let type := ptr.readType bctx admitted_bounds
  let firstUse := ptr.readFirstUse bctx admitted_bounds
  let index := ptr.readIndex bctx admitted_bounds
  let owner := ptr.readOwner bctx admitted_bounds
  s!"BlockArgument(type={type}, firstUse={printO firstUse}, index={index}, owner={printO owner}) [Note: addr={ptr}, memSize={memSize}]"

def OpOperandMPtr.dump (ptr : OpOperandMPtr) (bctx : IRBufContext OpInfo) : String :=
  let memSize := bctx.mem.size
  let nextUse := ptr.readNextUse bctx admitted_bounds
  let back := ptr.readBack bctx admitted_bounds
  let owner := ptr.readOwner bctx admitted_bounds
  let value := ptr.readValue bctx admitted_bounds
  s!"OpOperand(nextUse={printO nextUse}, back={printO back}, owner={printO owner}, value={printO value}) [Note: addr={ptr}, memSize={memSize}]"

def BlockOperandMPtr.dump (ptr : BlockOperandMPtr) (bctx : IRBufContext OpInfo) : String :=
  let memSize := bctx.mem.size
  let nextUse := ptr.readNextUse bctx admitted_bounds
  let back := ptr.readBack bctx admitted_bounds
  let owner := ptr.readOwner bctx admitted_bounds
  let value := ptr.readValue bctx admitted_bounds
  s!"BlockOperand(nextUse={printO nextUse}, back={printO back}, owner={printO owner}, value={printO value}) [Note: addr={ptr}, memSize={memSize}]"

/-- Dump a nullable `OPtr`, printing `null` for the sentinel and otherwise the underlying object.
The `*MPtr.dump` is called by its full name since `MPtr`/`OPtr` are both `UInt64`, so dot notation
on `ptr` would resolve back to this `OPtr.dump` and make it spuriously recursive. -/
def OperationOPtr.dump (ptr : OperationOPtr) (bctx : IRBufContext OpInfo) : String :=
  if ptr = .none then "null" else OperationMPtr.dump ptr bctx

def BlockOPtr.dump (ptr : BlockOPtr) (bctx : IRBufContext OpInfo) : String :=
  if ptr = .none then "null" else BlockMPtr.dump ptr bctx

def RegionOPtr.dump (ptr : RegionOPtr) (bctx : IRBufContext OpInfo) : String :=
  if ptr = .none then "null" else RegionMPtr.dump ptr bctx

def OpOperandOPtr.dump (ptr : OpOperandOPtr) (bctx : IRBufContext OpInfo) : String :=
  if ptr = .none then "null" else OpOperandMPtr.dump ptr bctx

def BlockOperandOPtr.dump (ptr : BlockOperandOPtr) (bctx : IRBufContext OpInfo) : String :=
  if ptr = .none then "null" else BlockOperandMPtr.dump ptr bctx


@[noinline, nospecialize]
def OperationMPtr.debugPrint (pref : String) (ptr : OperationMPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def RegionMPtr.debugPrint (pref : String) (ptr : RegionMPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def BlockMPtr.debugPrint (pref : String) (ptr : BlockMPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def ValueImplMPtr.debugPrint (pref : String) (ptr : ValueImplMPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def OpResultMPtr.debugPrint (pref : String) (ptr : OpResultMPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def BlockArgumentMPtr.debugPrint (pref : String) (ptr : BlockArgumentMPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def OpOperandMPtr.debugPrint (pref : String) (ptr : OpOperandMPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def BlockOperandMPtr.debugPrint (pref : String) (ptr : BlockOperandMPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def OperationOPtr.debugPrint (pref : String) (ptr : OperationOPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def BlockOPtr.debugPrint (pref : String) (ptr : BlockOPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def RegionOPtr.debugPrint (pref : String) (ptr : RegionOPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def OpOperandOPtr.debugPrint (pref : String) (ptr : OpOperandOPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx

@[noinline, nospecialize]
def BlockOperandOPtr.debugPrint (pref : String) (ptr : BlockOperandOPtr) (bctx : IRBufContext OpInfo) := dbg_trace "{pref}: {ptr.dump bctx}"; bctx
