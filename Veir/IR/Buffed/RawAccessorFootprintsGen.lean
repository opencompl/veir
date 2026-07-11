module

public import Veir.IR.Buffed.FootprintAttr
public import Veir.IR.Buffed.RawAccessors
public import ExArray.NatOps

/-!
# Footprint form of the raw accessors (generated)

For every fixed-offset raw accessor, a lemma rewriting it to the proof-only `Nat`-indexed
`ExArray` shadow operation, so that its memory footprint is a linear-arithmetic interval.
Generated from the accessor definitions in `RawAccessors.lean` — regenerate rather than editing
by hand. The `footprint_grind` set collects these together with the shadow read-after-write
lemmas; it must stay frozen (no product lemmas).
-/

set_option linter.unusedSectionVars false

public section

namespace Veir.Buffed

attribute [footprint_grind =]
  ExArray.read64'_blit64'_self ExArray.read32'_blit32'_self
  ExArray.read64'_blit64'_disjoint ExArray.read64'_blit32'_disjoint
  ExArray.read32'_blit64'_disjoint ExArray.read32'_blit32'_disjoint
  ExArray.blit64'_size ExArray.blit32'_size

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] (bctx : IRBufContext OpInfo)

/-- `Nat`-level version of `UInt64.uint64_add_int64_toInt_lt`: a wrap-free mixed
`UInt64 + Int64` address, with a nonnegative offset, adds up in `Nat`. -/
theorem uint64_add_int64_toNat {a : UInt64} {b : Int64}
    (hnneg : 0 ≤ b.toInt) (ha : (a.toNat : Int) < Int64.maxValue.toInt) :
    (a + b).toNat = a.toNat + b.toInt.toNat := by
  have := UInt64.uint64_add_int64_toInt_lt (a := a) (b := b) (by omega) ha
  simp only [UInt64.toInt] at this
  omega

attribute [local grind =] uint64_add_int64_toNat

@[footprint_grind =]
theorem ValueImplMPtr.writeKind_footprint (ptr : ValueImplMPtr) (val : UInt64) h (hb : ptr.toNat + 8 ≤ bctx.mem.size) :
    ValueImplMPtr.writeKind bctx ptr val h = { bctx with mem := bctx.mem.blit64' ptr.toNat val (by omega) } := by
  grind [ValueImplMPtr.writeKind, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem ValueImplMPtr.readKind!_footprint (ptr : ValueImplMPtr) :
    ValueImplMPtr.readKind! bctx ptr = bctx.mem.read64' ptr.toNat := by
  grind [ValueImplMPtr.readKind!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem ValueImplMPtr.writeType_footprint (ptr : ValueImplMPtr) (val : UInt64) h (hb : ptr.toNat + (ValueImpl.Offsets.typeInt.toNat + 8) ≤ bctx.mem.size) :
    ValueImplMPtr.writeType bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + ValueImpl.Offsets.typeInt.toNat) val (by omega) } := by
  grind [ValueImplMPtr.writeType, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem ValueImplMPtr.readType!_footprint (ptr : ValueImplMPtr) (hb : ptr.toNat + (ValueImpl.Offsets.typeInt.toNat + 8) ≤ bctx.mem.size) :
    ValueImplMPtr.readType! bctx ptr = bctx.mem.read64' (ptr.toNat + ValueImpl.Offsets.typeInt.toNat) := by
  grind [ValueImplMPtr.readType!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem ValueImplMPtr.writeFirstUse_footprint (ptr : ValueImplMPtr) (val : OpOperandOPtr) h (hb : ptr.toNat + (ValueImpl.Offsets.firstUseInt.toNat + 8) ≤ bctx.mem.size) :
    ValueImplMPtr.writeFirstUse bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + ValueImpl.Offsets.firstUseInt.toNat) val (by omega) } := by
  grind [ValueImplMPtr.writeFirstUse, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem ValueImplMPtr.readFirstUse!_footprint (ptr : ValueImplMPtr) (hb : ptr.toNat + (ValueImpl.Offsets.firstUseInt.toNat + 8) ≤ bctx.mem.size) :
    ValueImplMPtr.readFirstUse! bctx ptr = bctx.mem.read64' (ptr.toNat + ValueImpl.Offsets.firstUseInt.toNat) := by
  grind [ValueImplMPtr.readFirstUse!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpResultMPtr.writeKind_footprint (ptr : OpResultMPtr) (val : UInt64) h (hb : ptr.toNat + 8 ≤ bctx.mem.size) :
    OpResultMPtr.writeKind bctx ptr val h = { bctx with mem := bctx.mem.blit64' ptr.toNat val (by omega) } := by
  grind [OpResultMPtr.writeKind, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OpResultMPtr.readKind!_footprint (ptr : OpResultMPtr) :
    OpResultMPtr.readKind! bctx ptr = bctx.mem.read64' ptr.toNat := by
  grind [OpResultMPtr.readKind!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpResultMPtr.writeType_footprint (ptr : OpResultMPtr) (val : UInt64) h (hb : ptr.toNat + (ValueImpl.Offsets.typeInt.toNat + 8) ≤ bctx.mem.size) :
    OpResultMPtr.writeType bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + ValueImpl.Offsets.typeInt.toNat) val (by omega) } := by
  grind [OpResultMPtr.writeType, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OpResultMPtr.readType!_footprint (ptr : OpResultMPtr) (hb : ptr.toNat + (ValueImpl.Offsets.typeInt.toNat + 8) ≤ bctx.mem.size) :
    OpResultMPtr.readType! bctx ptr = bctx.mem.read64' (ptr.toNat + ValueImpl.Offsets.typeInt.toNat) := by
  grind [OpResultMPtr.readType!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpResultMPtr.writeFirstUse_footprint (ptr : OpResultMPtr) (val : OpOperandOPtr) h (hb : ptr.toNat + (ValueImpl.Offsets.firstUseInt.toNat + 8) ≤ bctx.mem.size) :
    OpResultMPtr.writeFirstUse bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + ValueImpl.Offsets.firstUseInt.toNat) val (by omega) } := by
  grind [OpResultMPtr.writeFirstUse, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OpResultMPtr.readFirstUse!_footprint (ptr : OpResultMPtr) (hb : ptr.toNat + (ValueImpl.Offsets.firstUseInt.toNat + 8) ≤ bctx.mem.size) :
    OpResultMPtr.readFirstUse! bctx ptr = bctx.mem.read64' (ptr.toNat + ValueImpl.Offsets.firstUseInt.toNat) := by
  grind [OpResultMPtr.readFirstUse!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpResultMPtr.writeIndex_footprint (ptr : OpResultMPtr) (val : UInt64) h (hb : ptr.toNat + (OpResult.Offsets.indexInt.toNat + 8) ≤ bctx.mem.size) :
    OpResultMPtr.writeIndex bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + OpResult.Offsets.indexInt.toNat) val (by omega) } := by
  grind [OpResultMPtr.writeIndex, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OpResultMPtr.readIndex!_footprint (ptr : OpResultMPtr) (hb : ptr.toNat + (OpResult.Offsets.indexInt.toNat + 8) ≤ bctx.mem.size) :
    OpResultMPtr.readIndex! bctx ptr = bctx.mem.read64' (ptr.toNat + OpResult.Offsets.indexInt.toNat) := by
  grind [OpResultMPtr.readIndex!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpResultMPtr.writeOwner_footprint (ptr : OpResultMPtr) (val : OperationMPtr) h (hb : ptr.toNat + (OpResult.Offsets.ownerInt.toNat + 8) ≤ bctx.mem.size) :
    OpResultMPtr.writeOwner bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + OpResult.Offsets.ownerInt.toNat) val (by omega) } := by
  grind [OpResultMPtr.writeOwner, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OpResultMPtr.readOwner!_footprint (ptr : OpResultMPtr) (hb : ptr.toNat + (OpResult.Offsets.ownerInt.toNat + 8) ≤ bctx.mem.size) :
    OpResultMPtr.readOwner! bctx ptr = bctx.mem.read64' (ptr.toNat + OpResult.Offsets.ownerInt.toNat) := by
  grind [OpResultMPtr.readOwner!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockArgumentMPtr.writeKind_footprint (ptr : BlockArgumentMPtr) (val : UInt64) h (hb : ptr.toNat + 8 ≤ bctx.mem.size) :
    BlockArgumentMPtr.writeKind bctx ptr val h = { bctx with mem := bctx.mem.blit64' ptr.toNat val (by omega) } := by
  grind [BlockArgumentMPtr.writeKind, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockArgumentMPtr.readKind!_footprint (ptr : BlockArgumentMPtr) :
    BlockArgumentMPtr.readKind! bctx ptr = bctx.mem.read64' ptr.toNat := by
  grind [BlockArgumentMPtr.readKind!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockArgumentMPtr.writeType_footprint (ptr : BlockArgumentMPtr) (val : UInt64) h (hb : ptr.toNat + (ValueImpl.Offsets.typeInt.toNat + 8) ≤ bctx.mem.size) :
    BlockArgumentMPtr.writeType bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + ValueImpl.Offsets.typeInt.toNat) val (by omega) } := by
  grind [BlockArgumentMPtr.writeType, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockArgumentMPtr.readType!_footprint (ptr : BlockArgumentMPtr) (hb : ptr.toNat + (ValueImpl.Offsets.typeInt.toNat + 8) ≤ bctx.mem.size) :
    BlockArgumentMPtr.readType! bctx ptr = bctx.mem.read64' (ptr.toNat + ValueImpl.Offsets.typeInt.toNat) := by
  grind [BlockArgumentMPtr.readType!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockArgumentMPtr.writeFirstUse_footprint (ptr : BlockArgumentMPtr) (val : OpOperandOPtr) h (hb : ptr.toNat + (ValueImpl.Offsets.firstUseInt.toNat + 8) ≤ bctx.mem.size) :
    BlockArgumentMPtr.writeFirstUse bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + ValueImpl.Offsets.firstUseInt.toNat) val (by omega) } := by
  grind [BlockArgumentMPtr.writeFirstUse, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockArgumentMPtr.readFirstUse!_footprint (ptr : BlockArgumentMPtr) (hb : ptr.toNat + (ValueImpl.Offsets.firstUseInt.toNat + 8) ≤ bctx.mem.size) :
    BlockArgumentMPtr.readFirstUse! bctx ptr = bctx.mem.read64' (ptr.toNat + ValueImpl.Offsets.firstUseInt.toNat) := by
  grind [BlockArgumentMPtr.readFirstUse!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockArgumentMPtr.writeIndex_footprint (ptr : BlockArgumentMPtr) (val : UInt64) h (hb : ptr.toNat + (BlockArgument.Offsets.indexInt.toNat + 8) ≤ bctx.mem.size) :
    BlockArgumentMPtr.writeIndex bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + BlockArgument.Offsets.indexInt.toNat) val (by omega) } := by
  grind [BlockArgumentMPtr.writeIndex, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockArgumentMPtr.readIndex!_footprint (ptr : BlockArgumentMPtr) (hb : ptr.toNat + (BlockArgument.Offsets.indexInt.toNat + 8) ≤ bctx.mem.size) :
    BlockArgumentMPtr.readIndex! bctx ptr = bctx.mem.read64' (ptr.toNat + BlockArgument.Offsets.indexInt.toNat) := by
  grind [BlockArgumentMPtr.readIndex!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockArgumentMPtr.writeOwner_footprint (ptr : BlockArgumentMPtr) (val : BlockMPtr) h (hb : ptr.toNat + (BlockArgument.Offsets.ownerInt.toNat + 8) ≤ bctx.mem.size) :
    BlockArgumentMPtr.writeOwner bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + BlockArgument.Offsets.ownerInt.toNat) val (by omega) } := by
  grind [BlockArgumentMPtr.writeOwner, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockArgumentMPtr.readOwner!_footprint (ptr : BlockArgumentMPtr) (hb : ptr.toNat + (BlockArgument.Offsets.ownerInt.toNat + 8) ≤ bctx.mem.size) :
    BlockArgumentMPtr.readOwner! bctx ptr = bctx.mem.read64' (ptr.toNat + BlockArgument.Offsets.ownerInt.toNat) := by
  grind [BlockArgumentMPtr.readOwner!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpOperandMPtr.writeNextUse_footprint (ptr : OpOperandMPtr) (val : OpOperandOPtr) h (hb : ptr.toNat + (OpOperand.Offsets.nextUseInt.toNat + 8) ≤ bctx.mem.size) :
    OpOperandMPtr.writeNextUse bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + OpOperand.Offsets.nextUseInt.toNat) val (by omega) } := by
  grind [OpOperandMPtr.writeNextUse, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OpOperandMPtr.readNextUse!_footprint (ptr : OpOperandMPtr) :
    OpOperandMPtr.readNextUse! bctx ptr = bctx.mem.read64' (ptr.toNat + OpOperand.Offsets.nextUseInt.toNat) := by
  grind [OpOperandMPtr.readNextUse!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpOperandMPtr.writeBack_footprint (ptr : OpOperandMPtr) (val : UInt64) h (hb : ptr.toNat + (OpOperand.Offsets.backInt.toNat + 8) ≤ bctx.mem.size) :
    OpOperandMPtr.writeBack bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + OpOperand.Offsets.backInt.toNat) val (by omega) } := by
  grind [OpOperandMPtr.writeBack, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OpOperandMPtr.readBack!_footprint (ptr : OpOperandMPtr) (hb : ptr.toNat + (OpOperand.Offsets.backInt.toNat + 8) ≤ bctx.mem.size) :
    OpOperandMPtr.readBack! bctx ptr = bctx.mem.read64' (ptr.toNat + OpOperand.Offsets.backInt.toNat) := by
  grind [OpOperandMPtr.readBack!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpOperandMPtr.writeOwner_footprint (ptr : OpOperandMPtr) (val : OperationMPtr) h (hb : ptr.toNat + (OpOperand.Offsets.ownerInt.toNat + 8) ≤ bctx.mem.size) :
    OpOperandMPtr.writeOwner bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + OpOperand.Offsets.ownerInt.toNat) val (by omega) } := by
  grind [OpOperandMPtr.writeOwner, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OpOperandMPtr.readOwner!_footprint (ptr : OpOperandMPtr) (hb : ptr.toNat + (OpOperand.Offsets.ownerInt.toNat + 8) ≤ bctx.mem.size) :
    OpOperandMPtr.readOwner! bctx ptr = bctx.mem.read64' (ptr.toNat + OpOperand.Offsets.ownerInt.toNat) := by
  grind [OpOperandMPtr.readOwner!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpOperandMPtr.writeValue_footprint (ptr : OpOperandMPtr) (val : UInt64) h (hb : ptr.toNat + (OpOperand.Offsets.valueInt.toNat + 8) ≤ bctx.mem.size) :
    OpOperandMPtr.writeValue bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + OpOperand.Offsets.valueInt.toNat) val (by omega) } := by
  grind [OpOperandMPtr.writeValue, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OpOperandMPtr.readValue!_footprint (ptr : OpOperandMPtr) (hb : ptr.toNat + (OpOperand.Offsets.valueInt.toNat + 8) ≤ bctx.mem.size) :
    OpOperandMPtr.readValue! bctx ptr = bctx.mem.read64' (ptr.toNat + OpOperand.Offsets.valueInt.toNat) := by
  grind [OpOperandMPtr.readValue!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockOperandMPtr.writeNextUse_footprint (ptr : BlockOperandMPtr) (val : BlockOperandOPtr) h (hb : ptr.toNat + (BlockOperand.Offsets.nextUseInt.toNat + 8) ≤ bctx.mem.size) :
    BlockOperandMPtr.writeNextUse bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + BlockOperand.Offsets.nextUseInt.toNat) val (by omega) } := by
  grind [BlockOperandMPtr.writeNextUse, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockOperandMPtr.readNextUse!_footprint (ptr : BlockOperandMPtr) :
    BlockOperandMPtr.readNextUse! bctx ptr = bctx.mem.read64' (ptr.toNat + BlockOperand.Offsets.nextUseInt.toNat) := by
  grind [BlockOperandMPtr.readNextUse!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockOperandMPtr.writeBack_footprint (ptr : BlockOperandMPtr) (val : UInt64) h (hb : ptr.toNat + (BlockOperand.Offsets.backInt.toNat + 8) ≤ bctx.mem.size) :
    BlockOperandMPtr.writeBack bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + BlockOperand.Offsets.backInt.toNat) val (by omega) } := by
  grind [BlockOperandMPtr.writeBack, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockOperandMPtr.readBack!_footprint (ptr : BlockOperandMPtr) (hb : ptr.toNat + (BlockOperand.Offsets.backInt.toNat + 8) ≤ bctx.mem.size) :
    BlockOperandMPtr.readBack! bctx ptr = bctx.mem.read64' (ptr.toNat + BlockOperand.Offsets.backInt.toNat) := by
  grind [BlockOperandMPtr.readBack!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockOperandMPtr.writeOwner_footprint (ptr : BlockOperandMPtr) (val : OperationMPtr) h (hb : ptr.toNat + (BlockOperand.Offsets.ownerInt.toNat + 8) ≤ bctx.mem.size) :
    BlockOperandMPtr.writeOwner bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + BlockOperand.Offsets.ownerInt.toNat) val (by omega) } := by
  grind [BlockOperandMPtr.writeOwner, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockOperandMPtr.readOwner!_footprint (ptr : BlockOperandMPtr) (hb : ptr.toNat + (BlockOperand.Offsets.ownerInt.toNat + 8) ≤ bctx.mem.size) :
    BlockOperandMPtr.readOwner! bctx ptr = bctx.mem.read64' (ptr.toNat + BlockOperand.Offsets.ownerInt.toNat) := by
  grind [BlockOperandMPtr.readOwner!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockOperandMPtr.writeValue_footprint (ptr : BlockOperandMPtr) (val : BlockMPtr) h (hb : ptr.toNat + (BlockOperand.Offsets.valueInt.toNat + 8) ≤ bctx.mem.size) :
    BlockOperandMPtr.writeValue bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + BlockOperand.Offsets.valueInt.toNat) val (by omega) } := by
  grind [BlockOperandMPtr.writeValue, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockOperandMPtr.readValue!_footprint (ptr : BlockOperandMPtr) (hb : ptr.toNat + (BlockOperand.Offsets.valueInt.toNat + 8) ≤ bctx.mem.size) :
    BlockOperandMPtr.readValue! bctx ptr = bctx.mem.read64' (ptr.toNat + BlockOperand.Offsets.valueInt.toNat) := by
  grind [BlockOperandMPtr.readValue!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OperationMPtr.writeNumResults_footprint (ptr : OperationMPtr) (val : UInt64) h (hb : ptr.toNat + (Operation.Offsets.numResultsInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.writeNumResults bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Operation.Offsets.numResultsInt.toNat) val (by omega) } := by
  grind [OperationMPtr.writeNumResults, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OperationMPtr.readNumResults!_footprint (ptr : OperationMPtr) :
    OperationMPtr.readNumResults! bctx ptr = bctx.mem.read64' (ptr.toNat + Operation.Offsets.numResultsInt.toNat) := by
  grind [OperationMPtr.readNumResults!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OperationMPtr.writePrev_footprint (ptr : OperationMPtr) (val : OperationOPtr) h (hb : ptr.toNat + (Operation.Offsets.prevInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.writePrev bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Operation.Offsets.prevInt.toNat) val (by omega) } := by
  grind [OperationMPtr.writePrev, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OperationMPtr.readPrev!_footprint (ptr : OperationMPtr) (hb : ptr.toNat + (Operation.Offsets.prevInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.readPrev! bctx ptr = bctx.mem.read64' (ptr.toNat + Operation.Offsets.prevInt.toNat) := by
  grind [OperationMPtr.readPrev!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OperationMPtr.writeNext_footprint (ptr : OperationMPtr) (val : OperationOPtr) h (hb : ptr.toNat + (Operation.Offsets.nextInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.writeNext bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Operation.Offsets.nextInt.toNat) val (by omega) } := by
  grind [OperationMPtr.writeNext, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OperationMPtr.readNext!_footprint (ptr : OperationMPtr) (hb : ptr.toNat + (Operation.Offsets.nextInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.readNext! bctx ptr = bctx.mem.read64' (ptr.toNat + Operation.Offsets.nextInt.toNat) := by
  grind [OperationMPtr.readNext!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OperationMPtr.writeParent_footprint (ptr : OperationMPtr) (val : BlockOPtr) h (hb : ptr.toNat + (Operation.Offsets.parentInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.writeParent bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Operation.Offsets.parentInt.toNat) val (by omega) } := by
  grind [OperationMPtr.writeParent, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OperationMPtr.readParent!_footprint (ptr : OperationMPtr) (hb : ptr.toNat + (Operation.Offsets.parentInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.readParent! bctx ptr = bctx.mem.read64' (ptr.toNat + Operation.Offsets.parentInt.toNat) := by
  grind [OperationMPtr.readParent!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OperationMPtr.writeOpType_footprint (ptr : OperationMPtr) (val : UInt32) h (hb : ptr.toNat + (Operation.Offsets.opTypeInt.toNat + 4) ≤ bctx.mem.size) :
    OperationMPtr.writeOpType bctx ptr val h = { bctx with mem := bctx.mem.blit32' (ptr.toNat + Operation.Offsets.opTypeInt.toNat) val (by omega) } := by
  grind [OperationMPtr.writeOpType, ExArray.blit32_eq_blit32']

@[footprint_grind =]
theorem OperationMPtr.readOpType!_footprint (ptr : OperationMPtr) (hb : ptr.toNat + (Operation.Offsets.opTypeInt.toNat + 4) ≤ bctx.mem.size) :
    OperationMPtr.readOpType! bctx ptr = bctx.mem.read32' (ptr.toNat + Operation.Offsets.opTypeInt.toNat) := by
  grind [OperationMPtr.readOpType!, ExArray.read32!_eq_read32']

@[footprint_grind =]
theorem OperationMPtr.writeNumBlockOperands_footprint (ptr : OperationMPtr) (val : UInt64) h (hb : ptr.toNat + (Operation.Offsets.numBlockOperandsInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.writeNumBlockOperands bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Operation.Offsets.numBlockOperandsInt.toNat) val (by omega) } := by
  grind [OperationMPtr.writeNumBlockOperands, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OperationMPtr.readNumBlockOperands!_footprint (ptr : OperationMPtr) (hb : ptr.toNat + (Operation.Offsets.numBlockOperandsInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.readNumBlockOperands! bctx ptr = bctx.mem.read64' (ptr.toNat + Operation.Offsets.numBlockOperandsInt.toNat) := by
  grind [OperationMPtr.readNumBlockOperands!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OperationMPtr.writeNumRegions_footprint (ptr : OperationMPtr) (val : UInt64) h (hb : ptr.toNat + (Operation.Offsets.numRegionsInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.writeNumRegions bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Operation.Offsets.numRegionsInt.toNat) val (by omega) } := by
  grind [OperationMPtr.writeNumRegions, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OperationMPtr.readNumRegions!_footprint (ptr : OperationMPtr) (hb : ptr.toNat + (Operation.Offsets.numRegionsInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.readNumRegions! bctx ptr = bctx.mem.read64' (ptr.toNat + Operation.Offsets.numRegionsInt.toNat) := by
  grind [OperationMPtr.readNumRegions!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OperationMPtr.writeNumOperands_footprint (ptr : OperationMPtr) (val : UInt64) h (hb : ptr.toNat + (Operation.Offsets.numOperandsInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.writeNumOperands bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Operation.Offsets.numOperandsInt.toNat) val (by omega) } := by
  grind [OperationMPtr.writeNumOperands, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OperationMPtr.readNumOperands!_footprint (ptr : OperationMPtr) (hb : ptr.toNat + (Operation.Offsets.numOperandsInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.readNumOperands! bctx ptr = bctx.mem.read64' (ptr.toNat + Operation.Offsets.numOperandsInt.toNat) := by
  grind [OperationMPtr.readNumOperands!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OperationMPtr.writeAttrs_footprint (ptr : OperationMPtr) (val : UInt64) h (hb : ptr.toNat + (Operation.Offsets.attrsInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.writeAttrs bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Operation.Offsets.attrsInt.toNat) val (by omega) } := by
  grind [OperationMPtr.writeAttrs, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem OperationMPtr.readAttrs!_footprint (ptr : OperationMPtr) (hb : ptr.toNat + (Operation.Offsets.attrsInt.toNat + 8) ≤ bctx.mem.size) :
    OperationMPtr.readAttrs! bctx ptr = bctx.mem.read64' (ptr.toNat + Operation.Offsets.attrsInt.toNat) := by
  grind [OperationMPtr.readAttrs!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockMPtr.writeFirstUse_footprint (ptr : BlockMPtr) (val : BlockOperandOPtr) h (hb : ptr.toNat + (Block.Offsets.firstUseInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.writeFirstUse bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Block.Offsets.firstUseInt.toNat) val (by omega) } := by
  grind [BlockMPtr.writeFirstUse, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockMPtr.readFirstUse!_footprint (ptr : BlockMPtr) :
    BlockMPtr.readFirstUse! bctx ptr = bctx.mem.read64' (ptr.toNat + Block.Offsets.firstUseInt.toNat) := by
  grind [BlockMPtr.readFirstUse!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockMPtr.writePrev_footprint (ptr : BlockMPtr) (val : BlockOPtr) h (hb : ptr.toNat + (Block.Offsets.prevInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.writePrev bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Block.Offsets.prevInt.toNat) val (by omega) } := by
  grind [BlockMPtr.writePrev, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockMPtr.readPrev!_footprint (ptr : BlockMPtr) (hb : ptr.toNat + (Block.Offsets.prevInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.readPrev! bctx ptr = bctx.mem.read64' (ptr.toNat + Block.Offsets.prevInt.toNat) := by
  grind [BlockMPtr.readPrev!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockMPtr.writeNext_footprint (ptr : BlockMPtr) (val : BlockOPtr) h (hb : ptr.toNat + (Block.Offsets.nextInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.writeNext bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Block.Offsets.nextInt.toNat) val (by omega) } := by
  grind [BlockMPtr.writeNext, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockMPtr.readNext!_footprint (ptr : BlockMPtr) (hb : ptr.toNat + (Block.Offsets.nextInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.readNext! bctx ptr = bctx.mem.read64' (ptr.toNat + Block.Offsets.nextInt.toNat) := by
  grind [BlockMPtr.readNext!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockMPtr.writeParent_footprint (ptr : BlockMPtr) (val : RegionOPtr) h (hb : ptr.toNat + (Block.Offsets.parentInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.writeParent bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Block.Offsets.parentInt.toNat) val (by omega) } := by
  grind [BlockMPtr.writeParent, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockMPtr.readParent!_footprint (ptr : BlockMPtr) (hb : ptr.toNat + (Block.Offsets.parentInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.readParent! bctx ptr = bctx.mem.read64' (ptr.toNat + Block.Offsets.parentInt.toNat) := by
  grind [BlockMPtr.readParent!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockMPtr.writeFirstOp_footprint (ptr : BlockMPtr) (val : OperationOPtr) h (hb : ptr.toNat + (Block.Offsets.firstOpInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.writeFirstOp bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Block.Offsets.firstOpInt.toNat) val (by omega) } := by
  grind [BlockMPtr.writeFirstOp, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockMPtr.readFirstOp!_footprint (ptr : BlockMPtr) (hb : ptr.toNat + (Block.Offsets.firstOpInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.readFirstOp! bctx ptr = bctx.mem.read64' (ptr.toNat + Block.Offsets.firstOpInt.toNat) := by
  grind [BlockMPtr.readFirstOp!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockMPtr.writeLastOp_footprint (ptr : BlockMPtr) (val : OperationOPtr) h (hb : ptr.toNat + (Block.Offsets.lastOpInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.writeLastOp bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Block.Offsets.lastOpInt.toNat) val (by omega) } := by
  grind [BlockMPtr.writeLastOp, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockMPtr.readLastOp!_footprint (ptr : BlockMPtr) (hb : ptr.toNat + (Block.Offsets.lastOpInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.readLastOp! bctx ptr = bctx.mem.read64' (ptr.toNat + Block.Offsets.lastOpInt.toNat) := by
  grind [BlockMPtr.readLastOp!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem BlockMPtr.writeNumArguments_footprint (ptr : BlockMPtr) (val : UInt64) h (hb : ptr.toNat + (Block.Offsets.numArgumentsInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.writeNumArguments bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Block.Offsets.numArgumentsInt.toNat) val (by omega) } := by
  grind [BlockMPtr.writeNumArguments, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockMPtr.readNumArguments!_footprint (ptr : BlockMPtr) (hb : ptr.toNat + (Block.Offsets.numArgumentsInt.toNat + 8) ≤ bctx.mem.size) :
    BlockMPtr.readNumArguments! bctx ptr = bctx.mem.read64' (ptr.toNat + Block.Offsets.numArgumentsInt.toNat) := by
  grind [BlockMPtr.readNumArguments!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem RegionMPtr.writeFirstBlock_footprint (ptr : RegionMPtr) (val : BlockOPtr) h (hb : ptr.toNat + (Region.Offsets.firstBlockInt.toNat + 8) ≤ bctx.mem.size) :
    RegionMPtr.writeFirstBlock bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Region.Offsets.firstBlockInt.toNat) val (by omega) } := by
  grind [RegionMPtr.writeFirstBlock, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem RegionMPtr.readFirstBlock!_footprint (ptr : RegionMPtr) :
    RegionMPtr.readFirstBlock! bctx ptr = bctx.mem.read64' (ptr.toNat + Region.Offsets.firstBlockInt.toNat) := by
  grind [RegionMPtr.readFirstBlock!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem RegionMPtr.writeLastBlock_footprint (ptr : RegionMPtr) (val : BlockOPtr) h (hb : ptr.toNat + (Region.Offsets.lastBlockInt.toNat + 8) ≤ bctx.mem.size) :
    RegionMPtr.writeLastBlock bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Region.Offsets.lastBlockInt.toNat) val (by omega) } := by
  grind [RegionMPtr.writeLastBlock, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem RegionMPtr.readLastBlock!_footprint (ptr : RegionMPtr) (hb : ptr.toNat + (Region.Offsets.lastBlockInt.toNat + 8) ≤ bctx.mem.size) :
    RegionMPtr.readLastBlock! bctx ptr = bctx.mem.read64' (ptr.toNat + Region.Offsets.lastBlockInt.toNat) := by
  grind [RegionMPtr.readLastBlock!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem RegionMPtr.writeParent_footprint (ptr : RegionMPtr) (val : OperationOPtr) h (hb : ptr.toNat + (Region.Offsets.parentInt.toNat + 8) ≤ bctx.mem.size) :
    RegionMPtr.writeParent bctx ptr val h = { bctx with mem := bctx.mem.blit64' (ptr.toNat + Region.Offsets.parentInt.toNat) val (by omega) } := by
  grind [RegionMPtr.writeParent, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem RegionMPtr.readParent!_footprint (ptr : RegionMPtr) (hb : ptr.toNat + (Region.Offsets.parentInt.toNat + 8) ≤ bctx.mem.size) :
    RegionMPtr.readParent! bctx ptr = bctx.mem.read64' (ptr.toNat + Region.Offsets.parentInt.toNat) := by
  grind [RegionMPtr.readParent!, ExArray.read64!_eq_read64']

@[footprint_grind =]
theorem OpOperandPtrMPtr.write_footprint (ptr : OpOperandPtrMPtr) (val : OpOperandOPtr) h
    (hb : ptr.toNat + 8 ≤ bctx.mem.size) :
    OpOperandPtrMPtr.write bctx ptr val h = { bctx with mem := bctx.mem.blit64' ptr.toNat val (by omega) } := by
  grind [OpOperandPtrMPtr.write, ExArray.blit64_eq_blit64']

@[footprint_grind =]
theorem BlockOperandPtrMPtr.write_footprint (ptr : BlockOperandPtrMPtr) (val : BlockOperandOPtr) h
    (hb : ptr.toNat + 8 ≤ bctx.mem.size) :
    BlockOperandPtrMPtr.write bctx ptr val h = { bctx with mem := bctx.mem.blit64' ptr.toNat val (by omega) } := by
  grind [BlockOperandPtrMPtr.write, ExArray.blit64_eq_blit64']

end Veir.Buffed
