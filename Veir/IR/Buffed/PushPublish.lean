module

public import Veir.IR.Buffed.PushCounts
import Veir.IR.Buffed.Frames
import Veir.IR.Buffed.RawAccessorFootprints

@[expose] public section
namespace Veir
open Buffed
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

/-! A push initializes a slot and then publishes it by writing the count word.
`Payload` is a proof about the intermediate buffer only; it is not an IRContext. -/
namespace Sim.Publication
structure Arguments (ctx : Sim.RawIRContext OpInfo) (res : Veir.BlockPtr) where
  numArguments : (res.get! ctx.spec).capArguments = (BlockMPtr.readNumArguments! ctx.buf (res.toM)).toNat
  arguments (arg : Veir.BlockArgumentPtr) (ib : arg.InBounds ctx.spec) : arg.block = res → arg.Matches ctx ib

structure BlockOperands (ctx : Sim.RawIRContext OpInfo) (op : Veir.OperationPtr) (ib : op.InBounds ctx.spec) where
  numBlockOperands : (op.get! ctx.spec).capBlockOperands = (op.toM.readNumBlockOperands! ctx.buf).toNat
  blockOperands (bo : Veir.BlockOperandPtr) (hin : bo.InBounds ctx.spec) : bo.op = op → bo.Matches ctx hin

structure Regions (ctx : Sim.RawIRContext OpInfo) (op : Veir.OperationPtr) where
  numRegions : (op.get! ctx.spec).capRegions = (op.toM.readNumRegions! ctx.buf).toNat
  regions idx (hin : idx < (op.getNumRegions! ctx.spec)) :
    Sim.RegionPtr.Sim ⟨op.toM.readNthRegion! (OpInfo := OpInfo) ctx.buf idx.toUInt64, .mk <| op.getRegion! ctx.spec idx⟩

structure Operands (ctx : Sim.RawIRContext OpInfo) (op : Veir.OperationPtr) where
  numOperands : (op.get! ctx.spec).capOperands = (op.toM.readNumOperands! ctx.buf).toNat
  operands (oper : Veir.OpOperandPtr) (hin : oper.InBounds ctx.spec) : oper.op = op → oper.Matches ctx hin

structure Results (ctx : Sim.RawIRContext OpInfo) (op : Veir.OperationPtr) (ib : op.InBounds ctx.spec) where
  numResults : (op.get! ctx.spec).capResults = (op.toM.readNumResults! ctx.buf).toNat
  results (res : Veir.OpResultPtr) (hin : res.InBounds ctx.spec) : res.op = op → res.Matches ctx hin

structure Op (ctx : Sim.RawIRContext OpInfo) (op : Veir.OperationPtr) (ib : op.InBounds ctx.spec) extends
  Veir.OperationPtr.MatchesBase ctx op ib, BlockOperands ctx op ib, Regions ctx op,
  Operands ctx op, Results ctx op ib, Veir.OperationPtr.Capacities ctx.spec op
structure Bl (ctx : Sim.RawIRContext OpInfo) (bl : Veir.BlockPtr) (ib : bl.InBounds ctx.spec) extends
  Veir.BlockPtr.MatchesBase ctx bl ib, Arguments ctx bl
structure Payload (ctx : Sim.RawIRContext OpInfo) where
  /-- All the fields are in bounds -/
  fieldsInBounds : ctx.spec.FieldsInBounds
  /-- All the values are representable. -/
  repr : ctx.spec.IsRepr
  /-- Allocated addresses do not go beyond the buffer size. -/
  in_bounds (ptr : TopLevelPtr) (ib : ptr.InBounds ctx.spec) :
    IsIncludedIN (ptr.range ctx.spec) ctx.buf.mem.range
  /-- The allocations are disjoint. -/
  disjoint_allocs (ptr₁ ptr₂ : TopLevelPtr) (ib₁ : ptr₁.InBounds ctx.spec) (ib₂ : ptr₂.InBounds ctx.spec) (hneq : ptr₁ ≠ ptr₂) :
    IsDisjointI (ptr₁.range ctx.spec) (ptr₂.range ctx.spec)
  /-- The buffer contains the encodings of all the operations. -/
  encoding_op (op : Veir.OperationPtr) (ib : op.InBounds ctx.spec) :
    Op ctx op ib
  /-- The buffer contains the encodings of all the blocks. -/
  encoding_block (blk : Veir.BlockPtr) (ib : blk.InBounds ctx.spec) :
    Bl ctx blk ib
  /-- The buffer contains the encodings of all the regions. -/
  encoding_region (rg : Veir.RegionPtr) (ib : rg.InBounds ctx.spec) :
    rg.Matches ctx ib
  /-- Attribute-table slot 0 canonically holds the empty dictionary, so the zero-initialized `attrs` field of a freshly allocated operation denotes the empty dictionary. -/
  attr_empty : ctx.buf.attributes[0]? = some (.dictionaryAttr DictionaryAttr.empty)

/-- Footprint of the final count write. All other bytes, and the attribute table, are unchanged. -/
def countField (owner : TopLevelPtr) (start : Nat) : Prop := match owner with
    | .operation op => start = op.id + 8 ∨ start = op.id + 56 ∨ start = op.id + 72 ∨ start = op.id + 88
    | .block bl => start = bl.id + 56
    | .region _ => False

structure Word (c : Sim.RawIRContext OpInfo) (b : IRBufContext) where
  owner : TopLevelPtr
  valid : owner.InBounds c.spec
  start : Nat
  field : countField owner start
  inside : (owner.range c.spec).lower ≤ start ∧ (start : Int) + 8 ≤ (owner.range c.spec).upper
  size : b.mem.size = c.buf.mem.size
  attrs : b.attributes = c.buf.attributes
  read (w : Nat) (a n : UInt64) : a.toNat + n.toNat ≤ start ∨ start + 8 ≤ a.toNat →
    b.mem.read! (w := w) a n = c.buf.mem.read! a n

variable {c : Sim.RawIRContext OpInfo} {b : IRBufContext}
private theorem Word.agree (w : Word c b) (h : Payload c) (p : TopLevelPtr) (ib : p.InBounds c.spec)
    (lo hi : Nat) (lower : (p.range c.spec).lower ≤ lo) (upper : (hi : Int) ≤ (p.range c.spec).upper)
    (same : w.owner = p → hi ≤ w.start ∨ w.start + 8 ≤ lo) : AgreesOn b c.buf lo hi := by
  refine ⟨Nat.le_of_eq w.size.symm, ?_, fun _ _ hx => w.attrs ▸ hx⟩
  intro n a len h1 h2
  apply w.read
  by_cases eq : w.owner = p
  · have := same eq; omega
  · have := h.disjoint_allocs w.owner p w.valid ib eq
    have := w.inside
    simp only [isDisjointI_def] at *; omega

private theorem opRange (h : Payload c) (op : Veir.OperationPtr) (ib : op.InBounds c.spec) :
    (TopLevelPtr.operation op).range c.spec = ((op.id : Int) + Operation.Offsets.resultsInt op c.spec ...
      (op.id : Int) + Operation.Offsets.afterInt op c.spec) := by
  rw [TopLevelPtr.range, Veir.OperationPtr.range_ideal h.repr ib]; rfl
private theorem blRange (h : Payload c) (bl : Veir.BlockPtr) (ib : bl.InBounds c.spec) :
    (TopLevelPtr.block bl).range c.spec = ((bl.id : Int) ... (bl.id : Int) + Block.Offsets.afterInt bl c.spec) := by
  rw [TopLevelPtr.range, Veir.BlockPtr.range_ideal h.repr ib]; rfl

private theorem Word.opAgree (w : Word c b) (h : Payload c) (op : Veir.OperationPtr) (ib : op.InBounds c.spec)
    (lo hi : Nat) (lower : (op.id : Int) + Operation.Offsets.resultsInt op c.spec ≤ lo)
    (upper : (hi : Int) ≤ op.id + Operation.Offsets.afterInt op c.spec)
    (safe : ∀ k : Nat, k = 8 ∨ k = 56 ∨ k = 72 ∨ k = 88 → hi ≤ op.id + k ∨ op.id + k + 8 ≤ lo) :
    AgreesOn b c.buf lo hi := by
  apply w.agree h (.operation op) (by exact ib) <;> try rw [opRange h op ib]
  · exact lower
  · exact upper
  · intro eq
    have hf := w.field; rw [eq] at hf; simp only [countField] at hf
    rcases hf with e | e | e | e <;> rw [e] <;> apply safe <;> decide

private theorem Word.blAgree (w : Word c b) (h : Payload c) (bl : Veir.BlockPtr) (ib : bl.InBounds c.spec)
    (lo hi : Nat) (lower : bl.id ≤ lo) (upper : (hi : Int) ≤ bl.id + Block.Offsets.afterInt bl c.spec)
    (safe : hi ≤ bl.id + 56 ∨ bl.id + 64 ≤ lo) : AgreesOn b c.buf lo hi := by
  apply w.agree h (.block bl) (by exact ib) <;> try rw [blRange h bl ib]
  · change (bl.id : Int) ≤ lo; omega
  · exact upper
  · intro eq; have hf := w.field; rw [eq] at hf; change w.start = bl.id + 56 at hf; omega

private theorem opBounds (h : Payload c) (op : Veir.OperationPtr) (ib : op.InBounds c.spec) :
    0 ≤ (op.id : Int) + Operation.Offsets.resultsInt op c.spec ∧
    (op.id : Int) + Operation.Offsets.afterInt op c.spec ≤ c.buf.mem.size := by
  have hin := h.in_bounds (.operation op) ib
  simp only [opRange h op ib, IsIncludedIN, ExArray.range_lower, ExArray.range_upper] at hin; exact hin
private theorem blBounds (h : Payload c) (bl : Veir.BlockPtr) (ib : bl.InBounds c.spec) :
    (bl.id : Int) + Block.Offsets.afterInt bl c.spec ≤ c.buf.mem.size := by
  have hin := h.in_bounds (.block bl) ib
  simp only [blRange h bl ib, IsIncludedIN, ExArray.range_upper] at hin; exact hin.2

private theorem step {a : UInt64} (off : Int64) (ha : a.toNat < Int64.maxValue.toInt) (hn : 0 ≤ off.toInt) :
    (a + off).toNat = a.toNat + off.toInt.toNat := by
  rw [UInt64.uint64_add_int64_toNat_lt] <;> omega

private theorem liftOpResult (h : Payload c) (w : Word c b) (res : Veir.OpResultPtr) (ib : res.InBounds c.spec)
    (hm : res.Matches c ib) : res.Matches ⟨b, c.spec'⟩ ib := by
  have parent : res.op.InBounds c.spec := by grind [Veir.OpResultPtr.inBounds_def]
  have bounds := opBounds h _ parent
  have cap := (h.repr.operations_indices _ parent).capResults
  have num := Veir.OperationPtr.getNumResults!_eq_getNumResults (ctx := c.spec) parent
  have fit := c.buf.mem.fits_in_memory
  have hs : res.toFlatNat c.spec + 40 ≤ c.buf.mem.size := by
    grind [Veir.OpResultPtr.inBounds_def, Veir.OpResultPtr.toFlatNat, Veir.OperationPtr.toFlat]
  have haddr : (res.toM c.spec).toNat = res.toFlatNat c.spec := by
    simp only [Veir.OpResultPtr.toM, Veir.OpResultPtr.toFlat_ideal h.repr _ ib, Nat.toUInt64_eq, UInt64.toNat_ofNat']; simp only [Int64.maxNatValue] at fit; omega
  have hagree : AgreesOn b c.buf (res.toFlatNat c.spec) (res.toFlatNat c.spec + 40) := by
    apply w.opAgree h _ parent <;> (try intro k hk) <;> grind [Veir.OpResultPtr.inBounds_def, Veir.OpResultPtr.toFlatNat, Veir.OperationPtr.toFlat]
  have hki := hagree.read64 (res.toM c.spec) (by grind) (by grind)
  have hty := hagree.read64 (res.toM c.spec + Buffed.ValueImpl.Offsets.type) (by grind) (by grind)
  have hfu := hagree.read64 (res.toM c.spec + Buffed.ValueImpl.Offsets.firstUse) (by grind) (by grind)
  have hix := hagree.read64 (res.toM c.spec + Buffed.OpResult.Offsets.index) (by grind) (by grind)
  have how := hagree.read64 (res.toM c.spec + Buffed.OpResult.Offsets.owner) (by grind) (by grind)
  have hat := hagree.attrs
  have ha := w.attrs
  constructor
  · have := hm.kind
    grind [Buffed.OpResultMPtr.readKind!]
  · have := hm.typee
    grind [Buffed.OpResultMPtr.readType!]
  · have := hm.firstUse
    grind [Buffed.OpResultMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.OpResultMPtr.readIndex!]
  · have := hm.owner
    grind [Buffed.OpResultMPtr.readOwner!]

private theorem liftOpOperand (h : Payload c) (w : Word c b) (oper : Veir.OpOperandPtr) (ib : oper.InBounds c.spec)
    (hm : oper.Matches c ib) : oper.Matches ⟨b, c.spec'⟩ ib := by
  have parent : oper.op.InBounds c.spec := by grind [Veir.OpOperandPtr.inBounds_def]
  have bounds := opBounds h _ parent
  have cap := (h.repr.operations_indices _ parent).capOperands
  have num := Veir.OperationPtr.getNumOperands!_eq_getNumOperands (ctx := c.spec) parent
  have fit := c.buf.mem.fits_in_memory
  have hs : oper.toFlatNat c.spec + 32 ≤ c.buf.mem.size := by
    grind [Veir.OpOperandPtr.inBounds_def, Veir.OpOperandPtr.toFlatNat, Veir.OperationPtr.toFlat]
  have haddr : (oper.toM c.spec).toNat = oper.toFlatNat c.spec := by
    simp only [Veir.OpOperandPtr.toM, Veir.OpOperandPtr.toFlat_ideal h.repr _ ib, Nat.toUInt64_eq, UInt64.toNat_ofNat']; simp only [Int64.maxNatValue] at fit; omega
  have hagree : AgreesOn b c.buf (oper.toFlatNat c.spec) (oper.toFlatNat c.spec + 32) := by
    apply w.opAgree h _ parent <;> (try intro k hk) <;> grind [Veir.OpOperandPtr.inBounds_def, Veir.OpOperandPtr.toFlatNat, Veir.OperationPtr.toFlat]
  have hnu := hagree.read64 (oper.toM c.spec + Buffed.OpOperand.Offsets.nextUse) (by grind) (by grind)
  have hba := hagree.read64 (oper.toM c.spec + Buffed.OpOperand.Offsets.back) (by grind) (by grind)
  have how := hagree.read64 (oper.toM c.spec + Buffed.OpOperand.Offsets.owner) (by grind) (by grind)
  have hva := hagree.read64 (oper.toM c.spec + Buffed.OpOperand.Offsets.value) (by grind) (by grind)
  have ha := w.attrs
  constructor
  · have := hm.nextUse
    grind [Buffed.OpOperandMPtr.readNextUse!]
  · have := hm.back
    grind [Buffed.OpOperandMPtr.readBack!]
  · have := hm.owner
    grind [Buffed.OpOperandMPtr.readOwner!]
  · have := hm.value
    grind [Buffed.OpOperandMPtr.readValue!]

private theorem liftBlockOperand (h : Payload c) (w : Word c b) (oper : Veir.BlockOperandPtr) (ib : oper.InBounds c.spec)
    (hm : oper.Matches c ib) : oper.Matches ⟨b, c.spec'⟩ ib := by
  have parent : oper.op.InBounds c.spec := by grind [Veir.BlockOperandPtr.inBounds_def]
  have bounds := opBounds h _ parent
  have cap := (h.repr.operations_indices _ parent).capBlockOperands
  have num := Veir.OperationPtr.getNumSuccessors!_eq_getNumSuccessors (ctx := c.spec) parent
  have fit := c.buf.mem.fits_in_memory
  have hs : oper.toFlatNat c.spec + 32 ≤ c.buf.mem.size := by
    grind [Veir.BlockOperandPtr.inBounds_def, Veir.BlockOperandPtr.toFlatNat, Veir.OperationPtr.toFlat]
  have haddr : (oper.toM c.spec).toNat = oper.toFlatNat c.spec := by
    simp only [Veir.BlockOperandPtr.toM, Veir.BlockOperandPtr.toFlat_ideal h.repr _ ib, Nat.toUInt64_eq, UInt64.toNat_ofNat']; simp only [Int64.maxNatValue] at fit; omega
  have hagree : AgreesOn b c.buf (oper.toFlatNat c.spec) (oper.toFlatNat c.spec + 32) := by
    apply w.opAgree h _ parent <;> (try intro k hk) <;> grind [Veir.BlockOperandPtr.inBounds_def, Veir.BlockOperandPtr.toFlatNat, Veir.OperationPtr.toFlat]
  have hnu := hagree.read64 (oper.toM c.spec + Buffed.BlockOperand.Offsets.nextUse) (by grind) (by grind)
  have hba := hagree.read64 (oper.toM c.spec + Buffed.BlockOperand.Offsets.back) (by grind) (by grind)
  have how := hagree.read64 (oper.toM c.spec + Buffed.BlockOperand.Offsets.owner) (by grind) (by grind)
  have hva := hagree.read64 (oper.toM c.spec + Buffed.BlockOperand.Offsets.value) (by grind) (by grind)
  have ha := w.attrs
  constructor
  · have := hm.nextUse
    grind [Buffed.BlockOperandMPtr.readNextUse!]
  · have := hm.back
    grind [Buffed.BlockOperandMPtr.readBack!]
  · have := hm.owner
    grind [Buffed.BlockOperandMPtr.readOwner!]
  · have := hm.value
    grind [Buffed.BlockOperandMPtr.readValue!]

private theorem liftBlockArgument (h : Payload c) (w : Word c b) (arg : Veir.BlockArgumentPtr) (ib : arg.InBounds c.spec)
    (hm : arg.Matches c ib) : arg.Matches ⟨b, c.spec'⟩ ib := by
  have parent : arg.block.InBounds c.spec := by grind [Veir.BlockArgumentPtr.inBounds_def]
  have bounds := blBounds h _ parent
  have cap := (h.repr.blocks_indices _ parent).capArguments
  have num := Veir.BlockPtr.getNumArguments!_eq_getNumArguments (ctx := c.spec) parent
  have fit := c.buf.mem.fits_in_memory
  have hs : arg.toFlatNat + 40 ≤ c.buf.mem.size := by
    grind [Veir.BlockArgumentPtr.inBounds_def, Veir.BlockArgumentPtr.toFlatNat, Veir.BlockPtr.toFlat]
  have haddr : (arg.toM).toNat = arg.toFlatNat := by
    simp only [Veir.BlockArgumentPtr.toM, Veir.BlockArgumentPtr.toFlat_ideal, Nat.toUInt64_eq, UInt64.toNat_ofNat']; simp only [Int64.maxNatValue] at fit; omega
  have hagree : AgreesOn b c.buf (arg.toFlatNat) (arg.toFlatNat + 40) := by
    apply w.blAgree h _ parent <;> grind [Veir.BlockArgumentPtr.inBounds_def, Veir.BlockArgumentPtr.toFlatNat, Veir.BlockPtr.toFlat]
  have hki := hagree.read64 arg.toM (by grind) (by grind)
  have hty := hagree.read64 (arg.toM + Buffed.ValueImpl.Offsets.type) (by grind) (by grind)
  have hfu := hagree.read64 (arg.toM + Buffed.ValueImpl.Offsets.firstUse) (by grind) (by grind)
  have hix := hagree.read64 (arg.toM + Buffed.BlockArgument.Offsets.index) (by grind) (by grind)
  have how := hagree.read64 (arg.toM + Buffed.BlockArgument.Offsets.owner) (by grind) (by grind)
  have hat := hagree.attrs
  have ha := w.attrs
  constructor
  · have := hm.kind
    grind [Buffed.BlockArgumentMPtr.readKind!]
  · have := hm.type
    grind [Buffed.BlockArgumentMPtr.readType!]
  · have := hm.firstUse
    grind [Buffed.BlockArgumentMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.BlockArgumentMPtr.readIndex!]
  · have := hm.owner
    grind [Buffed.BlockArgumentMPtr.readOwner!]

/-! ## Header structures (fixed offsets from the pointer's own address) -/

private theorem opHeader (w : Word c b) (h : Payload c) (op : Veir.OperationPtr) (ib : op.InBounds c.spec)
    (n : Nat)
    (ok : ∀ k : Nat, k = 8 ∨ k = 56 ∨ k = 72 ∨ k = 88 → n + 8 ≤ k ∨ k + 8 ≤ n) (hb : n + 8 ≤ 104) :
    AgreesOn b c.buf (op.id + n) (op.id + n + 8) := by
  apply w.opAgree h op ib <;> (try intro k hk; have := ok k hk) <;> grind

private theorem regionOffset (h : Payload c) (op : Veir.OperationPtr) (ib : op.InBounds c.spec) :
    op.toM.computeRegionsOffset! (OpInfo := OpInfo) c.buf = Operation.Offsets.regions op c.spec := by
  have enc := h.encoding_op op ib
  have ht := enc.opType
  have hn := enc.numOperands
  have hb := enc.numBlockOperands
  simp [OperationMPtr.computeRegionsOffset!, OperationMPtr.computeBlockOperandsOffset!,
    OperationMPtr.computeOperandsOffset!, Operation.Offsets.regions, Operation.Offsets.blockOperands,
    Operation.Offsets.operands, Operation.Sizes.properties, Operation.Sizes.operands, Operation.Sizes.blockOperands, ← ht, hn, hb, show OpOperand.size = BlockOperand.size from rfl, UInt64.mul_comm]

/-- Publish the initialized slot. The count proof is about the *final* bytes;
all payload reads are transported across the single, disjoint header write. -/
theorem finish (h : Payload c) (w : Word c b) (counts : Sim.CountsMatch ⟨b, c.spec'⟩) : Veir.Sim ⟨b, c.spec'⟩ := by
  have hf := c.buf.mem.fits_in_memory
  refine ⟨h.fieldsInBounds, h.repr, ?_, h.disjoint_allocs, ?_, ?_, ?_, ?_⟩
  · intro p ib; simpa only [IsIncludedIN, ExArray.range_lower, ExArray.range_upper, w.size] using h.in_bounds p ib
  · intro op ib
    have m := h.encoding_op op ib
    have base := Veir.OperationPtr.toM_toNat h.repr op ib
    have bounds := opBounds h op ib
    have addr (off : Int64) (n : Nat) (hn : off.toInt = n) : (op.toM + off).toNat = op.id + n := by
      rw [step] <;> grind
    have hPrev : op.toM.readPrev! b = op.toM.readPrev! c.buf := by
      apply (opHeader w h op ib 16 (by omega) (by decide)).read64 <;>
        rw [addr _ 16 (by decide)] <;> omega
    have hNext : op.toM.readNext! b = op.toM.readNext! c.buf := by
      apply (opHeader w h op ib 24 (by omega) (by decide)).read64 <;>
        rw [addr _ 24 (by decide)] <;> omega
    have hParent : op.toM.readParent! b = op.toM.readParent! c.buf := by
      apply (opHeader w h op ib 32 (by omega) (by decide)).read64 <;>
        rw [addr _ 32 (by decide)] <;> omega
    have hOpType : op.toM.readOpType! b = op.toM.readOpType! c.buf := by
      apply (opHeader w h op ib 40 (by omega) (by decide)).read32 <;>
        rw [addr _ 40 (by decide)] <;> omega
    have hAttrs : op.toM.readAttrs! b = op.toM.readAttrs! c.buf := by
      apply (opHeader w h op ib 96 (by omega) (by decide)).read64 <;>
        rw [addr _ 96 (by decide)] <;> omega
    have hNumBlockOperands : op.toM.readNumBlockOperands! b = op.toM.readNumBlockOperands! c.buf := by
      apply (opHeader w h op ib 48 (by omega) (by decide)).read64 <;>
        rw [addr _ 48 (by decide)] <;> omega
    have hNumOperands : op.toM.readNumOperands! b = op.toM.readNumOperands! c.buf := by
      apply (opHeader w h op ib 80 (by omega) (by decide)).read64 <;>
        rw [addr _ 80 (by decide)] <;> omega
    constructor
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hPrev] using m.prev
      · simpa only [hNext] using m.next
      · simpa only [hParent] using m.parent
      · simpa only [hOpType] using m.opType
      · simpa only [w.attrs, hAttrs] using m.attrs
      · have ag := w.opAgree h op ib (op.id + 104) (op.id + 104 + (Operation.propertySize (op.getOpType! c.spec)).toNat)
            (by grind) (by grind) (by intro k hk; omega)
        apply HasBuffedProperties.readPropertyAt_frame m.props ag.size _ ag.attrs
        intro n a len hl hu
        exact ag.read n a len (by have := addr Operation.Offsets.properties 104 rfl; grind)
          (by have := addr Operation.Offsets.properties 104 rfl; grind [Operation.propertySize_def])
    · exact ⟨(counts.blockOperands op ib).reserved, (counts.blockOperands op ib).live.symm,
        fun x hx eq => liftBlockOperand h w x hx (m.blockOperands x hx eq)⟩
    · refine ⟨(counts.regions op ib).reserved, (counts.regions op ib).live.symm, ?_⟩
      intro i hi
      have hn := (h.repr.operations_indices op ib)
      have hr := hn.capRegions
      have hcard := hn.regions
      change i < op.getNumRegions! c.spec at hi
      have hi32 : i < 4294967296 := by grind
      have hi64 : i.toUInt64.toNat = i := by simp [Nat.toUInt64_eq, Nat.mod_eq_of_lt (by omega : i < 2^64)]
      have hoff : op.toM.computeRegionsOffset! (OpInfo := OpInfo) b = op.toM.computeRegionsOffset! (OpInfo := OpInfo) c.buf := by
        simp only [OperationMPtr.computeRegionsOffset!, OperationMPtr.computeBlockOperandsOffset!, OperationMPtr.computeOperandsOffset!, hOpType, hNumOperands, hNumBlockOperands]
      let a := op.toM + (op.toM.computeRegionsOffset! (OpInfo := OpInfo) c.buf + ptrSize * i.toUInt64)
      have ha : (a.toNat : Int) = op.id + Operation.Offsets.regionsInt op c.spec + 8 * i := by
        have ho := Operation.Offsets.regions_ideal h.repr op ib
        have hmul : (ptrSize * i.toUInt64).toNat = 8 * i := by rw [UInt64.toNat_mul, hi64]; change (8 * i) % _ = _; apply Nat.mod_eq_of_lt; omega
        simp only [a, regionOffset h op ib]; rw [UInt64.uint64_add_int64_toNat_lt] <;>
          (try rw [Int64.add_toInt_lt']) <;> grind
      have ag := w.opAgree h op ib a.toNat (a.toNat + 8) (by grind) (by grind) (by intro k hk; grind)
      have old := m.regions i hi
      simp only [OperationMPtr.readNthRegion!, OperationMPtr.computeRegionOffset!, hoff] at old ⊢
      exact (ag.read64 a (by omega) (by omega)) ▸ old
    · exact ⟨(counts.operands op ib).reserved, (counts.operands op ib).live.symm,
        fun x hx eq => liftOpOperand h w x hx (m.operands x hx eq)⟩
    · exact ⟨(counts.results op ib).reserved, (counts.results op ib).live.symm,
        fun x hx eq => liftOpResult h w x hx (m.results x hx eq)⟩
  · intro bl ib
    have m := h.encoding_block bl ib
    have base := Veir.BlockPtr.toM_toNat h.repr bl ib
    have bounds := blBounds h bl ib
    have ag := w.blAgree h bl ib bl.id (bl.id + 48) (by omega) (by grind) (by omega)
    constructor
    · constructor
      · have he : bl.toM.readFirstUse! b = bl.toM.readFirstUse! c.buf := ag.read64 _ (by grind) (by grind)
        simpa only [he, Sim.OptionBlockOperandPtr.Sim_def, Sim.RawIRContext.spec] using m.firstUse
      · have he : bl.toM.readPrev! b = bl.toM.readPrev! c.buf := ag.read64 _ (by grind) (by grind)
        simpa only [he] using m.prev
      · have he : bl.toM.readNext! b = bl.toM.readNext! c.buf := ag.read64 _ (by grind) (by grind)
        simpa only [he] using m.next
      · have he : bl.toM.readParent! b = bl.toM.readParent! c.buf := ag.read64 _ (by grind) (by grind)
        simpa only [he] using m.parent
      · have he : bl.toM.readFirstOp! b = bl.toM.readFirstOp! c.buf := ag.read64 _ (by grind) (by grind)
        simpa only [he] using m.firstOp
      · have he : bl.toM.readLastOp! b = bl.toM.readLastOp! c.buf := ag.read64 _ (by grind) (by grind)
        simpa only [he] using m.lastOp
    · exact ⟨(counts.arguments bl ib).reserved, (counts.arguments bl ib).live.symm,
        fun x hx eq => liftBlockArgument h w x hx (m.arguments x hx eq)⟩
  · intro rg ib
    have base := Veir.RegionPtr.toM_toNat h.repr rg ib
    have hr : (TopLevelPtr.region rg).range c.spec = ((rg.id : Int) ... (rg.id : Int) + 24) := rfl
    have hin := h.in_bounds (.region rg) ib
    simp only [hr, IsIncludedIN, ExArray.range_upper] at hin
    have ag := w.agree h (.region rg) ib rg.id (rg.id + 24) (by rw [hr]; exact Int.le_refl _) (by rw [hr]; simp)
      (by intro eq; have hf := w.field; rw [eq] at hf; contradiction)
    have m := h.encoding_region rg ib
    constructor
    · have he : rg.toM.readFirstBlock! b = rg.toM.readFirstBlock! c.buf := ag.read64 _ (by grind) (by grind)
      simpa only [he] using m.firstBlock
    · have he : rg.toM.readLastBlock! b = rg.toM.readLastBlock! c.buf := ag.read64 _ (by grind) (by grind)
      simpa only [he] using m.lastBlock
    · have he : rg.toM.readParent! b = rg.toM.readParent! c.buf := ag.read64 _ (by grind) (by grind)
      simpa only [he] using m.parent
  · simpa only [w.attrs] using h.attr_empty

theorem opWordBound (h : Payload c) (op : Veir.OperationPtr) (ib : op.InBounds c.spec) (off : Int64)
    (k : Nat) (hk : off.toInt = k) (bound : k + 8 ≤ 104) :
    IsIncluded ((op.toM + off).toNat ... (op.toM + off).toNat + 8) c.buf.mem.range := by
  have := opBounds h op ib
  have := Veir.OperationPtr.toM_toNat h.repr op ib
  have := c.buf.mem.fits_in_memory
  simp only [IsIncluded, ExArray.range_lower, ExArray.range_upper]; rw [step] <;> grind

theorem blWordBound (h : Payload c) (bl : Veir.BlockPtr) (ib : bl.InBounds c.spec) (off : Int64)
    (k : Nat) (hk : off.toInt = k) (bound : k + 8 ≤ 64) :
    IsIncluded ((bl.toM + off).toNat ... (bl.toM + off).toNat + 8) c.buf.mem.range := by
  have := blBounds h bl ib
  have := Veir.BlockPtr.toM_toNat h.repr bl ib
  have := c.buf.mem.fits_in_memory
  simp only [IsIncluded, ExArray.range_lower, ExArray.range_upper]; rw [step] <;> grind

theorem finishOp (h : Payload c) (op : Veir.OperationPtr) (ib : op.InBounds c.spec)
    (off : Int64) (k : Nat) (hk : off.toInt = k) (field : (k = 8 ∨ k = 56 ∨ k = 72 ∨ k = 88))
    (val : UInt64) (eq : b = { c.buf with mem := c.buf.mem.blit64 (op.toM + off) val (opWordBound h _ ib off k hk (by omega)) })
    (counts : Sim.CountsMatch ⟨b, c.spec'⟩) : Veir.Sim ⟨b, c.spec'⟩ := by
  subst b
  have base := Veir.OperationPtr.toM_toNat h.repr op ib
  have bounds := opBounds h op ib
  have hf := c.buf.mem.fits_in_memory
  have addr : (op.toM + off).toNat = op.id + k := by rw [step] <;> grind
  apply finish h _ counts
  refine ⟨.operation op, ib, op.id + k, ?_, ?_, by simp, rfl, ?_⟩
  · simp only [countField]; omega
  · rw [opRange h op ib]; grind
  · intro w a n hd; exact ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega)

theorem finishBlock (h : Payload c) (bl : Veir.BlockPtr) (ib : bl.InBounds c.spec)
    (off : Int64) (k : Nat) (hk : off.toInt = k) (field : (k = 56))
    (val : UInt64) (eq : b = { c.buf with mem := c.buf.mem.blit64 (bl.toM + off) val (blWordBound h _ ib off k hk (by omega)) })
    (counts : Sim.CountsMatch ⟨b, c.spec'⟩) : Veir.Sim ⟨b, c.spec'⟩ := by
  subst b
  have base := Veir.BlockPtr.toM_toNat h.repr bl ib
  have bounds := blBounds h bl ib
  have hf := c.buf.mem.fits_in_memory
  have addr : (bl.toM + off).toNat = bl.id + k := by rw [step] <;> grind
  apply finish h _ counts
  refine ⟨.block bl, ib, bl.id + k, ?_, ?_, by simp, rfl, ?_⟩
  · simp only [countField]; omega
  · rw [blRange h bl ib]; grind
  · intro w a n hd; exact ExArray.read!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega)

end Sim.Publication
end Veir
