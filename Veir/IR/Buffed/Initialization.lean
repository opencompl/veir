module

public import Veir.IR.Buffed.RawAccessorsLemmas
public import Veir.IR.Buffed.RawReadWriteLemmas
public import Veir.IR.Buffed.Reservation

@[expose] public section
namespace Veir.Buffed

set_option maxHeartbeats 1000000

set_option hygiene false in
macro "header_bounds" : tactic => `(tactic|
  (have hf := b.mem.fits_in_memory
   simp only [IRBufContext.size_def] at *
   grind (instances := 4000) [UInt64.uint64_add_int64_toInt_lt, OperationMPtr.writeNumOperands_size, OperationMPtr.writeNumResults_size, OperationMPtr.writeNumBlockOperands_size, OperationMPtr.writeNumRegions_size, OperationMPtr.writeParent_size, OperationMPtr.writeNext_size, OperationMPtr.writePrev_size, OperationMPtr.writeOpType_size, OperationMPtr.writeAttrs_size]))

/-- Initialize every scalar header field, including the attribute index, in a
reserved range. The same initializer works for fresh and recycled storage. -/
@[inline]
def OperationMPtr.initialize (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (ty : UInt32) (hb : ptr.toNat + 72 ≤ b.mem.size) : IRBufContext :=
  let b := ptr.writeNumOperands b no (by header_bounds)
  let b := ptr.writeNumResults b nr (by header_bounds)
  let b := ptr.writeNumBlockOperands b nb (by header_bounds)
  let b := ptr.writeNumRegions b ng (by header_bounds)
  let b := ptr.writeParent b BlockOPtr.none (by header_bounds)
  let b := ptr.writeNext b OperationOPtr.none (by header_bounds)
  let b := ptr.writePrev b OperationOPtr.none (by header_bounds)
  let b := ptr.writeOpType b ty (by header_bounds)
  let b := ptr.writeAttrs b 0 (by header_bounds)
  b

@[simp]
theorem OperationMPtr.initialize_size (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (ty : UInt32) (hb) :
    (ptr.initialize b nr no nb ng ty hb).size = b.size := by
  simp [OperationMPtr.initialize, OperationMPtr.writeNumOperands, OperationMPtr.writeNumResults, OperationMPtr.writeNumBlockOperands, OperationMPtr.writeNumRegions, OperationMPtr.writeParent, OperationMPtr.writeNext, OperationMPtr.writePrev, OperationMPtr.writeOpType, OperationMPtr.writeAttrs, IRBufContext.size_def]

@[simp]
theorem OperationMPtr.initialize_attributes (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (ty : UInt32) (hb) :
    (ptr.initialize b nr no nb ng ty hb).attributes = b.attributes := by
  simp [OperationMPtr.initialize, OperationMPtr.writeNumOperands, OperationMPtr.writeNumResults, OperationMPtr.writeNumBlockOperands, OperationMPtr.writeNumRegions, OperationMPtr.writeParent, OperationMPtr.writeNext, OperationMPtr.writePrev, OperationMPtr.writeOpType, OperationMPtr.writeAttrs]

@[simp]
theorem OperationMPtr.initialize_freeList (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (ty : UInt32) (hb) :
    (ptr.initialize b nr no nb ng ty hb).freeList = b.freeList := by
  simp [OperationMPtr.initialize, OperationMPtr.writeNumOperands, OperationMPtr.writeNumResults, OperationMPtr.writeNumBlockOperands, OperationMPtr.writeNumRegions, OperationMPtr.writeParent, OperationMPtr.writeNext, OperationMPtr.writePrev, OperationMPtr.writeOpType, OperationMPtr.writeAttrs]

theorem OperationMPtr.initialize_reads (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (ty : UInt32) (hb) :
    OperationMPtr.readNumOperands! (ptr.initialize b nr no nb ng ty hb) ptr = no ∧
    OperationMPtr.readNumResults! (ptr.initialize b nr no nb ng ty hb) ptr = nr ∧
    OperationMPtr.readNumBlockOperands! (ptr.initialize b nr no nb ng ty hb) ptr = nb ∧
    OperationMPtr.readNumRegions! (ptr.initialize b nr no nb ng ty hb) ptr = ng ∧
    OperationMPtr.readParent! (ptr.initialize b nr no nb ng ty hb) ptr = BlockOPtr.none ∧
    OperationMPtr.readNext! (ptr.initialize b nr no nb ng ty hb) ptr = OperationOPtr.none ∧
    OperationMPtr.readPrev! (ptr.initialize b nr no nb ng ty hb) ptr = OperationOPtr.none ∧
    OperationMPtr.readOpType! (ptr.initialize b nr no nb ng ty hb) ptr = ty ∧
    OperationMPtr.readAttrs! (ptr.initialize b nr no nb ng ty hb) ptr = 0 := by
  have hf := b.mem.fits_in_memory
  have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 64 →
      (ptr + k).toNat = ptr.toNat + kn := by
    intro k kn hkn hk
    rw [UInt64.toNat_add, hkn]
    apply Nat.mod_eq_of_lt
    simp only [IRBufContext.size_def, Int64.maxNatValue] at *
    omega
  have h8 := hstep 8 8 rfl (by omega)
  have h16 := hstep 16 16 rfl (by omega)
  have h24 := hstep 24 24 rfl (by omega)
  have h32 := hstep 32 32 rfl (by omega)
  have h40 := hstep 40 40 rfl (by omega)
  have h48 := hstep 48 48 rfl (by omega)
  have h56 := hstep 56 56 rfl (by omega)
  have h64 := hstep 64 64 rfl (by omega)
  clear hstep
  simp only [OperationMPtr.initialize, OperationMPtr.writeNumOperands, OperationMPtr.writeNumResults, OperationMPtr.writeNumBlockOperands, OperationMPtr.writeNumRegions, OperationMPtr.writeParent, OperationMPtr.writeNext, OperationMPtr.writePrev, OperationMPtr.writeOpType, OperationMPtr.writeAttrs, OperationMPtr.readNumOperands!, OperationMPtr.readNumResults!, OperationMPtr.readNumBlockOperands!, OperationMPtr.readNumRegions!, OperationMPtr.readParent!, OperationMPtr.readNext!, OperationMPtr.readPrev!, OperationMPtr.readOpType!, OperationMPtr.readAttrs!]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded]

theorem OperationMPtr.initialize_read_disjoint (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (ty : UInt32) (hb) (w : Nat) (n len : UInt64)
    (hd : n.toNat + len.toNat ≤ ptr.toNat ∨ ptr.toNat + 72 ≤ n.toNat) :
    (ptr.initialize b nr no nb ng ty hb).mem.read! (w := w) n len = b.mem.read! n len := by
  have hf := b.mem.fits_in_memory
  have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 64 →
      (ptr + k).toNat = ptr.toNat + kn := by
    intro k kn hkn hk
    rw [UInt64.toNat_add, hkn]
    apply Nat.mod_eq_of_lt
    simp only [IRBufContext.size_def, Int64.maxNatValue] at *
    omega
  have h8 := hstep 8 8 rfl (by omega)
  have h16 := hstep 16 16 rfl (by omega)
  have h24 := hstep 24 24 rfl (by omega)
  have h32 := hstep 32 32 rfl (by omega)
  have h40 := hstep 40 40 rfl (by omega)
  have h48 := hstep 48 48 rfl (by omega)
  have h56 := hstep 56 56 rfl (by omega)
  have h64 := hstep 64 64 rfl (by omega)
  clear hstep
  simp only [OperationMPtr.initialize, OperationMPtr.writeNumOperands, OperationMPtr.writeNumResults, OperationMPtr.writeNumBlockOperands, OperationMPtr.writeNumRegions, OperationMPtr.writeParent, OperationMPtr.writeNext, OperationMPtr.writePrev, OperationMPtr.writeOpType, OperationMPtr.writeAttrs]
  grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded]


variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

theorem OperationMPtr.properties_address (b : IRBufContext) (ptr : OperationMPtr)
    (hb : ptr.toNat + 72 ≤ b.mem.size) :
    (ptr + Operation.Offsets.properties).toNat = ptr.toNat + 72 := by
  have hf := b.mem.fits_in_memory
  rw [UInt64.uint64_add_int64_toNat_lt] <;> grind

@[inline]
def OperationMPtr.initializeOp (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (op : OpInfo) (props : HasOpInfo.propertiesOf op)
    (hb : ptr.toNat + 72 + (Operation.propertySize op).toNat ≤ b.mem.size)
    (ha : b.attributes.size < 2^63) : IRBufContext :=
  let b' := ptr.initialize b nr no nb ng (SerializableOpInfo.encode op) (by omega)
  HasBuffedProperties.writePropertyAt op props (ptr + Operation.Offsets.properties) b'
    (by
      have ho := ptr.properties_address b (by omega)
      have hs := ptr.initialize_size b nr no nb ng (SerializableOpInfo.encode op) (by omega)
      change _ ≤ b'.size
      change b'.size = b.size at hs
      rw [hs]
      exact ho ▸ hb)
    (by simpa [b'] using ha)

@[simp]
theorem OperationMPtr.initializeOp_size (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (op : OpInfo) (props : HasOpInfo.propertiesOf op) (hb ha) :
    (ptr.initializeOp b nr no nb ng op props hb ha).mem.size = b.mem.size := by
  simp only [initializeOp, HasBuffedProperties.preserves_size]
  exact ptr.initialize_size b nr no nb ng (SerializableOpInfo.encode op) _

@[simp]
theorem OperationMPtr.initializeOp_freeList (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (op : OpInfo) (props : HasOpInfo.propertiesOf op) (hb ha) :
    (ptr.initializeOp b nr no nb ng op props hb ha).freeList = b.freeList := by
  simp [initializeOp, HasBuffedProperties.preserves_freeList]

theorem OperationMPtr.initializeOp_attributes (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (op : OpInfo) (props : HasOpInfo.propertiesOf op) (hb ha)
    {i : Nat} {a : Attribute} (h : b.attributes[i]? = some a) :
    (ptr.initializeOp b nr no nb ng op props hb ha).attributes[i]? = some a := by
  apply HasBuffedProperties.only_adds_attributes
  simpa using h

theorem OperationMPtr.initializeOp_property (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (op : OpInfo) (props : HasOpInfo.propertiesOf op) (hb ha) :
    HasBuffedProperties.readPropertyAt op (ptr + Operation.Offsets.properties)
      (ptr.initializeOp b nr no nb ng op props hb ha) = some props := by
  exact HasBuffedProperties.read_after_write

theorem OperationMPtr.initializeOp_read_disjoint (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (op : OpInfo) (props : HasOpInfo.propertiesOf op) (hb ha)
    (w : Nat) (n len : UInt64)
    (hd : n.toNat + len.toNat ≤ ptr.toNat ∨
      ptr.toNat + 72 + (Operation.propertySize op).toNat ≤ n.toNat) :
    (ptr.initializeOp b nr no nb ng op props hb ha).mem.read! (w := w) n len = b.mem.read! n len := by
  have ho := ptr.properties_address b (by omega)
  simp only [Operation.propertySize] at hd
  unfold initializeOp
  rw [HasBuffedProperties.only_modifies_properties (by simp only [IsDisjoint]; omega)]
  exact ptr.initialize_read_disjoint b nr no nb ng _ _ w n len (by omega)

theorem OperationMPtr.initializeOp_reads (b : IRBufContext) (ptr : OperationMPtr)
    (nr no nb ng : UInt64) (op : OpInfo) (props : HasOpInfo.propertiesOf op) (hb ha) :
    OperationMPtr.readNumOperands! (ptr.initializeOp b nr no nb ng op props hb ha) ptr = no ∧
    OperationMPtr.readNumResults! (ptr.initializeOp b nr no nb ng op props hb ha) ptr = nr ∧
    OperationMPtr.readNumBlockOperands! (ptr.initializeOp b nr no nb ng op props hb ha) ptr = nb ∧
    OperationMPtr.readNumRegions! (ptr.initializeOp b nr no nb ng op props hb ha) ptr = ng ∧
    OperationMPtr.readParent! (ptr.initializeOp b nr no nb ng op props hb ha) ptr = BlockOPtr.none ∧
    OperationMPtr.readNext! (ptr.initializeOp b nr no nb ng op props hb ha) ptr = OperationOPtr.none ∧
    OperationMPtr.readPrev! (ptr.initializeOp b nr no nb ng op props hb ha) ptr = OperationOPtr.none ∧
    OperationMPtr.readOpType! (ptr.initializeOp b nr no nb ng op props hb ha) ptr = SerializableOpInfo.encode op ∧
    OperationMPtr.readAttrs! (ptr.initializeOp b nr no nb ng op props hb ha) ptr = 0 := by
  have ho := ptr.properties_address b (by omega)
  have hreads := ptr.initialize_reads b nr no nb ng (SerializableOpInfo.encode op) (by omega)
  have hf := b.mem.fits_in_memory
  have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 64 →
      (ptr + k).toNat = ptr.toNat + kn := by
    intro k kn hkn hk
    rw [UInt64.toNat_add, hkn]
    apply Nat.mod_eq_of_lt
    simp only [IRBufContext.size_def, Int64.maxNatValue] at *
    omega
  have h8 := hstep 8 8 rfl (by omega)
  have h16 := hstep 16 16 rfl (by omega)
  have h24 := hstep 24 24 rfl (by omega)
  have h32 := hstep 32 32 rfl (by omega)
  have h40 := hstep 40 40 rfl (by omega)
  have h48 := hstep 48 48 rfl (by omega)
  have h56 := hstep 56 56 rfl (by omega)
  have h64 := hstep 64 64 rfl (by omega)
  clear hstep
  simp only [OperationMPtr.readNumOperands!, OperationMPtr.readNumResults!, OperationMPtr.readNumBlockOperands!, OperationMPtr.readNumRegions!, OperationMPtr.readParent!, OperationMPtr.readNext!, OperationMPtr.readPrev!, OperationMPtr.readOpType!, OperationMPtr.readAttrs!,
    ExArray.read64!_eq_read!, ExArray.read32!_eq_read!] at hreads ⊢
  unfold initializeOp
  simpa (disch := (simp only [IsDisjoint]; grind)) only
    [HasBuffedProperties.only_modifies_properties] using hreads

end Veir.Buffed
