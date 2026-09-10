module

public import Veir.IR.Buffed.Initialization

@[expose] public section
namespace Veir.Buffed
set_option maxHeartbeats 1000000

set_option hygiene false in
macro "block_init_bounds" : tactic => `(tactic|
  (have hf := b.mem.fits_in_memory
   simp only [IRBufContext.size_def] at *
   grind (instances := 4000) [UInt64.uint64_add_int64_toInt_lt, BlockMPtr.writeNumArguments_size, BlockMPtr.writeFirstUse_size, BlockMPtr.writePrev_size, BlockMPtr.writeNext_size, BlockMPtr.writeParent_size, BlockMPtr.writeFirstOp_size, BlockMPtr.writeLastOp_size]))

@[inline]
def BlockMPtr.initialize (b : IRBufContext) (ptr : BlockMPtr) (na : UInt64)
    (hb : ptr.toNat + 56 ≤ b.mem.size) : IRBufContext :=
  let b := ptr.writeNumArguments b na (by block_init_bounds)
  let b := ptr.writeFirstUse b BlockOperandOPtr.none (by block_init_bounds)
  let b := ptr.writePrev b BlockOPtr.none (by block_init_bounds)
  let b := ptr.writeNext b BlockOPtr.none (by block_init_bounds)
  let b := ptr.writeParent b RegionOPtr.none (by block_init_bounds)
  let b := ptr.writeFirstOp b OperationOPtr.none (by block_init_bounds)
  let b := ptr.writeLastOp b OperationOPtr.none (by block_init_bounds)
  b

@[simp]
theorem BlockMPtr.initialize_size (b : IRBufContext) (ptr : BlockMPtr) (na : UInt64) (hb) :
    (ptr.initialize b na hb).size = b.size := by
  simp [BlockMPtr.initialize, BlockMPtr.writeNumArguments, BlockMPtr.writeFirstUse, BlockMPtr.writePrev, BlockMPtr.writeNext, BlockMPtr.writeParent, BlockMPtr.writeFirstOp, BlockMPtr.writeLastOp, IRBufContext.size_def]

@[simp]
theorem BlockMPtr.initialize_attributes (b : IRBufContext) (ptr : BlockMPtr) (na : UInt64) (hb) :
    (ptr.initialize b na hb).attributes = b.attributes := by
  simp [BlockMPtr.initialize, BlockMPtr.writeNumArguments, BlockMPtr.writeFirstUse, BlockMPtr.writePrev, BlockMPtr.writeNext, BlockMPtr.writeParent, BlockMPtr.writeFirstOp, BlockMPtr.writeLastOp, IRBufContext.size_def]

@[simp]
theorem BlockMPtr.initialize_freeList (b : IRBufContext) (ptr : BlockMPtr) (na : UInt64) (hb) :
    (ptr.initialize b na hb).freeList = b.freeList := by
  simp [BlockMPtr.initialize, BlockMPtr.writeNumArguments, BlockMPtr.writeFirstUse, BlockMPtr.writePrev, BlockMPtr.writeNext, BlockMPtr.writeParent, BlockMPtr.writeFirstOp, BlockMPtr.writeLastOp, IRBufContext.size_def]

theorem BlockMPtr.initialize_reads (b : IRBufContext) (ptr : BlockMPtr) (na : UInt64) (hb) :
    BlockMPtr.readNumArguments! (ptr.initialize b na hb) ptr = na ∧
    BlockMPtr.readFirstUse! (ptr.initialize b na hb) ptr = BlockOperandOPtr.none ∧
    BlockMPtr.readPrev! (ptr.initialize b na hb) ptr = BlockOPtr.none ∧
    BlockMPtr.readNext! (ptr.initialize b na hb) ptr = BlockOPtr.none ∧
    BlockMPtr.readParent! (ptr.initialize b na hb) ptr = RegionOPtr.none ∧
    BlockMPtr.readFirstOp! (ptr.initialize b na hb) ptr = OperationOPtr.none ∧
    BlockMPtr.readLastOp! (ptr.initialize b na hb) ptr = OperationOPtr.none := by
  have hf := b.mem.fits_in_memory
  have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 48 →
      (ptr + k).toNat = ptr.toNat + kn := by
    intro k kn hkn hk
    rw [UInt64.toNat_add, hkn]
    apply Nat.mod_eq_of_lt
    simp only [Int64.maxNatValue] at *
    omega
  have h8 := hstep 8 8 rfl (by omega)
  have h16 := hstep 16 16 rfl (by omega)
  have h24 := hstep 24 24 rfl (by omega)
  have h32 := hstep 32 32 rfl (by omega)
  have h40 := hstep 40 40 rfl (by omega)
  have h48 := hstep 48 48 rfl (by omega)
  clear hstep
  simp only [BlockMPtr.initialize, BlockMPtr.writeNumArguments, BlockMPtr.writeFirstUse, BlockMPtr.writePrev, BlockMPtr.writeNext, BlockMPtr.writeParent, BlockMPtr.writeFirstOp, BlockMPtr.writeLastOp, BlockMPtr.readNumArguments!, BlockMPtr.readFirstUse!, BlockMPtr.readPrev!, BlockMPtr.readNext!, BlockMPtr.readParent!, BlockMPtr.readFirstOp!, BlockMPtr.readLastOp!]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded]

theorem BlockMPtr.initialize_read_disjoint (b : IRBufContext) (ptr : BlockMPtr) (na : UInt64)
    (hb) (w : Nat) (n len : UInt64)
    (hd : n.toNat + len.toNat ≤ ptr.toNat ∨ ptr.toNat + 56 ≤ n.toNat) :
    (ptr.initialize b na hb).mem.read! (w := w) n len = b.mem.read! n len := by
  have hf := b.mem.fits_in_memory
  have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 48 →
      (ptr + k).toNat = ptr.toNat + kn := by
    intro k kn hkn hk
    rw [UInt64.toNat_add, hkn]
    apply Nat.mod_eq_of_lt
    simp only [Int64.maxNatValue] at *
    omega
  have h8 := hstep 8 8 rfl (by omega)
  have h16 := hstep 16 16 rfl (by omega)
  have h24 := hstep 24 24 rfl (by omega)
  have h32 := hstep 32 32 rfl (by omega)
  have h40 := hstep 40 40 rfl (by omega)
  have h48 := hstep 48 48 rfl (by omega)
  clear hstep
  simp only [BlockMPtr.initialize, BlockMPtr.writeNumArguments, BlockMPtr.writeFirstUse, BlockMPtr.writePrev, BlockMPtr.writeNext, BlockMPtr.writeParent, BlockMPtr.writeFirstOp, BlockMPtr.writeLastOp]
  grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded]

set_option hygiene false in
macro "region_init_bounds" : tactic => `(tactic|
  (have hf := b.mem.fits_in_memory
   simp only [IRBufContext.size_def] at *
   grind (instances := 4000) [UInt64.uint64_add_int64_toInt_lt, RegionMPtr.writeParent_size, RegionMPtr.writeFirstBlock_size, RegionMPtr.writeLastBlock_size]))

@[inline]
def RegionMPtr.initialize (b : IRBufContext) (ptr : RegionMPtr) 
    (hb : ptr.toNat + 24 ≤ b.mem.size) : IRBufContext :=
  let b := ptr.writeParent b OperationOPtr.none (by region_init_bounds)
  let b := ptr.writeFirstBlock b BlockOPtr.none (by region_init_bounds)
  let b := ptr.writeLastBlock b BlockOPtr.none (by region_init_bounds)
  b

@[simp]
theorem RegionMPtr.initialize_size (b : IRBufContext) (ptr : RegionMPtr)  (hb) :
    (ptr.initialize b  hb).size = b.size := by
  simp [RegionMPtr.initialize, RegionMPtr.writeParent, RegionMPtr.writeFirstBlock, RegionMPtr.writeLastBlock, IRBufContext.size_def]

@[simp]
theorem RegionMPtr.initialize_attributes (b : IRBufContext) (ptr : RegionMPtr)  (hb) :
    (ptr.initialize b  hb).attributes = b.attributes := by
  simp [RegionMPtr.initialize, RegionMPtr.writeParent, RegionMPtr.writeFirstBlock, RegionMPtr.writeLastBlock, IRBufContext.size_def]

@[simp]
theorem RegionMPtr.initialize_freeList (b : IRBufContext) (ptr : RegionMPtr)  (hb) :
    (ptr.initialize b  hb).freeList = b.freeList := by
  simp [RegionMPtr.initialize, RegionMPtr.writeParent, RegionMPtr.writeFirstBlock, RegionMPtr.writeLastBlock, IRBufContext.size_def]

theorem RegionMPtr.initialize_reads (b : IRBufContext) (ptr : RegionMPtr)  (hb) :
    RegionMPtr.readParent! (ptr.initialize b  hb) ptr = OperationOPtr.none ∧
    RegionMPtr.readFirstBlock! (ptr.initialize b  hb) ptr = BlockOPtr.none ∧
    RegionMPtr.readLastBlock! (ptr.initialize b  hb) ptr = BlockOPtr.none := by
  have hf := b.mem.fits_in_memory
  have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 16 →
      (ptr + k).toNat = ptr.toNat + kn := by
    intro k kn hkn hk
    rw [UInt64.toNat_add, hkn]
    apply Nat.mod_eq_of_lt
    simp only [Int64.maxNatValue] at *
    omega
  have h8 := hstep 8 8 rfl (by omega)
  have h16 := hstep 16 16 rfl (by omega)
  clear hstep
  simp only [RegionMPtr.initialize, RegionMPtr.writeParent, RegionMPtr.writeFirstBlock, RegionMPtr.writeLastBlock, RegionMPtr.readParent!, RegionMPtr.readFirstBlock!, RegionMPtr.readLastBlock!]
  refine ⟨?_, ?_, ?_⟩ <;>
    grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded]

theorem RegionMPtr.initialize_read_disjoint (b : IRBufContext) (ptr : RegionMPtr) 
    (hb) (w : Nat) (n len : UInt64)
    (hd : n.toNat + len.toNat ≤ ptr.toNat ∨ ptr.toNat + 24 ≤ n.toNat) :
    (ptr.initialize b  hb).mem.read! (w := w) n len = b.mem.read! n len := by
  have hf := b.mem.fits_in_memory
  have hstep : ∀ (k : UInt64) (kn : Nat), k.toNat = kn → kn ≤ 16 →
      (ptr + k).toNat = ptr.toNat + kn := by
    intro k kn hkn hk
    rw [UInt64.toNat_add, hkn]
    apply Nat.mod_eq_of_lt
    simp only [Int64.maxNatValue] at *
    omega
  have h8 := hstep 8 8 rfl (by omega)
  have h16 := hstep 16 16 rfl (by omega)
  clear hstep
  simp only [RegionMPtr.initialize, RegionMPtr.writeParent, RegionMPtr.writeFirstBlock, RegionMPtr.writeLastBlock]
  grind (gen := 20) (splits := 30) [IsDisjoint, IsIncluded]

end Veir.Buffed
