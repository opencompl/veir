module

import all Veir.Rewriter.Basic
import all Veir.IR.Mutators
import all Veir.IR.Basic
import all Veir.Rewriter.LinkedList.Basic
import all Veir.Rewriter.InsertPoint

public import Veir.GlobalOpInfo
public import Veir.Rewriter.WfRewriter

/-! Allocation bounds preserved by the rewriter steps used in LLVM lowering. -/

public section

namespace Veir.LLVMLowering

variable {ctx ctx' : IRContext OpCode}

/-- Allocated identifiers lie below the next identifier offered by the allocator. -/
structure AllocationSafe (ctx : IRContext OpCode) : Prop where
  operations : ∀ p : OperationPtr, p.InBounds ctx → p.id < ctx.nextID
  blocks : ∀ p : BlockPtr, p.InBounds ctx → p.id < ctx.nextID
  regions : ∀ p : RegionPtr, p.InBounds ctx → p.id < ctx.nextID

end Veir.LLVMLowering

namespace Veir.LLVMLowering

variable {ctx ctx' : IRContext OpCode}

section
attribute [local simp] OperationPtr.set BlockPtr.set RegionPtr.set
  OperationPtr.setOperands OperationPtr.setBlockOperands OperationPtr.setResults
  OperationPtr.pushResult OperationPtr.setRegions OperationPtr.pushRegion
  OperationPtr.setNextOp OperationPtr.setPrevOp OperationPtr.setParent
  BlockPtr.setFirstUse BlockPtr.setFirstOp BlockPtr.setLastOp BlockPtr.setNextBlock
  BlockPtr.setPrevBlock BlockPtr.setParent BlockPtr.setArguments BlockPtr.pushArgument
  RegionPtr.setParent RegionPtr.setFirstBlock RegionPtr.setLastBlock
  OpOperandPtr.setBack OpOperandPtr.setNextUse OpOperandPtr.set
  OpResultPtr.setFirstUse OpResultPtr.set BlockArgumentPtr.setFirstUse BlockArgumentPtr.set

theorem value_setFirstUse_nextID : (ValuePtr.setFirstUse value ctx use hv).nextID = ctx.nextID := by
  cases value <;> simp [ValuePtr.setFirstUse]

attribute [local simp] value_setFirstUse_nextID

theorem pushResult_nextID : (Rewriter.pushResult ctx op ty ho).nextID = ctx.nextID := by
  simp [Rewriter.pushResult]

theorem pushOperand_nextID : (Rewriter.pushOperand ctx op value ho hv hx).nextID = ctx.nextID := by
  simp only [Rewriter.pushOperand, OpOperandPtr.insertIntoCurrent]
  split <;> simp [OperationPtr.pushOperand]

theorem initOpResults_nextID : (Rewriter.initOpResults ctx op ts i ho hi).nextID = ctx.nextID := by
  fun_induction Rewriter.initOpResults <;> simp_all +zetaDelta [pushResult_nextID]

theorem initOpOperands_nextID : (Rewriter.initOpOperands ctx op ho vs hx hv n hn).nextID = ctx.nextID := by
  fun_induction Rewriter.initOpOperands <;> simp_all +zetaDelta [pushOperand_nextID]

theorem pushRegion_nextID : (Rewriter.pushRegion ctx op region ho hr hp).nextID = ctx.nextID := by
  simp [Rewriter.pushRegion]

theorem initOpRegions_nextID (h : Rewriter.initOpRegions ctx op rs i ho hr hx hi = some ctx') :
    ctx'.nextID = ctx.nextID := by
  fun_induction Rewriter.initOpRegions <;> simp_all +zetaDelta [pushRegion_nextID]

theorem initBlockArguments_nextID : (Rewriter.initBlockArguments ctx block ts i hb hi).nextID = ctx.nextID := by
  fun_induction Rewriter.initBlockArguments <;> simp_all +zetaDelta [Rewriter.pushBlockArgument]

@[grind →]
theorem opSetParent_nextID (h : OperationPtr.setParentWithCheck op ctx parent ho = some ctx') :
    ctx'.nextID = ctx.nextID := by
  unfold OperationPtr.setParentWithCheck at h; split at h <;> simp_all
  cases h; rfl

@[grind →]
theorem blockSetParent_nextID (h : BlockPtr.setParentWithCheck block ctx parent hb = some ctx') :
    ctx'.nextID = ctx.nextID := by
  unfold BlockPtr.setParentWithCheck at h; split at h <;> simp_all
  cases h; rfl

@[grind =]
theorem blockLink_nextID : (BlockPtr.linkBetween block ctx prev next hb hp hn).nextID = ctx.nextID := by
  cases prev <;> cases next <;> simp [BlockPtr.linkBetween]

theorem insertOp_nextID (h : Rewriter.insertOp ctx op ip ho hi hx = some ctx') :
    ctx'.nextID = ctx.nextID := by
  cases hp : ip.prev ctx hi <;> cases hn : ip.next <;>
    simp [Rewriter.insertOp, OperationPtr.linkBetweenWithParent, OperationPtr.linkBetween,
      hp, hn] at h
  all_goals split at h <;> try contradiction
  all_goals split at h <;> simp_all
  all_goals grind

theorem insertBlock_nextID (h : Rewriter.insertBlock ctx block ip hb hi hx = some ctx') :
    ctx'.nextID = ctx.nextID := by
  cases hp : ip.prev ctx hi <;> cases hn : ip.next <;>
    simp [Rewriter.insertBlock, BlockPtr.linkBetweenWithParent, hp, hn] at h
  all_goals split at h <;> try contradiction
  all_goals split at h <;> simp_all
  all_goals grind

end

theorem AllocationSafe.pushOperand (h : AllocationSafe ctx) :
    AllocationSafe (Rewriter.pushOperand ctx op value ho hv hx) := by
  rcases h with ⟨hops, hbs, hrs⟩
  constructor <;> intro p hp <;> have hn := pushOperand_nextID (ctx := ctx) (op := op) (value := value) (ho := ho) (hv := hv) (hx := hx)
  all_goals grind

theorem AllocationSafe.initOpResults (h : AllocationSafe ctx) :
    AllocationSafe (Rewriter.initOpResults ctx op ts i ho hi) := by
  rcases h with ⟨hops, hbs, hrs⟩
  constructor <;> intro p hp <;> have hn := initOpResults_nextID (ctx := ctx) (op := op) (ts := ts) (i := i) (ho := ho) (hi := hi)
  all_goals grind

theorem AllocationSafe.initOpOperands (h : AllocationSafe ctx) :
    AllocationSafe (Rewriter.initOpOperands ctx op ho vs hx hv n hn) := by
  fun_induction Rewriter.initOpOperands <;> simp_all +zetaDelta [AllocationSafe.pushOperand]

theorem AllocationSafe.initOpRegions (h : AllocationSafe ctx)
    (hc : Rewriter.initOpRegions ctx op rs i ho hr hx hi = some ctx') : AllocationSafe ctx' := by
  rcases h with ⟨hops, hbs, hrs⟩
  have hn := initOpRegions_nextID hc
  constructor <;> intro p hp <;> grind

theorem AllocationSafe.insertOp (h : AllocationSafe ctx)
    (hc : Rewriter.insertOp ctx op ip ho hi hx = some ctx') : AllocationSafe ctx' := by
  rcases h with ⟨hops, hbs, hrs⟩
  have hn := insertOp_nextID hc
  constructor <;> intro p hp <;> grind

theorem AllocationSafe.insertBlock (h : AllocationSafe ctx)
    (hc : Rewriter.insertBlock ctx block ip hb hi hx = some ctx') : AllocationSafe ctx' := by
  rcases h with ⟨hops, hbs, hrs⟩
  have hn := insertBlock_nextID hc
  constructor <;> intro p hp <;> grind

theorem AllocationSafe.initBlockArguments (h : AllocationSafe ctx) :
    AllocationSafe (Rewriter.initBlockArguments ctx block ts 0 hb hi) := by
  rcases h with ⟨hops, hbs, hrs⟩
  have hn := initBlockArguments_nextID (ctx := ctx) (block := block) (ts := ts) (i := 0) (hb := hb) (hi := hi)
  constructor <;> intro p hp <;> grind

section
setup_grind_with_get_set_definitions

theorem AllocationSafe.allocateOp (h : AllocationSafe ctx) {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
    (code : Dialect) (props : propertiesOf code) :
    ∃ ctx' op, Rewriter.createEmptyOp ctx code props = some (ctx', op) ∧ AllocationSafe ctx' := by
  have hn : ¬ (OperationPtr.mk ctx.nextID).InBounds ctx := fun hp => Nat.lt_irrefl _ (h.operations _ hp)
  unfold Rewriter.createEmptyOp OperationPtr.allocEmpty
  simp only [OperationPtr.InBounds] at hn
  simp only [show ctx.operations.contains ⟨ctx.nextID⟩ = false by simpa using hn]
  refine ⟨_, _, rfl, ?_⟩; rcases h with ⟨ho, hb, hr⟩
  constructor <;> intro p hp <;>
    simp_all only [OperationPtr.set, OperationPtr.InBounds, BlockPtr.InBounds, RegionPtr.InBounds, Std.HashMap.mem_insert] <;> grind

theorem AllocationSafe.allocateRegion (h : AllocationSafe ctx) :
    ∃ ctx' region, Rewriter.createRegion ctx = some (ctx', region) ∧ AllocationSafe ctx' := by
  have hn : ¬ (RegionPtr.mk ctx.nextID).InBounds ctx := fun hp => Nat.lt_irrefl _ (h.regions _ hp)
  unfold Rewriter.createRegion RegionPtr.allocEmpty
  simp only [RegionPtr.InBounds] at hn
  simp only [show ctx.regions.contains ⟨ctx.nextID⟩ = false by simpa using hn]
  refine ⟨_, _, rfl, ?_⟩; rcases h with ⟨ho, hb, hr⟩
  constructor <;> intro p hp <;>
    simp_all only [RegionPtr.set, OperationPtr.InBounds, BlockPtr.InBounds, RegionPtr.InBounds, Std.HashMap.mem_insert] <;> grind

theorem AllocationSafe.allocateBlock (h : AllocationSafe ctx) :
    ∃ ctx' block, BlockPtr.allocEmpty ctx = some (ctx', block) ∧ AllocationSafe ctx' := by
  have hn : ¬ (BlockPtr.mk ctx.nextID).InBounds ctx := fun hp => Nat.lt_irrefl _ (h.blocks _ hp)
  unfold BlockPtr.allocEmpty
  simp only [BlockPtr.InBounds] at hn
  simp only [show ctx.blocks.contains ⟨ctx.nextID⟩ = false by simpa using hn]
  refine ⟨_, _, rfl, ?_⟩; rcases h with ⟨ho, hb, hr⟩
  constructor <;> intro p hp <;>
    simp_all only [BlockPtr.set, OperationPtr.InBounds, BlockPtr.InBounds, RegionPtr.InBounds, Std.HashMap.mem_insert] <;> grind

end

theorem AllocationSafe.empty : AllocationSafe (IRContext.empty OpCode) := by
  constructor <;> intro p hp <;>
    simp [OperationPtr.InBounds, BlockPtr.InBounds, RegionPtr.InBounds, IRContext.empty] at hp

end Veir.LLVMLowering
