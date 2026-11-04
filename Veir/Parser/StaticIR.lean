module

public import Veir.Parser.Frames
public import Veir.Rewriter.WellFormed.CreateOp
public import Veir.Rewriter.WellFormed.CreateBlock
public import Veir.Rewriter.WellFormed.CreateRegion
public import Veir.Rewriter.WellFormed.ReplaceOp
public import Veir.Rewriter.WellFormed.Attributes
public import Veir.IR.Buffed.HasUses
public import Veir.Rewriter.WellFormed.EraseEmptyBlock
import all Veir.IR.Buffed.Sim
import all Veir.IR.Buffed.Basic

/-!
Proof-taking construction primitives. There is no address registry in this context, no
pointer validation, and no replacement of a caller's simulated pointer by another pointer.
Successful allocation returns its liveness proof and a frame for every existing handle.
All certificates are propositions and disappear during compilation.
-/
public section
namespace Veir.Parser.StaticIR

abbrev RawContext := IR.RawContext

structure Context where
  raw : RawContext
  wellFormed : raw.spec.WellFormed

@[inline, expose]
def empty : Context := ⟨Sim.IRContext.empty, Sim.IRContext.empty_wellFormed⟩

instance : Inhabited Context := ⟨empty⟩

abbrev Context.toIRContext (ctx : Context) : RawContext := ctx.raw
noncomputable abbrev Context.spec (ctx : Context) := ctx.raw.spec
abbrev Context.buf (ctx : Context) := ctx.raw.buf
instance : CoeOut Context RawContext := ⟨Context.raw⟩

@[inline]
def valueType (ctx : RawContext) (value : IR.Value) (_live : value.InBounds ctx) : Attribute :=
  IR.valueType ctx value

/-- This proof-only wrapper flattens to the raw context. Inline the dependent continuation
so erased preconditions do not leave partially applied runtime closures. -/
@[inline, expose]
def Context.withRaw {α : RawContext → Type} (ctx : Context)
    (f : (raw : RawContext) → raw.spec.WellFormed → α raw) : α ctx.raw :=
  f ctx.raw ctx.wellFormed

/-- An allocation-only (or in-place) transition preserves even local references which are
not stored in a parser table. -/
def Preserves (before after : RawContext) : Prop :=
  ∀ p : Sim.GenericPtr, p.InBounds before → p.InBounds after

theorem Preserves.refl (ctx : RawContext) : Preserves ctx ctx := fun _ hp => hp

theorem Preserves.trans {a b c : RawContext} (hab : Preserves a b) (hbc : Preserves b c) :
    Preserves a c := fun p hp => hbc p (hab p hp)

theorem Preserves.operation {a b : RawContext} (h : Preserves a b) {p : IR.Op}
    (hp : p.InBounds a) : p.InBounds b :=
  (Sim.GenericPtr.iff_operation p).mp (h (.fromOperation p) ((Sim.GenericPtr.iff_operation p).mpr hp))

theorem Preserves.block {a b : RawContext} (h : Preserves a b) {p : IR.Block}
    (hp : p.InBounds a) : p.InBounds b :=
  (Sim.GenericPtr.iff_block p).mp (h (.fromBlock p) ((Sim.GenericPtr.iff_block p).mpr hp))

theorem Preserves.region {a b : RawContext} (h : Preserves a b) {p : IR.Region}
    (hp : p.InBounds a) : p.InBounds b :=
  (Sim.GenericPtr.iff_region p).mp (h (.fromRegion p) ((Sim.GenericPtr.iff_region p).mpr hp))

theorem Preserves.value {a b : RawContext} (h : Preserves a b) {p : IR.Value}
    (hp : p.InBounds a) : p.InBounds b :=
  (Sim.GenericPtr.iff_value p).mp (h (.fromValue p) ((Sim.GenericPtr.iff_value p).mpr hp))

theorem Preserves.insertPoint {a b : RawContext} (h : Preserves a b) {ip : InsertPoint}
    (hi : ip.InBounds a.spec) : ip.InBounds b.spec := by
  cases ip with
  | before op =>
    have hp : op.toSim.InBounds a := by grind
    have hn := h.operation hp
    grind
  | atEnd block =>
    have hp : block.toSim.InBounds a := by grind
    have hn := h.block hp
    grind

theorem Preserves.blockInsertPoint {a b : RawContext} (h : Preserves a b) {ip : BlockInsertPoint}
    (hi : ip.InBounds a.spec) : ip.InBounds b.spec := by
  cases ip with
  | before block =>
    have hp : block.toSim.InBounds a := by grind
    have hn := h.block hp
    grind
  | atEnd region =>
    have hp : region.toSim.InBounds a := by grind
    have hn := h.region hp
    grind

/-- Construct a checked insertion point from an allocated region, without testing its address. -/
def regionEnd (ctx : RawContext) (region : IR.Region) (hi : region.InBounds ctx) :
    { ip : BlockInsertPoint // ip.InBounds ctx.spec ∧ ip.IsRepr } :=
  let ip := BlockInsertPoint.atEnd ⟨region.impl.toNat⟩
  have hs : RegionPtr.mk region.impl.toNat = region.spec := congrArg RegionPtr.mk (by
    simpa only [RegionPtr.toFlat] using (Sim.RegionPtr.toFlat_eq_impl_toNat hi).symm)
  ⟨ip, by
    change (RegionPtr.mk region.impl.toNat).InBounds ctx.spec ∧ (RegionPtr.mk region.impl.toNat).IsRepr
    rw [hs]
    exact ⟨hi.ib, ctx.isRepr.regions region.spec hi.ib⟩⟩

def blockEnd (ctx : RawContext) (block : IR.Block) (hi : block.InBounds ctx) :
    { ip : InsertPoint // ip.InBounds ctx.spec ∧ ip.IsRepr } :=
  let ip := InsertPoint.atEnd ⟨block.impl.toNat⟩
  have hs : BlockPtr.mk block.impl.toNat = block.spec := congrArg BlockPtr.mk (by
    simpa only [BlockPtr.toFlat] using (Sim.BlockPtr.toFlat_eq_impl_toNat hi).symm)
  ⟨ip, by
    change (BlockPtr.mk block.impl.toNat).InBounds ctx.spec ∧ (BlockPtr.mk block.impl.toNat).IsRepr
    rw [hs]
    exact ⟨hi.ib, ctx.isRepr.blocks block.spec hi.ib⟩⟩

structure Allocation (before : RawContext) (α : Type) (live : α → RawContext → Prop) where
  ctx : Context
  pointer : α
  inBounds : live pointer ctx.raw
  preserves : Preserves before ctx.raw

structure OpAllocation (before : RawContext) (resultCount : Nat)
    extends Allocation before IR.Op Sim.OperationPtr.InBounds where
  fresh : ¬ pointer.spec.InBounds before.spec
  results : pointer.spec.getNumResults! ctx.raw.spec = resultCount

structure BlockAllocation (before : RawContext) (argumentCount : Nat)
    extends Allocation before IR.Block Sim.BlockPtr.InBounds where
  fresh : ¬ pointer.spec.InBounds before.spec
  arguments : pointer.spec.getNumArguments! ctx.raw.spec = argumentCount

/-- A result index is justified by the allocation's result count, not checked again at runtime. -/
def OpAllocation.result {before : RawContext} {count : Nat} (a : OpAllocation before count)
    (index : Fin count) : { v : IR.Value // v.InBounds a.ctx.raw ∧
      v.spec = .opResult ⟨a.pointer.spec, index.val.toUInt64.toNat⟩ } :=
  let result := a.pointer.getResultPtr a.ctx.raw index.val.toUInt64 a.inBounds
  have hi : index.val.toUInt64.toNat < a.pointer.spec.getNumResults! a.ctx.raw.spec := by
    rw [a.results]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) index.isLt
  ⟨Sim.ValuePtr.fromOpResultPtr result, by grind [generic_ptr_grind], by
    simp [result, Sim.ValuePtr.fromOpResultPtr, Sim.ValuePtr.spec, Sim.OperationPtr.getResultPtr.unfold,
      OperationPtr.getResult, Sim.OperationPtr.spec, Erased.map_out]⟩

def BlockAllocation.argument {before : RawContext} {count : Nat} (a : BlockAllocation before count)
    (index : Fin count) : { v : IR.Value // v.InBounds a.ctx.raw ∧
      v.spec = .blockArgument ⟨a.pointer.spec, index.val.toUInt64.toNat⟩ } :=
  let arg := a.pointer.getArgumentPtr a.ctx.raw index.val.toUInt64 a.inBounds
  have hi : index.val.toUInt64.toNat < a.pointer.spec.getNumArguments! a.ctx.raw.spec := by
    rw [a.arguments]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) index.isLt
  ⟨Sim.ValuePtr.fromBlockArgumentPtr arg, by grind [generic_ptr_grind], by
    simp [arg, Sim.ValuePtr.fromBlockArgumentPtr, Sim.ValuePtr.spec, Sim.BlockPtr.getArgumentPtr.unfold,
      BlockPtr.getArgument, Sim.BlockPtr.spec, Erased.map_out]⟩

structure Mutation (before : RawContext) where
  ctx : Context
  preserves : Preserves before ctx.raw

/-- The array and insertion-point contracts are proofs, not executable checks. -/
@[noinline]
def createOp (ctx : Context) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array IR.Value) (successors : Array IR.Block) (regions : Array IR.Region)
    (properties : propertiesOf opType) (ip : Option InsertPoint) :
    (∀ i (hi : i < operands.size), operands[i].InBounds ctx.raw) →
    (∀ i (hi : i < successors.size), successors[i].InBounds ctx.raw) →
    (∀ i (hi : i < regions.size), regions[i].InBounds ctx.raw) →
    ip.maybe InsertPoint.InBounds ctx.raw.spec → ip.maybe₁ InsertPoint.IsRepr →
    Option (OpAllocation ctx.raw resultTypes.size) :=
  ctx.withRaw (α := fun raw =>
    (∀ i (hi : i < operands.size), operands[i].InBounds raw) →
    (∀ i (hi : i < successors.size), successors[i].InBounds raw) →
    (∀ i (hi : i < regions.size), regions[i].InBounds raw) →
    ip.maybe InsertPoint.InBounds raw.spec → ip.maybe₁ InsertPoint.IsRepr →
    Option (OpAllocation raw resultTypes.size)) fun raw wf hoper hsucc hregion hip hrep =>
    if htypes : resultTypes.size < 2^32 then
      match hc : Rewriter.createOp raw opType resultTypes operands successors regions properties ip
        hoper hsucc hregion hip hrep htypes raw.fieldsInBounds with
      | none => none
      | some (next, op) =>
        some ⟨⟨⟨next, Rewriter.createOp_preserves_wellFormed wf hc⟩, op,
          Rewriter.createOp_new_inBounds op hc, Rewriter.createOp_sim_inBounds_mono hc⟩,
          Rewriter.createOp_new_not_inBounds op hc, Rewriter.createOp_numResults wf hc⟩
    else none

@[noinline]
def createBlock (ctx : Context) (types : Array TypeAttr) (ip : Option BlockInsertPoint) :
    ip.maybe BlockInsertPoint.InBounds ctx.raw.spec → ip.maybe₁ BlockInsertPoint.IsRepr →
    Option (BlockAllocation ctx.raw types.size) :=
  ctx.withRaw (α := fun raw => ip.maybe BlockInsertPoint.InBounds raw.spec →
    ip.maybe₁ BlockInsertPoint.IsRepr → Option (BlockAllocation raw types.size)) fun raw wf hip hrep =>
    match hc : Rewriter.createBlock raw types ip hip hrep with
    | none => none
    | some (next, block) =>
      some ⟨⟨⟨next, Rewriter.createBlock_preserves_wellFormed wf hc⟩, block,
        Rewriter.createBlock_new_inBounds hc, fun p hp => Rewriter.createBlock_inBounds_mono p hc hp⟩,
        Rewriter.createBlock_new_not_inBounds hc, Rewriter.createBlock_numArguments wf hc⟩

@[noinline]
def createRegion (ctx : Context) : Option (Allocation ctx.raw IR.Region Sim.RegionPtr.InBounds) :=
  ctx.withRaw (α := fun raw => Option (Allocation raw IR.Region Sim.RegionPtr.InBounds)) fun raw wf =>
    match hc : Rewriter.createRegion raw with
    | none => none
    | some (next, region) =>
      some ⟨⟨next, Rewriter.createRegion_wellFormed wf hc⟩, region,
        Rewriter.createRegion_new_inBounds hc, Rewriter.createRegion_inBounds_mono hc⟩

@[noinline]
def insertBlock (ctx : Context) (block : IR.Block) (ip : BlockInsertPoint) :
    block.InBounds ctx.raw → ip.InBounds ctx.raw.spec → ip.IsRepr → Option (Mutation ctx.raw) :=
  ctx.withRaw (α := fun raw => block.InBounds raw → ip.InBounds raw.spec → ip.IsRepr →
    Option (Mutation raw)) fun raw wf hb hip hrep =>
    match hc : Rewriter.insertBlock? raw block ip hb hip hrep raw.fieldsInBounds with
    | none => none
    | some next => some ⟨⟨next,
        Rewriter.insertBlock?_WellFormed raw block ip hb hip hrep raw.fieldsInBounds wf hc⟩,
        fun p hp => (Rewriter.insertBlock?_inBounds p hc).mp hp⟩

@[noinline]
def replaceValue (ctx : Context) (oldValue newValue : IR.Value) :
    oldValue.InBounds ctx.raw → newValue.InBounds ctx.raw → Option (Mutation ctx.raw) :=
  ctx.withRaw (α := fun raw => oldValue.InBounds raw → newValue.InBounds raw →
    Option (Mutation raw)) fun raw wf hold hnew =>
    if oldValue.impl = newValue.impl then some ⟨⟨raw, wf⟩, Preserves.refl raw⟩ else
    match hc : Rewriter.replaceValue? raw oldValue newValue hold hnew raw.fieldsInBounds with
    | none => none
    | some next => some ⟨⟨next,
        Rewriter.replaceValue?_WellFormed oldValue newValue hold hnew raw.fieldsInBounds wf hc⟩,
        fun p hp => (Rewriter.replaceValue?_inBounds p hc).mp hp⟩

@[noinline]
def setAttributes (ctx : Context) (op : IR.Op) (attrs : DictionaryAttr) :
    op.InBounds ctx.raw → Option (Mutation ctx.raw) :=
  ctx.withRaw (α := fun raw => op.InBounds raw → Option (Mutation raw)) fun raw wf hop =>
    match hc : Sim.OperationPtr.setAttributes raw op attrs hop with
    | none => none
    | some next =>
      have hs := Sim.OperationPtr.setAttributes_spec raw op attrs hop hc
      have hl : next.spec.LayoutUnchanged raw.spec := by
        rw [hs, IRContext.LayoutUnchanged.symm]
        exact OperationPtr.setAttributes_preservesLayout hop.ib
      some ⟨⟨next, Sim.OperationPtr.setAttributes_wellFormed raw op attrs hop wf hc⟩,
        fun p hp => ⟨Sim.GenericPtr.sim_layoutUnchanged hp hl, by
          rw [hs]
          grind [GenericPtr.InBounds]⟩⟩

/-- Attach attributes while the allocation's liveness certificate is still available.
No address lookup is needed, and the allocation wrapper is consumed before mutation. -/
@[noinline]
def Allocation.setAttributes {before : RawContext}
    (allocation : Allocation before IR.Op Sim.OperationPtr.InBounds) (attrs : DictionaryAttr) :
    Option (Allocation before IR.Op Sim.OperationPtr.InBounds) := do
  let ⟨ctx, op, hp, frame⟩ := allocation
  if attrs.entries.isEmpty then return ⟨ctx, op, hp, frame⟩
  let updated ← StaticIR.setAttributes ctx op attrs hp
  return ⟨updated.ctx, op, updated.preserves.operation hp, frame.trans updated.preserves⟩

/-- A deletion frame is a proposition: returning it alongside a parser state must not
retain a second runtime reference to the IR buffer. -/
structure OpFrame (before after : RawContext) (dead : IR.Op) : Prop where
  operations : ∀ p : IR.Op, p.InBounds before → p.spec ≠ dead.spec → p.InBounds after
  blocks : ∀ p : IR.Block, p.InBounds before → p.InBounds after
  regions : ∀ p : IR.Region, p.InBounds before → p.InBounds after
  values : ∀ p : IR.Value, p.InBounds before →
    (∀ res, p.spec = .opResult res → res.op ≠ dead.spec) → p.InBounds after

/-- The precise frame for deletion: only results of the deleted operation may lose liveness. -/
structure OpDeletion (before : RawContext) (dead : IR.Op) where
  ctx : Context
  operations : ∀ p : IR.Op, p.InBounds before → p.spec ≠ dead.spec → p.InBounds ctx.raw
  blocks : ∀ p : IR.Block, p.InBounds before → p.InBounds ctx.raw
  regions : ∀ p : IR.Region, p.InBounds before → p.InBounds ctx.raw
  values : ∀ p : IR.Value, p.InBounds before →
    (∀ res, p.spec = .opResult res → res.op ≠ dead.spec) → p.InBounds ctx.raw

theorem OpDeletion.frame {before : RawContext} {dead : IR.Op} (d : OpDeletion before dead) :
    OpFrame before d.ctx.raw dead := ⟨d.operations, d.blocks, d.regions, d.values⟩

/-- Liveness is supplied statically. The remaining guards are deletion's semantic conditions
(no regions and no result uses), not pointer validation. -/
@[noinline]
def eraseOp (ctx : Context) (op : IR.Op) :
    op.InBounds ctx.raw → Option (OpDeletion ctx.raw op) :=
  ctx.withRaw (α := fun raw => op.InBounds raw → Option (OpDeletion raw op)) fun raw wf hib =>
    if hregions : op.getNumRegions raw hib = 0 then
      if huses : op.hasUses raw hib wf = false then
        have hwf := wf.operations op.spec hib.ib
        have hrepr := raw.isRepr.operations_indices op.spec hib.ib
        have noRegions : op.spec.getNumRegions! raw.spec = 0 := by
          have := hwf.capRegions_eq_numRegions
          grind
        have noUses : op.spec.hasUses! raw.spec = false := by
          rwa [Sim.OperationPtr.hasUses_spec] at huses
        have hd := Rewriter.eraseOp_deallocFieldsInBounds raw op wf noRegions noUses
        let next := Rewriter.eraseOp raw op raw.fieldsInBounds hib hwf.capOperands_eq_numOperands
          hwf.capBlockOperands_eq_numSuccessors hd
        some ⟨⟨next, Rewriter.eraseOp_WellFormed raw op wf raw.fieldsInBounds hib
            hwf.capOperands_eq_numOperands hwf.capBlockOperands_eq_numSuccessors noRegions noUses hd⟩,
          fun _ hp hn => Rewriter.eraseOp_operation_inBounds hp hn,
          fun _ hp => Rewriter.eraseOp_block_inBounds hp,
          fun _ hp => Rewriter.eraseOp_region_inBounds hp,
          fun _ hp hn => Rewriter.eraseOp_value_inBounds hp hn⟩
      else none
    else none

structure BlockDeletion (before : RawContext) (dead : IR.Block) where
  ctx : Context
  operations : ∀ p : IR.Op, p.InBounds before → p.InBounds ctx.raw
  blocks : ∀ p : IR.Block, p.InBounds before → p.spec ≠ dead.spec → p.InBounds ctx.raw
  regions : ∀ p : IR.Region, p.InBounds before → p.InBounds ctx.raw
  values : ∀ p : IR.Value, p.InBounds before → p.InBounds ctx.raw

@[noinline]
def eraseBlock (ctx : Context) (block : IR.Block) :
    block.InBounds ctx.raw → Option (BlockDeletion ctx.raw block) :=
  ctx.withRaw (α := fun raw => block.InBounds raw → Option (BlockDeletion raw block)) fun raw wf hib => do
    have hfields := raw.fieldsInBounds
    match hp : (block.getParent raw hib).toOption with
    | some _ => none
    | none =>
      match ho : (block.getFirstOp raw hib).toOption with
      | some _ => none
      | none =>
        match hu : (block.getFirstUse raw hib).toOption with
        | some _ => none
        | none =>
          if ha : block.getNumArguments raw hib = 0 then
            have parent : (block.spec.get! raw.spec).parent = none := by
              have := (Sim.OptionRegionPtr.toOption_none_iff_spec_none (ctx := raw) (by grind)).mp hp
              grind
            have ops : (block.spec.get! raw.spec).firstOp = none := by
              have := (Sim.OptionOperationPtr.toOption_none_iff_spec_none (ctx := raw) (by grind)).mp ho
              grind
            have uses : (block.spec.get! raw.spec).firstUse = none := by
              have := (Sim.OptionBlockOperandPtr.toOption_none_iff_spec_none (ctx := raw) (by grind)).mp hu
              grind
            have args : block.spec.getNumArguments! raw.spec = 0 := by
              have := (wf.blocks block.spec hib.ib).capBlockArguments_eq_numBlockArguments
              have := Sim.BlockPtr.getNumArguments_spec raw block hib
              grind
            have hd := IRContext.fieldsInBounds_deallocEmptyBlock block.spec hib.ib wf parent args ops uses
            let next := Rewriter.eraseBlock raw block hib parent hd
            have hs := Rewriter.eraseBlock_spec raw block hib parent hd
            return ⟨⟨next, Rewriter.eraseBlock_wellFormed raw block hib parent hd wf⟩,
              fun p hp => ⟨hp.sim, by rw [hs]; grind⟩,
              fun p hp hn => ⟨hp.sim, by rw [hs]; grind⟩,
              fun p hp => ⟨hp.sim, by rw [hs]; grind⟩,
              fun _ hp => Rewriter.eraseBlock_value_inBounds (hp := parent) hp args⟩
          else none

/-- Successor redirection transports the input proofs through each use-list update. The
address equality test is the algorithm's self-replacement case, not a validity test. -/
partial def replaceBlockUses (ctx : Context) (oldBlock newBlock : IR.Block) :
    oldBlock.InBounds ctx.raw → newBlock.InBounds ctx.raw → Option (Mutation ctx.raw) :=
  ctx.withRaw (α := fun raw => oldBlock.InBounds raw → newBlock.InBounds raw → Option (Mutation raw))
    fun raw wf hold hnew => do
      if oldBlock.impl = newBlock.impl then return ⟨⟨raw, wf⟩, Preserves.refl raw⟩
      match huse : (oldBlock.getFirstUse raw hold).toOption with
      | none => return ⟨⟨raw, wf⟩, Preserves.refl raw⟩
      | some use =>
        have hu : use.InBounds raw := by have := raw.fieldsInBounds; grind
        let next := Rewriter.replaceBlockUse raw use newBlock hu hnew
        have frame : Preserves raw next := fun p hp =>
          (Rewriter.replaceBlockUse_inBounds raw use newBlock hu hnew p).mpr hp
        let result ← replaceBlockUses
          ⟨next, Rewriter.replaceBlockUse_wellFormed raw use newBlock hu hnew wf⟩ oldBlock newBlock
          (frame.block hold) (frame.block hnew)
        return ⟨result.ctx, frame.trans result.preserves⟩

end Veir.Parser.StaticIR
