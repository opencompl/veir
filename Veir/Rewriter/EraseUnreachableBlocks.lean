module

public import Veir.Rewriter.WfRewriter.EraseBlocks
public import Veir.IRNesting

/-!
# Erasing unreachable blocks

A block is unreachable if there is no CFG path to it from the entry block of
its region (see `BlockPtr.LocallyReachable`). The unreachable blocks of a region
are erased all at once, in four phases:

1. Compute the unreachable blocks of the region, and every operation, block, and
   region nested in them (`DeadBlockSet.compute?`). Nothing is modified.
2. Drop the operands and successors of every operation in the set. Since every
   predecessor of an unreachable block is itself unreachable, and an unreachable
   definition does not dominate any reachable use, nothing outside the set
   refers into the set afterwards.
3. Erase the operations in the set, along with their nested blocks and regions.
4. Erase the unreachable blocks, which are now empty.

Each step checks its own preconditions and returns `none` if they do not hold,
so the context stays well formed whether or not the set was computed correctly.
-/

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
  An upper bound on the number of operations, blocks, and regions in the
  context, used as fuel for the traversals below.
-/
def IRContext.numNodes (ctx : IRContext OpInfo) : Nat :=
  ctx.operations.size + ctx.blocks.size + ctx.regions.size + 1

/--
  Explore the CFG from the blocks in `worklist`, adding each newly found
  successor to `reached` and to the worklist.
  Return `none` if `fuel` runs out before the worklist is empty.
-/
def RegionPtr.reachableBlocks.loop (ctx : IRContext OpInfo) :
    (fuel : Nat) → (worklist : List BlockPtr) → (reached : Std.HashSet BlockPtr) →
    Option (Std.HashSet BlockPtr)
  | _, [], reached => some reached
  | 0, _ :: _, _ => none
  | fuel + 1, block :: worklist, reached =>
    let (worklist, reached) := (block.getSuccessors! ctx).foldl (init := (worklist, reached))
      fun (worklist, reached) successor =>
        if reached.contains successor then
          (worklist, reached)
        else
          (successor :: worklist, reached.insert successor)
    RegionPtr.reachableBlocks.loop ctx fuel worklist reached

/--
  The blocks of `region` that are reachable from its entry block, following the
  successors of block terminators (as in `RegionPtr.Path`).
-/
def RegionPtr.reachableBlocks (region : RegionPtr) (ctx : IRContext OpInfo) :
    Option (Std.HashSet BlockPtr) :=
  match region.getFirstBlock! ctx with
  | none => some ∅
  | some entry => RegionPtr.reachableBlocks.loop ctx ctx.numNodes [entry] {entry}

/-- Collect `block` and the blocks that follow it in its region. -/
def BlockPtr.collectBlockChain (ctx : IRContext OpInfo) :
    (fuel : Nat) → (block : Option BlockPtr) → (acc : Array BlockPtr) → Option (Array BlockPtr)
  | _, none, acc => some acc
  | 0, some _, _ => none
  | fuel + 1, some block, acc =>
    BlockPtr.collectBlockChain ctx fuel (block.getNextBlock! ctx) (acc.push block)

/-- The blocks of `region`, in order. -/
def RegionPtr.getBlocks? (region : RegionPtr) (ctx : IRContext OpInfo) : Option (Array BlockPtr) :=
  BlockPtr.collectBlockChain ctx ctx.numNodes (region.getFirstBlock! ctx) #[]

/-- The unreachable blocks of a region, and everything nested in them. -/
structure DeadBlockSet where
  /-- The unreachable blocks, whose parent is the region being simplified. -/
  deadBlocks : Array BlockPtr := #[]
  /-- Every operation nested, at any depth, in an unreachable block. -/
  ops : Array OperationPtr := #[]
  /-- Every block of a region of an operation in `ops`. -/
  nestedBlocks : Array BlockPtr := #[]
  /-- Every region of an operation in `ops`. -/
  nestedRegions : Array RegionPtr := #[]

/--
  Add the nodes in `worklist` to `acc`, together with everything nested in them.
  An operation node stands for itself and the operations that follow it in its
  block, a block node for itself and the blocks that follow it in its region.
  Return `none` if `fuel` runs out before the worklist is empty.
-/
def DeadBlockSet.collectNested (ctx : IRContext OpInfo) :
    (fuel : Nat) → (worklist : List IRNode) → (acc : DeadBlockSet) → Option DeadBlockSet
  | _, [], acc => some acc
  | 0, _ :: _, _ => none
  | fuel + 1, node :: worklist, acc =>
    match node with
    | .operation op =>
      let worklist := (op.getRegions! ctx).toList.map IRNode.region ++ worklist
      let worklist := match op.getNextOp! ctx with
        | some next => .operation next :: worklist
        | none => worklist
      DeadBlockSet.collectNested ctx fuel worklist { acc with ops := acc.ops.push op }
    | .region region =>
      let worklist := match region.getFirstBlock! ctx with
        | some block => .block block :: worklist
        | none => worklist
      DeadBlockSet.collectNested ctx fuel worklist
        { acc with nestedRegions := acc.nestedRegions.push region }
    | .block block =>
      let worklist := match block.getFirstOp! ctx with
        | some op => .operation op :: worklist
        | none => worklist
      let worklist := match block.getNextBlock! ctx with
        | some next => .block next :: worklist
        | none => worklist
      DeadBlockSet.collectNested ctx fuel worklist
        { acc with nestedBlocks := acc.nestedBlocks.push block }

/-- Compute the unreachable blocks of `region`, and everything nested in them. -/
def DeadBlockSet.compute? (ctx : IRContext OpInfo) (region : RegionPtr) : Option DeadBlockSet := do
  let reachable ← region.reachableBlocks ctx
  let blocks ← region.getBlocks? ctx
  let deadBlocks := blocks.filter (!reachable.contains ·)
  let worklist := deadBlocks.toList.filterMap fun block => (block.getFirstOp! ctx).map .operation
  DeadBlockSet.collectNested ctx ctx.numNodes worklist { deadBlocks }

/--
  Erase the blocks of `dead` and everything nested in them.
  Return `none` if any step finds that its preconditions do not hold, which
  happens only if `dead` is not closed under uses, successors, and nesting.
-/
def WfRewriter.eraseDeadBlockSet? (ctx : WfIRContext OpInfo) (dead : DeadBlockSet) :
    Option (WfIRContext OpInfo) := do
  -- Phase 2: no operation in the set uses a value or a block anymore.
  let ctx ← dead.ops.foldlM WfRewriter.dropOperands? ctx
  -- Phase 3: erase the operations in the set, then their nested blocks and regions.
  let ctx ← dead.ops.foldlM (init := ctx) fun ctx op => do
    WfRewriter.eraseOp? (← WfRewriter.detachRegions? ctx op) op
  let ctx ← dead.nestedBlocks.foldlM (init := ctx) fun ctx block => do
    WfRewriter.deallocBlock? (← WfRewriter.detachBlockIfAttached? ctx block) block
  let ctx ← dead.nestedRegions.foldlM WfRewriter.deallocRegion? ctx
  -- Phase 4: erase the now empty unreachable blocks.
  dead.deadBlocks.foldlM (init := ctx) fun ctx block => do
    WfRewriter.deallocBlock? (← WfRewriter.detachBlock? ctx block) block

/--
  Erase the blocks of `region` that are unreachable from its entry block,
  together with everything nested in them.
  Blocks in regions nested in reachable blocks are left unchanged.
-/
def WfRewriter.eraseUnreachableBlocks? (ctx : WfIRContext OpInfo) (region : RegionPtr) :
    Option (WfIRContext OpInfo) := do
  let dead ← DeadBlockSet.compute? ctx.raw region
  if dead.deadBlocks.isEmpty then
    return ctx
  WfRewriter.eraseDeadBlockSet? ctx dead

/--
  Erase the unreachable blocks of every region nested in `root`.
  Regions are processed outermost first, so regions nested in an erased block are
  skipped.
-/
def WfRewriter.eraseUnreachableBlocksIn? (ctx : WfIRContext OpInfo) (root : OperationPtr) :
    Option (WfIRContext OpInfo) := do
  let worklist := (root.getRegions! ctx.raw).toList.map IRNode.region
  let nested ← DeadBlockSet.collectNested ctx.raw ctx.raw.numNodes worklist {}
  nested.nestedRegions.foldlM (init := ctx) fun ctx region =>
    if region.InBounds ctx.raw then
      WfRewriter.eraseUnreachableBlocks? ctx region
    else
      some ctx

end Veir
