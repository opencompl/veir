module

public import Veir.Rewriter.WfRewriter.EraseBlocks
public import Veir.IRNesting

/-!
# Erasing unreachable blocks

A block is unreachable if there is no CFG path to it from the entry block of
its region (see `BlockPtr.LocallyReachable`). The unreachable blocks of a region
are erased all at once, in four phases:

1. Compute the unreachable blocks of the region, and every operation, block, and
   region nested in them (`DeadBlockSet.compute!`). Nothing is modified.
2. Drop the operands and successors of every operation in the set. Since every
   predecessor of an unreachable block is itself unreachable, and an unreachable
   definition does not dominate any reachable use, nothing outside the set
   refers into the set afterwards.
3. Erase the operations in the set, along with their nested blocks and regions.
4. Erase the unreachable blocks, which are now empty.

Each step checks its own preconditions and panics if they do not hold, so a
bug in the computation of the set is reported rather than hidden.
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

/-- Add each of `successors` that is not in `reached` to `reached` and to the worklist. -/
def RegionPtr.reachableBlocks.visit :
    (successors : List BlockPtr) → (worklist : List BlockPtr) → (reached : Std.HashSet BlockPtr) →
    List BlockPtr × Std.HashSet BlockPtr
  | [], worklist, reached => (worklist, reached)
  | successor :: successors, worklist, reached =>
    if reached.contains successor then
      RegionPtr.reachableBlocks.visit successors worklist reached
    else
      RegionPtr.reachableBlocks.visit successors (successor :: worklist) (reached.insert successor)

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
    let (worklist, reached) :=
      RegionPtr.reachableBlocks.visit (block.getSuccessors! ctx).toList worklist reached
    RegionPtr.reachableBlocks.loop ctx fuel worklist reached

/--
  The blocks of `region` that are reachable from its entry block, following the
  successors of block terminators (as in `RegionPtr.Path`).
  Return `none` if the traversal runs out of fuel. Unlike the other traversals,
  this one does not panic itself: no fallback set is both computable here and
  closed under successors, so the caller (`DeadBlockSet.compute!`) panics instead,
  falling back to reporting no unreachable blocks, which keeps the analysis sound.
-/
def RegionPtr.reachableBlocks (region : RegionPtr) (ctx : IRContext OpInfo) :
    Option (Std.HashSet BlockPtr) :=
  match region.getFirstBlock! ctx with
  | none => some ∅
  | some entry => RegionPtr.reachableBlocks.loop ctx ctx.numNodes [entry] {entry}

/--
  Collect `block` and the blocks that follow it in its region.
  Panic if `fuel` runs out before the end of the region.
-/
def BlockPtr.collectBlockChain (ctx : IRContext OpInfo) :
    (fuel : Nat) → (block : Option BlockPtr) → (acc : Array BlockPtr) → Array BlockPtr
  | _, none, acc => acc
  | 0, some _, acc =>
    haveI : Inhabited (Array BlockPtr) := ⟨acc⟩
    panic! "BlockPtr.collectBlockChain: out of fuel"
  | fuel + 1, some block, acc =>
    BlockPtr.collectBlockChain ctx fuel (block.getNextBlock! ctx) (acc.push block)

/-- The blocks of `region`, in order. -/
def RegionPtr.getBlocks! (region : RegionPtr) (ctx : IRContext OpInfo) : Array BlockPtr :=
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
  Fold `f` over the nodes in `worklist` and everything nested in them. An
  operation node stands for itself and the operations that follow it in its
  block, a block node for itself and the blocks that follow it in its region.
  The order is depth first, but not strictly preorder: the operation (or block)
  that follows a node is visited before the nodes nested in it. The only
  ordering guarantee is that a region is visited before the regions nested in it.
  Panic if `fuel` runs out before the worklist is empty.
-/
def IRNode.foldNested {β : Type} (ctx : IRContext OpInfo) (f : β → IRNode → β) :
    (fuel : Nat) → (worklist : List IRNode) → (acc : β) → β
  | _, [], acc => acc
  | 0, _ :: _, acc =>
    haveI : Inhabited β := ⟨acc⟩
    panic! "IRNode.foldNested: out of fuel"
  | fuel + 1, node :: worklist, acc =>
    let worklist := match node with
      | .operation o =>
        let worklist := (o.getRegions! ctx).toList.map IRNode.region ++ worklist
        match o.getNextOp! ctx with
        | some next => .operation next :: worklist
        | none => worklist
      | .region r =>
        match r.getFirstBlock! ctx with
        | some b => .block b :: worklist
        | none => worklist
      | .block b =>
        let worklist := match b.getFirstOp! ctx with
          | some o => .operation o :: worklist
          | none => worklist
        match b.getNextBlock! ctx with
        | some next => .block next :: worklist
        | none => worklist
    IRNode.foldNested ctx f fuel worklist (f acc node)

/-- Add a node to the operations, nested blocks, or nested regions of `acc`. -/
def DeadBlockSet.add (acc : DeadBlockSet) : IRNode → DeadBlockSet
  | .operation op => { acc with ops := acc.ops.push op }
  | .block block => { acc with nestedBlocks := acc.nestedBlocks.push block }
  | .region region => { acc with nestedRegions := acc.nestedRegions.push region }

/-- Add the nodes in `worklist` to `acc`, together with everything nested in them. -/
def DeadBlockSet.collectNested (ctx : IRContext OpInfo) (worklist : List IRNode)
    (acc : DeadBlockSet) : DeadBlockSet :=
  IRNode.foldNested ctx DeadBlockSet.add ctx.numNodes worklist acc

/--
  Compute the unreachable blocks of `region`, and everything nested in them.
  Panic, reporting no unreachable blocks, if the reachability analysis runs out of fuel.
-/
def DeadBlockSet.compute! (ctx : IRContext OpInfo) (region : RegionPtr) : DeadBlockSet :=
  match region.reachableBlocks ctx with
  | none =>
    haveI : Inhabited DeadBlockSet := ⟨{}⟩
    panic! "DeadBlockSet.compute!: reachability analysis out of fuel"
  | some reachable =>
    let deadBlocks := (region.getBlocks! ctx).filter (!reachable.contains ·)
    let worklist := deadBlocks.toList.filterMap fun block => (block.getFirstOp! ctx).map .operation
    DeadBlockSet.collectNested ctx worklist { deadBlocks }

/--
  Erase the blocks of `dead` and everything nested in them.
  Panic if any step finds that its preconditions do not hold, which happens
  only if `dead` is not closed under uses, successors, and nesting.
-/
def WfRewriter.eraseDeadBlockSet! (ctx : WfIRContext OpInfo) (dead : DeadBlockSet) :
    WfIRContext OpInfo :=
  -- Phase 2: no operation in the set uses a value or a block anymore.
  let ctx := dead.ops.foldl WfRewriter.dropOperands! ctx
  -- Phase 3: erase the operations in the set, then their nested blocks and regions.
  let ctx := dead.ops.foldl (init := ctx) fun ctx op =>
    WfRewriter.eraseOp! (WfRewriter.detachRegions! ctx op) op
  let ctx := dead.nestedBlocks.foldl (init := ctx) fun ctx block =>
    WfRewriter.deallocBlock! (WfRewriter.detachBlock! ctx block) block
  let ctx := dead.nestedRegions.foldl WfRewriter.deallocRegion! ctx
  -- Phase 4: erase the now empty unreachable blocks.
  dead.deadBlocks.foldl (init := ctx) fun ctx block =>
    WfRewriter.deallocBlock! (WfRewriter.detachBlock! ctx block) block

/--
  Erase the blocks of `region` that are unreachable from its entry block,
  together with everything nested in them.
  Blocks in regions nested in reachable blocks are left unchanged.
-/
def WfRewriter.eraseUnreachableBlocks! (ctx : WfIRContext OpInfo) (region : RegionPtr) :
    WfIRContext OpInfo :=
  let dead := DeadBlockSet.compute! ctx.raw region
  if dead.deadBlocks.isEmpty then
    ctx
  else
    WfRewriter.eraseDeadBlockSet! ctx dead

/--
  Erase the unreachable blocks of every region nested in `root`.
  Regions are processed outermost first, so regions nested in an erased block are
  skipped.
-/
def WfRewriter.eraseUnreachableBlocksIn! (ctx : WfIRContext OpInfo) (root : OperationPtr) :
    WfIRContext OpInfo :=
  let worklist := (root.getRegions! ctx.raw).toList.map IRNode.region
  let regions := IRNode.foldNested ctx.raw (fun regions node =>
      match node with
      | .region region => regions.push region
      | _ => regions)
    ctx.raw.numNodes worklist #[]
  regions.foldl (init := ctx) fun ctx region =>
    if region.InBounds ctx.raw then
      WfRewriter.eraseUnreachableBlocks! ctx region
    else
      ctx

end Veir
