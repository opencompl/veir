module

public import Veir.Analysis.DataFlow.DominanceAnalysis
public import Veir.Interfaces.RegionKindInterfaces

public section

namespace Veir

open Std (HashMap HashSet)

/--
Dominance frontiers for the reachable CFG of one SSA region.

Compute this once with `DominanceFrontier.compute`, then use `iterated` for each
memory slot's defining blocks when placing SSA block arguments. The cached data
remains valid only while the region's blocks and CFG edges are unchanged.
-/
structure DominanceFrontier where
  /-- Reachable blocks in region order, used to give queries a stable order. -/
  blocks : Array BlockPtr := #[]
  /-- Each reachable block's frontier, also in region order. -/
  frontiers : HashMap BlockPtr (Array BlockPtr) := {}

namespace DominanceFrontier

/--
Compute ordinary dominance frontiers using predecessor walks up the immediate
dominator tree. A block `b` belongs to `DF(a)` when `a` dominates a reachable
predecessor of `b`, but does not strictly dominate `b`.

The caller must supply completed `DominanceAnalysis` facts for the current CFG
and a structurally verified region (in particular, its entry has no predecessors).
Unreachable blocks and predecessor edges from them are ignored. Empty regions
and regions without SSA dominance have empty frontiers. Nested regions are not
traversed; each needs its own frontier computation.

This deliberately simple implementation materializes all frontiers, which can
require quadratic space. The result can be reused for multiple IDF queries.
-/
def compute (region : RegionPtr) (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DominanceFrontier := Id.run do
  if !region.hasSSADominance irCtx then
    return {}

  let mut result : DominanceFrontier := {}
  let mut current := (region.get! irCtx.raw).firstBlock
  while let some block := current do
    current := (block.get! irCtx.raw).next
    if block.isReachable dfCtx then
      result := { result with
        blocks := result.blocks.push block
        frontiers := result.frontiers.insert block #[] }

  for block in result.blocks do
    let idom := (block.getIDom? dfCtx).get!
    -- The entry's immediate dominator is itself, and it has no predecessors.
    if block = idom then
      continue
    let mut seen : HashSet BlockPtr := ∅
    let mut currentUse := (block.get! irCtx.raw).firstUse
    while let some predUse := currentUse do
      let use := predUse.get! irCtx.raw
      currentUse := use.nextUse
      let some pred := (use.owner.get! irCtx.raw).parent | continue
      if !result.frontiers.contains pred then
        continue
      let mut runner := pred
      while runner ≠ idom do
        -- A previously visited chain has already contributed this block.
        -- This also deduplicates multiple edges from the same predecessor.
        if seen.contains runner then
          break
        seen := seen.insert runner
        result := { result with
          frontiers := result.frontiers.insert runner ((result.frontiers[runner]!).push block) }
        runner := (runner.getIDom? dfCtx).get!
  return result

/--
Return the iterated dominance frontier of `definingBlocks`, without liveness
pruning. These are candidate blocks for new SSA block arguments.

The result contains no duplicates and follows region order, independently of
the order or multiplicity of the seeds. Unreachable seeds and seeds from other
regions are ignored. A seed can itself occur in the result, for example at a
loop header; being a definition does not exclude a block from the frontier.
-/
def iterated (frontier : DominanceFrontier)
    (definingBlocks : Array BlockPtr) : Array BlockPtr := Id.run do
  let mut workList := #[]
  let mut scheduled : HashSet BlockPtr := ∅
  for block in definingBlocks do
    if frontier.frontiers.contains block && !scheduled.contains block then
      scheduled := scheduled.insert block
      workList := workList.push block

  let mut mergeBlocks : HashSet BlockPtr := ∅
  while !workList.isEmpty do
    let block := workList.back!
    workList := workList.pop
    for merge in frontier.frontiers[block]! do
      mergeBlocks := mergeBlocks.insert merge
      if !scheduled.contains merge then
        scheduled := scheduled.insert merge
        workList := workList.push merge
  return frontier.blocks.filter mergeBlocks.contains

end DominanceFrontier

end Veir
