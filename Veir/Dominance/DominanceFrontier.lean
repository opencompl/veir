module

public import Veir.Dominance.Lemmas.Path
public import Veir.Interfaces.RegionKindInterfaces
import Veir.Dominance.Lemmas.Block

/-!
# Dominance Frontier Specifications

Dominance frontiers are defined on the reachable CFG of one SSA region, using
the path-based dominance definitions. Unreachable predecessors are excluded.
Iterated frontiers follow one or more frontier steps, so a defining block is
included only if a frontier path reaches it, for example through a loop.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo} {region : RegionPtr}
variable {dominator block block₁ block₂ : BlockPtr}

/-! ## Ordinary dominance frontiers -/

/--
`block` belongs to the dominance frontier of `dominator` in an SSA `region`.
Both blocks are reachable in the region. The dominator dominates a reachable
predecessor of `block`, but does not properly dominate `block` itself.

The successor relation is the same as in `RegionPtr.Path`. Dominance here is
the reflexive closure of proper SSA dominance within this region; it does not
include dominance through enclosing regions. Self-frontiers are permitted.
-/
def BlockPtr.InDominanceFrontier (dominator block : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  region.hasSSADominance ctx = true ∧
  block.LocallyReachable region ctx ∧
  ∃ predecessor : BlockPtr,
    predecessor.LocallyReachable region ctx ∧
    block ∈ predecessor.getSuccessors! ctx.raw ∧
    (dominator = predecessor ∨
      dominator.ProperlyDominatesInSSACFGRegion predecessor region ctx) ∧
    ¬ dominator.ProperlyDominatesInSSACFGRegion block region ctx

namespace BlockPtr.InDominanceFrontier

/-- A reachable predecessor can witness frontier membership. -/
theorem of_predecessor {predecessor : BlockPtr}
    (ssa : region.hasSSADominance ctx = true)
    (reachable : block.LocallyReachable region ctx)
    (predecessorReachable : predecessor.LocallyReachable region ctx)
    (successor : block ∈ predecessor.getSuccessors! ctx.raw)
    (dominance : dominator = predecessor ∨
      dominator.ProperlyDominatesInSSACFGRegion predecessor region ctx)
    (notProper : ¬ dominator.ProperlyDominatesInSSACFGRegion block region ctx) :
    dominator.InDominanceFrontier block region ctx :=
  ⟨ssa, reachable, predecessor, predecessorReachable, successor, dominance, notProper⟩

/-- Frontier membership supplies a reachable predecessor witnessing the dominance conditions. -/
@[grind →]
theorem exists_predecessor (frontier : dominator.InDominanceFrontier block region ctx) :
    ∃ predecessor : BlockPtr,
      predecessor.LocallyReachable region ctx ∧
      block ∈ predecessor.getSuccessors! ctx.raw ∧
      (dominator = predecessor ∨
        dominator.ProperlyDominatesInSSACFGRegion predecessor region ctx) ∧
      ¬ dominator.ProperlyDominatesInSSACFGRegion block region ctx :=
  frontier.2.2

/-- Frontier membership is restricted to SSA regions. -/
@[grind →]
theorem hasSSADominance (frontier : dominator.InDominanceFrontier block region ctx) :
    region.hasSSADominance ctx = true :=
  frontier.1

/-- The block whose frontier is taken is reachable in the region. -/
@[grind →]
theorem locallyReachable_dominator
    (frontier : dominator.InDominanceFrontier block region ctx) :
    dominator.LocallyReachable region ctx := by
  obtain ⟨predecessor, reachable, _, dominance, _⟩ := frontier.exists_predecessor
  rcases dominance with rfl | dominance
  · exact reachable
  · exact dominance.locallyReachable_dominator_of_locallyReachable_dominated reachable

/-- A frontier block is reachable in the region. -/
@[grind →]
theorem locallyReachable_frontier
    (frontier : dominator.InDominanceFrontier block region ctx) :
    block.LocallyReachable region ctx :=
  frontier.2.1

end BlockPtr.InDominanceFrontier

/-! ## Iterated dominance frontiers -/

/--
`block` belongs to the iterated dominance frontier of `definingBlocks` in one SSA
region when a nonempty path of frontier steps reaches it from a defining block.
The seed predicate may contain arbitrary blocks; every frontier step restricts
its endpoints to the reachable CFG of `region`.
-/
def BlockPtr.InIteratedDominanceFrontier (block : BlockPtr)
    (definingBlocks : BlockPtr → Prop) (region : RegionPtr) (ctx : WfIRContext OpInfo) : Prop :=
  ∃ definingBlock, definingBlocks definingBlock ∧
    Relation.TransGen (fun source target => source.InDominanceFrontier target region ctx)
      definingBlock block

namespace BlockPtr.InIteratedDominanceFrontier

variable {definingBlocks candidates : BlockPtr → Prop}

/-- One frontier step from a defining block establishes iterated-frontier membership. -/
theorem of_frontier (definition : definingBlocks dominator)
    (frontier : dominator.InDominanceFrontier block region ctx) :
    block.InIteratedDominanceFrontier definingBlocks region ctx :=
  ⟨dominator, definition, .single frontier⟩

/-- Iterated-frontier membership is closed under another frontier step. -/
theorem of_frontier_step
    (iterated : block₁.InIteratedDominanceFrontier definingBlocks region ctx)
    (frontier : block₁.InDominanceFrontier block₂ region ctx) :
    block₂.InIteratedDominanceFrontier definingBlocks region ctx := by
  obtain ⟨definingBlock, definition, path⟩ := iterated
  exact ⟨definingBlock, definition, .tail path frontier⟩

/-- The iterated frontier is contained in every frontier-closed set containing the seeds' frontiers. -/
theorem least
    (initial : ∀ {source target}, definingBlocks source →
      source.InDominanceFrontier target region ctx → candidates target)
    (closed : ∀ {source target}, candidates source →
      source.InDominanceFrontier target region ctx → candidates target)
    (iterated : block.InIteratedDominanceFrontier definingBlocks region ctx) :
    candidates block := by
  obtain ⟨definingBlock, definition, path⟩ := iterated
  induction path with
  | single frontier => exact initial definition frontier
  | tail _ frontier ih => exact closed ih frontier

/-- Every iterated-frontier block is reachable in the region. -/
@[grind →]
theorem locallyReachable
    (iterated : block.InIteratedDominanceFrontier definingBlocks region ctx) :
    block.LocallyReachable region ctx := by
  apply iterated.least <;> grind

end BlockPtr.InIteratedDominanceFrontier

end Veir
