module

public import Veir.Dominance.Lemmas.Block

import all Veir.Dominance.Basic

/-!
# Dominance Frontier Lemmas

Membership, reachability, and closure properties of dominance frontiers and
iterated dominance frontiers on the reachable CFG of one SSA region.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo} {region : RegionPtr}
variable {dominator block block₁ block₂ : BlockPtr}

/-! ## Ordinary dominance frontiers -/

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
    block.InDominanceFrontier dominator region ctx :=
  ⟨ssa, reachable, predecessor, predecessorReachable, successor, dominance, notProper⟩

/-- Frontier membership supplies a reachable predecessor witnessing the dominance conditions. -/
theorem exists_predecessor (frontier : block.InDominanceFrontier dominator region ctx) :
    ∃ predecessor : BlockPtr,
      predecessor.LocallyReachable region ctx ∧
      block ∈ predecessor.getSuccessors! ctx.raw ∧
      (dominator = predecessor ∨
        dominator.ProperlyDominatesInSSACFGRegion predecessor region ctx) ∧
      ¬ dominator.ProperlyDominatesInSSACFGRegion block region ctx :=
  frontier.2.2

/-- Frontier membership is restricted to SSA regions. -/
@[grind →]
theorem hasSSADominance (frontier : block.InDominanceFrontier dominator region ctx) :
    region.hasSSADominance ctx = true :=
  frontier.1

/-- The block whose frontier is taken is reachable in the region. -/
@[grind →]
theorem locallyReachable_dominator
    (frontier : block.InDominanceFrontier dominator region ctx) :
    dominator.LocallyReachable region ctx := by
  obtain ⟨predecessor, reachable, _, dominance, _⟩ := frontier.exists_predecessor
  rcases dominance with rfl | dominance
  · exact reachable
  · exact dominance.locallyReachable_dominator_of_locallyReachable_dominated reachable

/-- A frontier block is reachable in the region. -/
@[grind →]
theorem locallyReachable_frontier
    (frontier : block.InDominanceFrontier dominator region ctx) :
    block.LocallyReachable region ctx :=
  frontier.2.1

/-- A reachable block with a self-loop belongs to its own dominance frontier. -/
theorem self_of_successor
    (ssa : region.hasSSADominance ctx = true)
    (reachable : block.LocallyReachable region ctx)
    (successor : block ∈ block.getSuccessors! ctx.raw) :
    block.InDominanceFrontier block region ctx := by
  have notProper : ¬ block.ProperlyDominatesInSSACFGRegion block region ctx := by
    grind [BlockPtr.ProperlyDominatesInSSACFGRegion]
  exact of_predecessor ssa reachable reachable successor (Or.inl rfl) notProper

end BlockPtr.InDominanceFrontier

/-! ## Iterated dominance frontiers -/

namespace BlockPtr.InIteratedDominanceFrontier

variable {definingBlocks candidates : BlockPtr → Prop}

/-- One frontier step from a defining block establishes iterated-frontier membership. -/
theorem of_frontier (definition : definingBlocks dominator)
    (frontier : block.InDominanceFrontier dominator region ctx) :
    block.InIteratedDominanceFrontier definingBlocks region ctx :=
  ⟨dominator, definition, .single frontier⟩

/-- Iterated-frontier membership is closed under another frontier step. -/
theorem of_frontier_step
    (iterated : block₁.InIteratedDominanceFrontier definingBlocks region ctx)
    (frontier : block₂.InDominanceFrontier block₁ region ctx) :
    block₂.InIteratedDominanceFrontier definingBlocks region ctx := by
  obtain ⟨definingBlock, definition, path⟩ := iterated
  exact ⟨definingBlock, definition, .tail path frontier⟩

/-- The iterated frontier is contained in every frontier-closed set containing the seeds' frontiers. -/
theorem least
    (initial : ∀ {source target}, definingBlocks source →
      target.InDominanceFrontier source region ctx → candidates target)
    (closed : ∀ {source target}, candidates source →
      target.InDominanceFrontier source region ctx → candidates target)
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

/-- No defining block can reach the iterated frontier without an initial frontier step. -/
theorem not_of_forall_not_frontier
    (noFrontier : ∀ source target : BlockPtr, definingBlocks source →
      ¬ target.InDominanceFrontier source region ctx) :
    ¬ block.InIteratedDominanceFrontier definingBlocks region ctx := by
  intro iterated
  apply iterated.least (candidates := fun _ => False)
  · exact fun definition frontier => noFrontier _ _ definition frontier
  · exact fun impossible _ => impossible.elim

/-- An empty set of defining blocks has an empty iterated dominance frontier. -/
@[simp]
theorem not_empty :
    ¬ block.InIteratedDominanceFrontier (fun _ => False) region ctx := by
  apply not_of_forall_not_frontier
  exact fun _ _ impossible => impossible.elim

end BlockPtr.InIteratedDominanceFrontier

end Veir
