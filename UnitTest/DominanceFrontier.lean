module

import Veir.Dominance.DominanceFrontier
import Veir.Dominance.Lemmas.Block

/-!
# Dominance Frontier Specification Examples

These proofs check reachability filtering and nonempty frontier paths through
the public specification API, independently of any computed dominance facts.
-/

open Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpInfo} {region : RegionPtr}
variable {dominator block : BlockPtr} {definitions : BlockPtr → Prop}

-- A reachable self-loop gives a self-frontier, even when the block is a seed.
example (ssa : region.hasSSADominance ctx = true)
    (reachable : block.LocallyReachable region ctx)
    (edge : block ∈ block.getSuccessors! ctx.raw) :
    block.InDominanceFrontier block region ctx ∧
      block.InIteratedDominanceFrontier (· = block) region ctx := by
  have notProper : ¬ block.ProperlyDominatesInSSACFGRegion block region ctx := by
    intro dominance
    exact dominance.not_dominated_of_locallyReachable_dominated reachable dominance
  have frontier := BlockPtr.InDominanceFrontier.of_predecessor
    ssa reachable reachable edge (Or.inl rfl) notProper
  exact ⟨frontier, .of_frontier rfl frontier⟩

-- Both endpoints of a frontier step must be reachable.
example (unreachable : ¬ dominator.LocallyReachable region ctx) :
    ¬ dominator.InDominanceFrontier block region ctx := by grind

example (unreachable : ¬ block.LocallyReachable region ctx) :
    ¬ dominator.InDominanceFrontier block region ctx ∧
      ¬ block.InIteratedDominanceFrontier definitions region ctx := by grind

-- An incoming edge from an unreachable predecessor cannot witness membership.
example (unreachable : ∀ predecessor : BlockPtr, block ∈ predecessor.getSuccessors! ctx.raw →
    ¬ predecessor.LocallyReachable region ctx) :
    ¬ dominator.InDominanceFrontier block region ctx := by
  intro frontier
  obtain ⟨predecessor, reachable, edge, _, _⟩ := frontier.exists_predecessor
  exact unreachable predecessor edge reachable

-- This specification deliberately excludes graph regions.
example (graph : region.hasSSADominance ctx = false) :
    ¬ dominator.InDominanceFrontier block region ctx := by grind

-- An empty seed predicate has an empty iterated frontier.
example : ¬ block.InIteratedDominanceFrontier (fun _ => False) region ctx := by
  intro iterated
  exact iterated.least (candidates := fun _ => False)
    (fun impossible _ => impossible.elim) (fun impossible _ => impossible.elim)

-- A seed without any outgoing frontier step is not included by a zero-step path.
example (noFrontier : ∀ target, ¬ block.InDominanceFrontier target region ctx) :
    ¬ block.InIteratedDominanceFrontier (· = block) region ctx := by
  intro iterated
  apply iterated.least (candidates := fun _ => False)
  · intro source target definition frontier
    subst source
    exact noFrontier target frontier
  · exact fun impossible _ => impossible.elim
