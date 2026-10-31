module

public import Veir.Rewriter.EraseUnreachableBlocks
public import Veir.Dominance.Basic

import all Veir.Rewriter.EraseUnreachableBlocks
import all Veir.Dominance.Basic

/-!
# Soundness of the unreachable block analysis

Every block that `DeadBlockSet.compute!` reports as unreachable is not locally
reachable from the entry of its region (`BlockPtr.LocallyReachable`).

The proof shows that the set returned by `RegionPtr.reachableBlocks` contains
the entry block and is closed under successors, and hence contains every block
at the end of a CFG path from the entry block.
-/

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

namespace RegionPtr.reachableBlocks

/-- `visit` adds every successor to `reached`, and only adds blocks that are also in the worklist. -/
theorem visit_spec {successors worklist : List BlockPtr} {reached : Std.HashSet BlockPtr} :
    (∀ block ∈ reached, block ∈ (visit successors worklist reached).2) ∧
    (∀ block ∈ successors, block ∈ (visit successors worklist reached).2) ∧
    (∀ block ∈ worklist, block ∈ (visit successors worklist reached).1) ∧
    (∀ block ∈ (visit successors worklist reached).2,
      block ∈ reached ∨ block ∈ (visit successors worklist reached).1) ∧
    (∀ block ∈ (visit successors worklist reached).1,
      block ∈ worklist ∨ block ∈ (visit successors worklist reached).2) := by
  induction successors generalizing worklist reached with
  | nil => simp only [visit]; grind
  | cons successor successors ih =>
    simp only [visit]
    split
    · grind
    · have := @ih (successor :: worklist) (reached.insert successor)
      grind

/--
  If every block in `reached` is either in the worklist or has all its
  successors in `reached`, and the worklist is included in `reached`, then the
  result of `loop` includes `reached` and is closed under successors.
-/
theorem loop_spec {ctx : IRContext OpInfo} {fuel : Nat} {worklist : List BlockPtr}
    {reached result : Std.HashSet BlockPtr}
    (h : loop ctx fuel worklist reached = some result)
    (hclosed : ∀ block ∈ reached,
      block ∈ worklist ∨ ∀ successor ∈ block.getSuccessors! ctx, successor ∈ reached)
    (hworklist : ∀ block ∈ worklist, block ∈ reached) :
    (∀ block ∈ reached, block ∈ result) ∧
    ∀ block ∈ result, ∀ successor ∈ block.getSuccessors! ctx, successor ∈ result := by
  induction fuel generalizing worklist reached with
  | zero =>
    cases worklist with
    | nil => simp only [loop, Option.some.injEq] at h; subst h; grind
    | cons => simp [loop] at h
  | succ fuel ih =>
    cases worklist with
    | nil => simp only [loop, Option.some.injEq] at h; subst h; grind
    | cons block worklist =>
      simp only [loop] at h
      have spec := @visit_spec (block.getSuccessors! ctx).toList worklist reached
      simp only [Array.mem_toList_iff] at spec
      have ⟨hincl, hclosed'⟩ := ih h (by grind) (by grind)
      exact ⟨fun block' h' => hincl block' (spec.1 block' h'), hclosed'⟩

end RegionPtr.reachableBlocks

/-- The blocks reachable from the entry of `region` are all in `region.reachableBlocks`. -/
theorem RegionPtr.mem_reachableBlocks_of_locallyReachable {ctx : WfIRContext OpInfo}
    {region : RegionPtr} {block : BlockPtr} {reachable : Std.HashSet BlockPtr}
    (h : region.reachableBlocks ctx.raw = some reachable)
    (hreach : block.LocallyReachable region ctx) :
    block ∈ reachable := by
  unfold BlockPtr.LocallyReachable at hreach
  obtain ⟨entry, blocks, hentry, hpath⟩ := hreach
  simp only [reachableBlocks, hentry] at h
  have ⟨hincl, hclosed⟩ := reachableBlocks.loop_spec h
    (by simp only [Std.HashSet.singleton_eq_insert, Std.HashSet.mem_insert]; grind)
    (by simp only [Std.HashSet.singleton_eq_insert]; grind)
  have hentryIn : entry ∈ reachable := hincl entry (by simp)
  clear hincl hentry h
  induction hpath with
  | Single => exact hentryIn
  | Cons _ successor _ ih => exact ih (hclosed _ hentryIn _ successor)

/-- `collectNested` does not change the unreachable blocks of the accumulator. -/
theorem DeadBlockSet.collectNested_deadBlocks {ctx : IRContext OpInfo} {fuel : Nat}
    {worklist : List IRNode} {acc : DeadBlockSet} :
    (collectNested ctx fuel worklist acc).deadBlocks = acc.deadBlocks := by
  fun_induction collectNested <;> simp_all [panicWithPosWithDecl, panic, panicCore]

/--
  Soundness of the unreachable block analysis: every block reported as
  unreachable is not locally reachable from the entry of its region.
-/
theorem DeadBlockSet.not_locallyReachable_of_mem_deadBlocks {ctx : WfIRContext OpInfo}
    {region : RegionPtr} {block : BlockPtr}
    (hdead : block ∈ (compute! ctx.raw region).deadBlocks) :
    ¬ block.LocallyReachable region ctx := by
  intro hreach
  unfold compute! at hdead
  split at hdead
  · simp [panicWithPosWithDecl, panic, panicCore] at hdead
  · rename_i reachable hreachable
    rw [collectNested_deadBlocks] at hdead
    have := RegionPtr.mem_reachableBlocks_of_locallyReachable hreachable hreach
    grind

end Veir
