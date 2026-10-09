module

public import Veir.Dominance.Basic
public import Veir.Interfaces.RegionKindInterfaces

import all Veir.Dominance.Basic

/-!
# Operation Dominance and Reachability Lemmas

General lemmas about operation reachability, operation dominance, and operation/value
dominance at points before and after operations. These do not require `WfIRContext.Dom`.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}
variable {op op₁ op₂ : OperationPtr}
variable {root : IRNode} {region : RegionPtr} {block : BlockPtr}

/-! ## Operation dominance -/

/--
  An operation `op₁` properly dominates an operation `op₂` if it dominates it
  and the operations are not equal.
-/
theorem OperationPtr.properlyDominates_iff_dominates_of_ne (hne : op₁ ≠ op₂) :
    op₁.ProperlyDominates op₂ ctx enclosingOk ↔ op₁.Dominates op₂ ctx enclosingOk := by
  grind [OperationPtr.Dominates]

grind_pattern OperationPtr.properlyDominates_iff_dominates_of_ne =>
    op₁.ProperlyDominates op₂ ctx enclosingOk where
  guard op₁ ≠ op₂

/--
An operation `op₁` dominates an operation `op₂` if it properly dominates it.
-/
@[grind →]
theorem OperationPtr.dominates_of_properlyDominates :
    op₁.ProperlyDominates op₂ ctx enclosingOk → op₁.Dominates op₂ ctx enclosingOk := by
  grind [OperationPtr.Dominates]

/--
An operation dominates itself.
-/
@[grind .]
theorem OperationPtr.dominates_refl : op.Dominates op ctx enclosingOk := by
  grind [OperationPtr.Dominates]

/--
An operation `op₁` dominates an operation `op₂` if and only if
`op₁` properly dominates `op₂` or if `op₁` is `op₂`.
-/
theorem OperationPtr.dominates_iff_properlyDominates_or_eq :
    op₁.Dominates op₂ ctx enclosingOk ↔
      op₁.ProperlyDominates op₂ ctx enclosingOk ∨ op₁ = op₂ := by
  grind [OperationPtr.Dominates]

/-- Proper dominance excluding enclosing operations witnesses a parent region for the dominator. -/
theorem OperationPtr.ProperlyDominates.exists_parentRegion
    (dominance : op₁.ProperlyDominates op₂ ctx false) :
    ∃ region, op₁.getParentRegion! ctx.raw = some region := by
  cases dominance with
  | AncestorDominatedInRegion hAncestor dominance =>
    cases dominance with
    | SameBlock dominance =>
      cases dominance <;>
        grind [OperationPtr.ProperlyDominatesInSSACFGBlock,
          OperationPtr.ProperlyDominatesInGraphBlock]
    | BlockDominance hDominatorBlock hDominatedBlock dominance =>
      cases dominance <;>
        grind [BlockPtr.ProperlyDominatesInSSACFGRegion,
          BlockPtr.ProperlyDominatesInGraphRegion]

/-- A dominator excluding enclosing operations has a parent region when its dominated operation does. -/
theorem OperationPtr.Dominates.exists_parentRegion
    (dominance : op₁.Dominates op₂ ctx false)
    (dominatedParent : op₂.getParentRegion! ctx.raw = some region) :
    ∃ region, op₁.getParentRegion! ctx.raw = some region := by
  rcases dominance with hEq | dominance
  · grind
  · grind [dominance.exists_parentRegion]

/-! ## Operation reachability -/

/-- Local reachability identifies an operation's parent region. -/
theorem OperationPtr.LocallyReachable.parentRegion
    (reachable : op.LocallyReachable region ctx) :
    op.getParentRegion! ctx.raw = some region := by
  grind [OperationPtr.LocallyReachable]

grind_pattern OperationPtr.LocallyReachable.parentRegion => op.LocallyReachable region ctx

/-- A dominator of a hierarchically reachable operation is hierarchically reachable. -/
@[grind →]
axiom OperationPtr.HierarchicallyReachable.of_dominates :
    op₁.HierarchicallyReachable ctx →
    op₂.Dominates op₁ ctx enclosingOk →
    op₂.HierarchicallyReachable ctx

/-- A hierarchically reachable operation is locally reachable in some parent region. -/
@[grind .]
axiom OperationPtr.HierarchicallyReachable.exists_locallyReachable :
  op.HierarchicallyReachable ctx →
  op.getParentRegion! ctx.raw = some region →
  ∃ region, op.LocallyReachable region ctx

/-- A hierarchically reachable operation has a hierarchically reachable parent block. -/
@[grind .]
axiom OperationPtr.HierarchicallyReachable.exists_parent :
  op.HierarchicallyReachable ctx →
  ∃ (block : BlockPtr),
    (op.get! ctx.raw).parent = some block ∧
    block.HierarchicallyReachable ctx

/-- An operation enclosing a hierarchically reachable block is hierarchically reachable. -/
axiom OperationPtr.HierarchicallyReachable.of_ancestor_block
    (reachable : block.HierarchicallyReachable ctx) (ancestry : op.Ancestor block ctx) :
    op.HierarchicallyReachable ctx

/-- An operation dominating the entry of a hierarchically reachable block in an SSA region
is itself hierarchically reachable. -/
@[grind →]
axiom OperationPtr.HierarchicallyReachable.of_dominatesIp_atStart
    (blockInBounds : block.InBounds ctx.raw)
    (blockParent : (block.get! ctx.raw).parent = some region)
    (regionSSA : region.hasSSADominance ctx)
    (reachable : block.HierarchicallyReachable ctx)
    (dominance : op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx) :
    op.HierarchicallyReachable ctx

/-! ## Dominance and rootedness -/

/--
Proper dominance between operations is transitive when the final operation is reachable: its
chain of enclosing nodes ends at a root, and every enclosing block of an SSACFG region is
reachable from the region entry.
-/
axiom OperationPtr.ProperlyDominates.trans_of_reachable {op₃ : OperationPtr}
    (rooted : ∃ root, IRNode.RootedAt op₃ root ctx)
    (reachable : ∀ block region, (IRNode.block block).Ancestor op₃ ctx →
      (block.get! ctx.raw).parent = some region → region.hasSSADominance ctx = true →
      block.LocallyReachable region ctx) :
    op₁.ProperlyDominates op₂ ctx true →
    op₂.ProperlyDominates op₃ ctx true →
    op₁.ProperlyDominates op₃ ctx true

/--
If an operation `op₁` dominates an operation `op₂`, it dominates the operation after `op₂`,
if it exists.
-/
axiom OperationPtr.dominates_next :
  op₁.Dominates op₂ ctx enclosingOk →
  (op₂.get! ctx.raw).next = some op₂Next →
  op₁.Dominates op₂Next ctx enclosingOk

/-- A dominator is rooted at the same root as the operation it dominates. -/
@[grind →]
axiom OperationPtr.RootedAt.of_dominated
    (op₂Rooted : op₂.RootedAt root ctx) (hDom : op₁.Dominates op₂ ctx enclosingOk) :
    op₁.RootedAt root ctx

/-- A rooted operation in an SSA region cannot properly dominate itself with
`enclosingOk = false`, even if it is unreachable. -/
axiom OperationPtr.not_properlyDominates_self {op : OperationPtr}
    (opRooted : op.RootedAt root ctx)
    (opRegion : op.getParentRegion! ctx.raw = some region)
    (opRegionSSA : region.hasSSADominance ctx) :
    ¬ op.ProperlyDominates op ctx false

/-- If a rooted operation dominates a hierarchically reachable operation in an SSA region,
the dominated operation cannot properly dominate it with `enclosingOk = false`. -/
axiom OperationPtr.not_properlyDominates_reverse_of_dominates
    (op₁In : op₁.RootedAt root ctx) (op₂Reachable : op₂.HierarchicallyReachable ctx)
    (op₂ParentRegion : op₂.getParentRegion! ctx.raw = some region₂)
    (op₂RegionSSA : region₂.hasSSADominance ctx) :
    op₁.Dominates op₂ ctx enclosingOk →
    ¬ op₂.ProperlyDominates op₁ ctx false

grind_pattern OperationPtr.not_properlyDominates_reverse_of_dominates =>
    op₁.RootedAt root ctx, op₂.HierarchicallyReachable ctx,
    op₂.getParentRegion! ctx.raw, region₂.hasSSADominance ctx,
    op₁.Dominates op₂ ctx enclosingOk where
  guard op₂.getParentRegion! ctx.raw = some region₂

/-- A hierarchically reachable operation dominated by an operation rooted at `root`
is rooted at that same `root`. -/
axiom OperationPtr.RootedAt.of_dominator {dominator dominated : OperationPtr} :
    dominator.RootedAt root ctx →
    dominator.Dominates dominated ctx enclosingOk →
    dominated.HierarchicallyReachable ctx →
    dominated.RootedAt root ctx

grind_pattern OperationPtr.RootedAt.of_dominator =>
  dominator.RootedAt root ctx, dominator.Dominates dominated ctx enclosingOk,
  dominated.HierarchicallyReachable ctx

/-! ## Dominance at operation insertion points -/

/-- Dominating a block while excluding enclosing operations witnesses a parent region. -/
theorem OperationPtr.ProperlyDominatesBlock.exists_parentRegion
    (dominance : op.ProperlyDominatesBlock block ctx false) :
    ∃ region, op.getParentRegion! ctx.raw = some region := by
  cases dominance with
  | SameRegion dominatorParent dominance =>
    cases dominance <;>
      grind [BlockPtr.ProperlyDominatesInSSACFGRegion,
        BlockPtr.ProperlyDominatesInGraphRegion]
  | AncestorOpDominated ancestry dominance =>
    exact dominance.exists_parentRegion

/-- A dominator excluding enclosing operations has a parent region when the insertion point does. -/
theorem OperationPtr.DominatesIp.exists_parentRegion {ip : InsertPoint}
    (dominance : op.DominatesIp ip ctx false)
    (ipParent : ip.block! ctx.raw = some block)
    (blockParent : (block.get! ctx.raw).parent = some region) :
    ∃ region, op.getParentRegion! ctx.raw = some region := by
  cases dominance with
  | Before dominance => exact dominance.exists_parentRegion
  | AtEndSameBlock dominatorParent => grind
  | AtEndOtherBlock dominance => exact dominance.exists_parentRegion

/-- An operation dominates the point after another operation exactly when it dominates
that operation. -/
axiom OperationPtr.DominatesIp.after_iff :
    op₁.DominatesIp (InsertPoint.after op₂ ctx.raw block op₂HasParent op₂InBounds) ctx enclosingOk ↔
    op₁.Dominates op₂ ctx enclosingOk

/-- An operation dominates the point before another operation exactly when it properly
dominates that operation with the same `enclosingOk` flag. -/
@[simp]
theorem OperationPtr.DominatesIp.before_iff :
    op₁.DominatesIp (.before op₂) ctx enclosingOk ↔
      op₁.ProperlyDominates op₂ ctx enclosingOk := by
  constructor
  · rintro ⟨dominance⟩
    grind
  · exact .Before

grind_pattern OperationPtr.DominatesIp.before_iff => op₁.DominatesIp (.before op₂) ctx enclosingOk

/-- A value dominates the point before an operation exactly when it properly dominates its user. -/
axiom ValuePtr.DominatesIp.before_iff {value : ValuePtr} :
    value.DominatesIp (.before op) ctx ↔ value.ProperlyDominates op ctx

/--
A value dominating the program point before an operation `op₁` also dominates the program
point before any operation `op₂` properly dominated by `op₁`.
-/
axiom ValuePtr.DominatesIp.before_of_properlyDominates {value : ValuePtr} :
  value.DominatesIp (InsertPoint.before op₁) ctx → op₁.ProperlyDominates op₂ ctx true →
  value.DominatesIp (InsertPoint.before op₂) ctx

/-- A value dominates the point after an operation exactly when it dominates the point
before the operation or is one of its results. -/
axiom ValuePtr.DominatesIp.after_iff {value : ValuePtr} :
    value.DominatesIp (InsertPoint.after op ctx.raw block blockIsParent opInBounds) ctx ↔
    value.DominatesIp (.before op) ctx ∨ value ∈ op.getResults! ctx.raw

/-- An operation dominating a rooted block's entry has the same root. -/
@[grind →]
axiom OperationPtr.RootedAt.of_dominatesIp_atStart
    (blockRooted : block.RootedAt root ctx)
    (opDom : op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx) :
    op.RootedAt root ctx

end Veir
