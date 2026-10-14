module

public import Veir.Dominance.Basic
public import Veir.Dominance.Lemmas.Path
public import Veir.Dominance.Lemmas.Block
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

/-- Same-region proper dominance identifies the dominator's parent region. -/
@[grind →]
theorem OperationPtr.ProperlyDominatesInRegion.parentRegion_dominator
    (dominance : op₁.ProperlyDominatesInRegion op₂ region ctx) :
    op₁.getParentRegion! ctx.raw = some region := by
  cases dominance with
  | SameBlock dominance =>
    cases dominance <;>
      grind [OperationPtr.ProperlyDominatesInSSACFGBlock,
        OperationPtr.ProperlyDominatesInGraphBlock]
  | BlockDominance _ _ dominance =>
    have parent := dominance.parent_dominator
    grind

/-- Same-region proper dominance identifies the dominated operation's parent region. -/
@[grind →]
theorem OperationPtr.ProperlyDominatesInRegion.parentRegion_dominated
    (dominance : op₁.ProperlyDominatesInRegion op₂ region ctx) :
    op₂.getParentRegion! ctx.raw = some region := by
  cases dominance with
  | SameBlock dominance =>
    cases dominance <;>
      grind [OperationPtr.ProperlyDominatesInSSACFGBlock,
        OperationPtr.ProperlyDominatesInGraphBlock]
  | BlockDominance _ _ dominance =>
    have parent := dominance.parent_dominated
    grind

/-- A proper dominator encloses its target or has a parent region enclosing the target. -/
theorem OperationPtr.ProperlyDominates.ancestor_or_parentRegion
    (dominance : op₁.ProperlyDominates op₂ ctx enclosingOk) :
    op₁.Ancestor op₂ ctx ∨
      ∃ region, op₁.getParentRegion! ctx.raw = some region ∧ region.Ancestor op₂ ctx := by
  cases dominance with
  | Ancestor ancestry _ => exact Or.inl ancestry
  | @AncestorDominatedInRegion ancestor region ancestry dominance enclosingOk =>
    exact Or.inr ⟨region, dominance.parentRegion_dominator,
      (IRNode.Ancestor.of_getParentRegion!_eq_some dominance.parentRegion_dominated).trans ancestry⟩

/-- A dominator's parent region encloses the dominated operation, when that parent exists. -/
theorem OperationPtr.Dominates.parentRegion_ancestor
    (dominance : op₁.Dominates op₂ ctx enclosingOk)
    (parentRegion : op₁.getParentRegion! ctx.raw = some region) :
    region.Ancestor op₂ ctx := by
  rcases dominance with rfl | dominance
  · exact IRNode.Ancestor.of_getParentRegion!_eq_some parentRegion
  · rcases dominance.ancestor_or_parentRegion with ancestry | ⟨otherRegion, otherParent, ancestry⟩
    · exact (IRNode.Ancestor.of_getParentRegion!_eq_some parentRegion).trans ancestry
    · have sameRegion : otherRegion = region := by grind
      subst otherRegion
      exact ancestry

/-- SSA operation dominance is either strict order in one block or proper block dominance. -/
theorem OperationPtr.ProperlyDominatesInRegion.ssa_cases
    (dominance : op₁.ProperlyDominatesInRegion op₂ region ctx)
    (ssa : region.hasSSADominance ctx) :
    ∃ block₁ block₂, ∃ parent₁ : op₁.getParent! ctx.raw = some block₁,
      ∃ parent₂ : op₂.getParent! ctx.raw = some block₂,
      ((block₁ = block₂ ∧ op₁.idxInParent ctx.raw < op₂.idxInParent ctx.raw) ∨
        block₁.ProperlyDominatesInSSACFGRegion block₂ region ctx) := by
  cases dominance with
  | @SameBlock block dominance =>
    cases dominance with
    | Ssa dominance =>
      obtain ⟨parent₁, parent₂, _, _, order⟩ := dominance
      exact ⟨block, block, parent₁, parent₂, Or.inl ⟨rfl, order⟩⟩
    | Graph dominance => grind [OperationPtr.ProperlyDominatesInGraphBlock]
  | @BlockDominance block₁ block₂ parent₁ parent₂ dominance =>
    cases dominance with
    | Ssa dominance => exact ⟨block₁, block₂, parent₁, parent₂, Or.inr dominance⟩
    | Graph dominance => grind [BlockPtr.ProperlyDominatesInGraphRegion]

/-- Same-region SSA proper dominance is irreflexive, independently of reachability. -/
theorem OperationPtr.not_properlyDominatesInRegion_self
    (ssa : region.hasSSADominance ctx) :
    ¬ op.ProperlyDominatesInRegion op region ctx := by
  intro dominance
  obtain ⟨block₁, block₂, parent₁, parent₂, same | dominance⟩ := dominance.ssa_cases ssa
  · grind
  · have distinct : block₁ ≠ block₂ := dominance.2.2.2.1
    grind

/-- Same-region SSA proper dominance cannot run backwards when the target is locally reachable. -/
theorem OperationPtr.ProperlyDominatesInRegion.not_dominated_of_locallyReachable_dominated
    (dominance : op₁.ProperlyDominatesInRegion op₂ region ctx)
    (ssa : region.hasSSADominance ctx)
    (reachable : op₂.LocallyReachable region ctx) :
    ¬ op₂.ProperlyDominatesInRegion op₁ region ctx := by
  intro reverse
  obtain ⟨block₁, block₂, parent₁, parent₂, forwardCases⟩ := dominance.ssa_cases ssa
  obtain ⟨reverseBlock₂, reverseBlock₁, reverseParent₂, reverseParent₁, reverseCases⟩ :=
    reverse.ssa_cases ssa
  have same₁ : reverseBlock₁ = block₁ := by grind
  have same₂ : reverseBlock₂ = block₂ := by grind
  subst reverseBlock₁ reverseBlock₂
  rcases forwardCases with ⟨same, order⟩ | forward
  · rcases reverseCases with ⟨_, reverseOrder⟩ | reverse
    · grind
    · have distinct : block₂ ≠ block₁ := reverse.2.2.2.1
      grind
  · rcases reverseCases with ⟨same, _⟩ | reverse
    · have distinct : block₁ ≠ block₂ := forward.2.2.2.1
      grind
    · obtain ⟨targetBlock, targetParent, _, targetReachable⟩ := reachable
      have same : targetBlock = block₂ := by grind
      subst targetBlock
      exact forward.not_dominated_of_locallyReachable_dominated targetReachable reverse

/-- An operation ancestor dominates its descendant when enclosing operations are allowed. -/
theorem OperationPtr.dominates_of_ancestor
    (ancestry : op₁.Ancestor op₂ ctx) : op₁.Dominates op₂ ctx true := by
  by_cases same : op₁ = op₂
  · exact Or.inl same
  · exact Or.inr (.Ancestor ancestry same)

/-- An enclosing operation of a dominator also dominates the target when enclosure is allowed. -/
theorem OperationPtr.Dominates.of_ancestor_dominator {ancestor : OperationPtr}
    (dominance : op₁.Dominates op₂ ctx enclosingOk)
    (ancestry : ancestor.Ancestor op₁ ctx) : ancestor.Dominates op₂ ctx true := by
  rcases dominance with rfl | dominance
  · exact OperationPtr.dominates_of_ancestor ancestry
  · cases dominance with
    | Ancestor targetAncestry _ =>
      exact OperationPtr.dominates_of_ancestor (ancestry.trans targetAncestry)
    | @AncestorDominatedInRegion target region targetAncestry localDominance enclosingOk =>
      by_cases same : ancestor = op₁
      · subst ancestor
        exact Or.inr (.AncestorDominatedInRegion targetAncestry localDominance true)
      · have ancestorOfRegion :=
          (ancestry.toProperAncestor (by simpa using same)).ancestor_of_parentRegion_descendant
            localDominance.parentRegion_dominator
        have regionOfTarget :=
          (IRNode.Ancestor.of_getParentRegion!_eq_some localDominance.parentRegion_dominated).trans
            targetAncestry
        exact OperationPtr.dominates_of_ancestor (ancestorOfRegion.trans regionOfTarget)

/-- Global dominance between rooted operations in one region reduces to equality or
proper dominance in that region. -/
theorem OperationPtr.Dominates.inRegion
    (dominance : op₁.Dominates op₂ ctx enclosingOk)
    (rooted : op₂.RootedAt root ctx)
    (dominatorParent : op₁.getParentRegion! ctx.raw = some region)
    (dominatedParent : op₂.getParentRegion! ctx.raw = some region) :
    op₁ = op₂ ∨ op₁.ProperlyDominatesInRegion op₂ region ctx := by
  rcases dominance with same | dominance
  · exact Or.inl same
  · cases dominance with
    | Ancestor ancestry _ =>
      exact Or.inl (OperationPtr.Ancestor.eq_of_parentRegion_ancestor ancestry rooted dominatedParent
        (IRNode.Ancestor.of_getParentRegion!_eq_some dominatorParent))
    | @AncestorDominatedInRegion ancestor localRegion ancestry localDominance enclosingOk =>
      have sameRegion : localRegion = region := by
        have parent := localDominance.parentRegion_dominator
        grind
      subst localRegion
      have same : ancestor = op₂ :=
        OperationPtr.Ancestor.eq_of_parentRegion_ancestor ancestry rooted dominatedParent
          (IRNode.Ancestor.of_getParentRegion!_eq_some localDominance.parentRegion_dominated)
      subst ancestor
      exact Or.inr localDominance

/-- Proper dominance excluding enclosing operations witnesses a parent region for the dominator. -/
theorem OperationPtr.ProperlyDominates.exists_parentRegion
    (dominance : op₁.ProperlyDominates op₂ ctx false) :
    ∃ region, op₁.getParentRegion! ctx.raw = some region := by
  cases dominance with
  | AncestorDominatedInRegion _ dominance =>
    exact ⟨_, dominance.parentRegion_dominator⟩

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
theorem OperationPtr.HierarchicallyReachable.exists_locallyReachable :
  op.HierarchicallyReachable ctx →
  op.getParentRegion! ctx.raw = some region →
  ∃ region, op.LocallyReachable region ctx := by
  intro reachable parentRegion
  obtain ⟨block, opParent, blockParent⟩ :=
    OperationPtr.getParentRegion!_eq_some_iff.mp parentRegion
  exact ⟨region, OperationPtr.LocallyReachable.of_parent_block
    ((reachable.parent_block opParent).locallyReachable blockParent) opParent⟩

/-- An operation enclosing a hierarchically reachable block is hierarchically reachable. -/
theorem OperationPtr.HierarchicallyReachable.of_ancestor_block
    (reachable : block.HierarchicallyReachable ctx) (ancestry : op.Ancestor block ctx) :
    op.HierarchicallyReachable ctx := by
  intro parent opParent
  have parentAncestry : (IRNode.block parent).Ancestor op ctx :=
    IRNode.Ancestor.of_parent (by
      simp only [IRNode.parent!_operation, opParent, Option.map_some])
  exact reachable.of_ancestor (parentAncestry.trans ancestry)

/-- An operation dominating the entry of a hierarchically reachable block in an SSA region
is itself hierarchically reachable. -/
@[grind →]
axiom OperationPtr.HierarchicallyReachable.of_dominatesIp_atStart
    (blockInBounds : block.InBounds ctx.raw)
    (blockParent : block.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (reachable : block.HierarchicallyReachable ctx)
    (dominance : op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx) :
    op.HierarchicallyReachable ctx

/-! ## Dominance and rootedness -/

/-- Operations related by same-region dominance share a root. -/
theorem OperationPtr.ProperlyDominatesInRegion.rootedAt_iff
    (dominance : op₁.ProperlyDominatesInRegion op₂ region ctx) :
    op₁.RootedAt root ctx ↔ op₂.RootedAt root ctx := by
  exact IRNode.Ancestor.rootedAt_iff_of_common_ancestor
    (IRNode.Ancestor.of_getParentRegion!_eq_some dominance.parentRegion_dominator)
    (IRNode.Ancestor.of_getParentRegion!_eq_some dominance.parentRegion_dominated)

/-- Operations related by proper dominance share a root, independently of reachability. -/
theorem OperationPtr.ProperlyDominates.rootedAt_iff
    (dominance : op₁.ProperlyDominates op₂ ctx enclosingOk) :
    op₁.RootedAt root ctx ↔ op₂.RootedAt root ctx := by
  rcases dominance.ancestor_or_parentRegion with ancestry | ⟨region, parentRegion, ancestry⟩
  · exact ancestry.rootedAt_iff
  · exact IRNode.Ancestor.rootedAt_iff_of_common_ancestor
      (IRNode.Ancestor.of_getParentRegion!_eq_some parentRegion) ancestry

/-- Operations related by dominance share a root, independently of reachability. -/
theorem OperationPtr.Dominates.rootedAt_iff
    (dominance : op₁.Dominates op₂ ctx enclosingOk) :
    op₁.RootedAt root ctx ↔ op₂.RootedAt root ctx := by
  rcases dominance with rfl | dominance
  · rfl
  · exact dominance.rootedAt_iff

/--
Proper dominance between operations is transitive when the final operation is reachable: its
chain of enclosing nodes ends at a root, and every enclosing block of an SSACFG region is
reachable from the region entry.
-/
axiom OperationPtr.ProperlyDominates.trans_of_reachable {op₃ : OperationPtr}
    (rooted : ∃ root, IRNode.RootedAt op₃ root ctx)
    (reachable : ∀ block region, (IRNode.block block).Ancestor op₃ ctx →
      block.getParent! ctx.raw = some region → region.hasSSADominance ctx = true →
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
  op₂.getNextOp! ctx.raw = some op₂Next →
  op₁.Dominates op₂Next ctx enclosingOk

/-- A dominator is rooted at the same root as the operation it dominates. -/
@[grind →]
theorem OperationPtr.RootedAt.of_dominated
    (op₂Rooted : op₂.RootedAt root ctx) (hDom : op₁.Dominates op₂ ctx enclosingOk) :
    op₁.RootedAt root ctx := by
  exact hDom.rootedAt_iff.mpr op₂Rooted

/-- A rooted operation in an SSA region cannot properly dominate itself with
`enclosingOk = false`, even if it is unreachable. -/
theorem OperationPtr.not_properlyDominates_self {op : OperationPtr}
    (opRooted : op.RootedAt root ctx)
    (opRegion : op.getParentRegion! ctx.raw = some region)
    (opRegionSSA : region.hasSSADominance ctx) :
    ¬ op.ProperlyDominates op ctx false := by
  intro dominance
  cases dominance with
  | @AncestorDominatedInRegion ancestor localRegion ancestry localDominance enclosingOk =>
    have sameRegion : localRegion = region :=
      Option.some.inj (localDominance.parentRegion_dominator.symm.trans opRegion)
    subst localRegion
    have same := OperationPtr.Ancestor.eq_of_parentRegion_ancestor ancestry opRooted opRegion
      (IRNode.Ancestor.of_getParentRegion!_eq_some localDominance.parentRegion_dominated)
    subst ancestor
    exact OperationPtr.not_properlyDominatesInRegion_self opRegionSSA localDominance

/-- If a rooted operation dominates a hierarchically reachable operation in an SSA region,
the dominated operation cannot properly dominate it with `enclosingOk = false`. -/
theorem OperationPtr.not_properlyDominates_reverse_of_dominates
    (op₁In : op₁.RootedAt root ctx) (op₂Reachable : op₂.HierarchicallyReachable ctx)
    (op₂ParentRegion : op₂.getParentRegion! ctx.raw = some region₂)
    (op₂RegionSSA : region₂.hasSSADominance ctx) :
    op₁.Dominates op₂ ctx enclosingOk →
    ¬ op₂.ProperlyDominates op₁ ctx false := by
  intro forward reverse
  have op₂Rooted := forward.rootedAt_iff.mp op₁In
  cases reverse with
  | @AncestorDominatedInRegion ancestor localRegion ancestry localDominance enclosingOk =>
    have sameRegion : localRegion = region₂ :=
      Option.some.inj (localDominance.parentRegion_dominator.symm.trans op₂ParentRegion)
    subst localRegion
    have ancestorDominance := forward.of_ancestor_dominator ancestry
    rcases ancestorDominance.inRegion op₂Rooted localDominance.parentRegion_dominated
        op₂ParentRegion with same | localForward
    · subst ancestor
      exact OperationPtr.not_properlyDominatesInRegion_self op₂RegionSSA localDominance
    · obtain ⟨reachableRegion, localReachable⟩ :=
        OperationPtr.HierarchicallyReachable.exists_locallyReachable op₂Reachable op₂ParentRegion
      have sameRegion : reachableRegion = region₂ :=
        Option.some.inj (localReachable.parentRegion.symm.trans op₂ParentRegion)
      subst reachableRegion
      exact localForward.not_dominated_of_locallyReachable_dominated
        op₂RegionSSA localReachable localDominance

grind_pattern OperationPtr.not_properlyDominates_reverse_of_dominates =>
    op₁.RootedAt root ctx, op₂.HierarchicallyReachable ctx,
    op₂.getParentRegion! ctx.raw, region₂.hasSSADominance ctx,
    op₁.Dominates op₂ ctx enclosingOk where
  guard op₂.getParentRegion! ctx.raw = some region₂

/-- A hierarchically reachable operation dominated by an operation rooted at `root`
is rooted at that same `root`. -/
theorem OperationPtr.RootedAt.of_dominator {dominator dominated : OperationPtr} :
    dominator.RootedAt root ctx →
    dominator.Dominates dominated ctx enclosingOk →
    dominated.HierarchicallyReachable ctx →
    dominated.RootedAt root ctx := by
  intro rooted dominance _
  exact dominance.rootedAt_iff.mp rooted

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
    (blockParent : block.getParent! ctx.raw = some region) :
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
theorem ValuePtr.DominatesIp.before_iff {value : ValuePtr} :
    value.DominatesIp (.before op) ctx ↔ value.ProperlyDominates op ctx := by
  cases value with
  | opResult result =>
    constructor
    · intro dominance
      cases dominance with
      | OpResult dominance => exact OperationPtr.DominatesIp.before_iff.mp dominance
    · intro dominance
      exact .OpResult (.Before dominance)
  | blockArgument argument =>
    constructor
    · intro dominance
      cases dominance with
      | BlockArg parentEq dominance =>
        exact ⟨_, by simpa only [InsertPoint.block!_before_eq] using parentEq, dominance⟩
    · rintro ⟨parent, parentEq, dominance⟩
      exact .BlockArg (by simpa only [InsertPoint.block!_before_eq] using parentEq) dominance

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

/-- An operation properly dominating a rooted block has the same root. -/
theorem OperationPtr.ProperlyDominatesBlock.rootedAt_dominator
    (dominance : op.ProperlyDominatesBlock block ctx enclosingOk)
    (blockRooted : block.RootedAt root ctx) :
    op.RootedAt root ctx := by
  cases dominance with
  | Ancestor ancestry => exact blockRooted.of_ancestor ancestry
  | SameRegion dominatorParent dominance =>
    exact (dominance.rootedAt_iff.mpr blockRooted).of_parent (by grind)
  | AncestorOpDominated ancestry dominance =>
    exact dominance.rootedAt_iff.mpr (blockRooted.of_ancestor ancestry)

/-- An operation dominating an insertion point in a rooted block has the same root. -/
theorem OperationPtr.DominatesIp.rootedAt_dominator {ip : InsertPoint}
    (dominance : op.DominatesIp ip ctx enclosingOk)
    (ipParent : ip.block! ctx.raw = some block)
    (blockRooted : block.RootedAt root ctx) :
    op.RootedAt root ctx := by
  cases dominance with
  | Before dominance =>
    apply dominance.rootedAt_iff.mpr
    exact blockRooted.of_parent (by grind)
  | AtEndSameBlock dominatorParent =>
    simp only [InsertPoint.block!_atEnd_eq, Option.some.injEq] at ipParent
    subst block
    exact blockRooted.of_parent (by grind)
  | AtEndOtherBlock dominance =>
    simp only [InsertPoint.block!_atEnd_eq, Option.some.injEq] at ipParent
    subst block
    exact dominance.rootedAt_dominator blockRooted

/-- An operation dominating a rooted block's entry has the same root. -/
@[grind →]
theorem OperationPtr.RootedAt.of_dominatesIp_atStart
    (blockRooted : block.RootedAt root ctx)
    (opDom : op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx) :
    op.RootedAt root ctx := by
  cases first : block.getFirstOp! ctx.raw with
  | some firstOp =>
    simp only [InsertPoint.atStart!_eq, first] at opDom
    grind [opDom.rootedAt_dominator]
  | none =>
    simp only [InsertPoint.atStart!_eq, first] at opDom
    exact opDom.rootedAt_dominator (by grind) blockRooted

end Veir
