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

@[grind →]
theorem OperationPtr.ProperlyDominatesInSSARegion.toProperlyDominatesInRegion
    (dominance : op₁.ProperlyDominatesInSSARegion op₂ region ctx) :
    op₁.ProperlyDominatesInRegion op₂ region ctx :=
  dominance.1

@[grind →]
theorem OperationPtr.ProperlyDominatesInSSARegion.hasSSADominance
    (dominance : op₁.ProperlyDominatesInSSARegion op₂ region ctx) :
    region.hasSSADominance ctx = true :=
  dominance.2

/-- SSA operation dominance is either strict order in one block or proper block dominance. -/
theorem OperationPtr.ProperlyDominatesInSSARegion.block_cases
    (dominance : op₁.ProperlyDominatesInSSARegion op₂ region ctx) :
    ∃ block₁ block₂, op₁.getParent! ctx.raw = some block₁ ∧
      op₂.getParent! ctx.raw = some block₂ ∧
      ((block₁ = block₂ ∧ op₁.idxInParent ctx.raw < op₂.idxInParent ctx.raw) ∨
        block₁.ProperlyDominatesInSSACFGRegion block₂ region ctx) := by
  have ssa := dominance.hasSSADominance
  have dominance := dominance.toProperlyDominatesInRegion
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
theorem OperationPtr.ProperlyDominatesInSSARegion.irrefl :
    ¬ op.ProperlyDominatesInSSARegion op region ctx := by
  intro dominance
  obtain ⟨block₁, block₂, parent₁, parent₂, same | dominance⟩ := dominance.block_cases
  · grind
  · have distinct : block₁ ≠ block₂ := dominance.2.2.2.1
    grind

/-- Same-region SSA proper dominance cannot run backwards when the target is locally reachable. -/
theorem OperationPtr.ProperlyDominatesInSSARegion.asymm
    (dominance : op₁.ProperlyDominatesInSSARegion op₂ region ctx)
    (reachable : op₂.LocallyReachable region ctx) :
    ¬ op₂.ProperlyDominatesInSSARegion op₁ region ctx := by
  intro reverse
  obtain ⟨block₁, block₂, parent₁, parent₂, forwardCases⟩ := dominance.block_cases
  obtain ⟨reverseBlock₂, reverseBlock₁, reverseParent₂, reverseParent₁, reverseCases⟩ :=
    reverse.block_cases
  have same₁ : reverseBlock₁ = block₁ := by grind
  have same₂ : reverseBlock₂ = block₂ := by grind
  subst reverseBlock₁ reverseBlock₂
  rcases forwardCases with ⟨same, order⟩ | forward
  · rcases reverseCases with ⟨_, reverseOrder⟩ | ⟨_, _, _, distinct, _⟩ <;> grind
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

/-- Every ancestor operation of a hierarchically reachable operation is hierarchically reachable. -/
theorem OperationPtr.HierarchicallyReachable.of_ancestor
    {ancestor : OperationPtr}
    (reachable : op.HierarchicallyReachable ctx)
    (ancestry : ancestor.Ancestor op ctx) :
    ancestor.HierarchicallyReachable ctx := by
  by_cases same : ancestor = op
  · simpa [same] using reachable
  cases parent : op.getParent! ctx.raw with
  | none =>
    obtain ⟨nodes, path⟩ := ancestry.exists_parentPath
    cases path <;> grind
  | some block =>
    apply OperationPtr.HierarchicallyReachable.of_ancestor_block (reachable.parent_block parent)
    exact (ancestry.toProperAncestor (by simpa using same)).ancestor_of_parent_descendant
      (by grind)

grind_pattern OperationPtr.HierarchicallyReachable.of_ancestor =>
  op.HierarchicallyReachable ctx, (IRNode.operation ancestor).Ancestor op ctx

namespace OperationPtr.ProperlyDominatesInRegion

/-- Regional proper dominance is transitive when the final operation is locally reachable. -/
theorem trans_of_reachable {op₃ : OperationPtr}
    (first : op₁.ProperlyDominatesInRegion op₂ region ctx)
    (second : op₂.ProperlyDominatesInRegion op₃ region ctx)
    (reachable : op₃.LocallyReachable region ctx) :
    op₁.ProperlyDominatesInRegion op₃ region ctx := by
  cases first with
  | @SameBlock firstBlock first =>
    cases second with
    | @SameBlock secondBlock second =>
      cases first <;> cases second
      · exact .SameBlock (block := firstBlock) (.Ssa (by
          grind [OperationPtr.ProperlyDominatesInSSACFGBlock]))
      · grind [OperationPtr.ProperlyDominatesInSSACFGBlock,
          OperationPtr.ProperlyDominatesInGraphBlock]
      · grind [OperationPtr.ProperlyDominatesInSSACFGBlock,
          OperationPtr.ProperlyDominatesInGraphBlock]
      · exact .SameBlock (block := firstBlock) (.Graph (by
          grind [OperationPtr.ProperlyDominatesInGraphBlock]))
    | BlockDominance middleParent targetParent second =>
      cases first <;>
        exact .BlockDominance (by grind [OperationPtr.ProperlyDominatesInSSACFGBlock,
          OperationPtr.ProperlyDominatesInGraphBlock]) targetParent second
  | @BlockDominance firstBlock middleBlock firstParent middleParent first =>
    cases second with
    | @SameBlock secondBlock second =>
      cases second <;>
        exact .BlockDominance firstParent (by grind [OperationPtr.ProperlyDominatesInSSACFGBlock,
          OperationPtr.ProperlyDominatesInGraphBlock]) first
    | @BlockDominance secondBlock targetBlock secondParent targetParent second =>
      exact .BlockDominance firstParent targetParent
        (first.trans_of_reachable (by grind) (by grind [OperationPtr.LocallyReachable]))

/-- A proper ancestor of a regional dominator properly dominates the rooted target. -/
theorem of_properAncestor_dominator {ancestor : OperationPtr}
    (dominance : op₁.ProperlyDominatesInRegion op₂ region ctx)
    (ancestry : (ancestor : IRNode).ProperAncestor op₁ ctx)
    (rooted : op₂.RootedAt root ctx) :
    ancestor.ProperlyDominates op₂ ctx true := by
  have ancestorOfRegion :=
    ancestry.ancestor_of_parentRegion_descendant dominance.parentRegion_dominator
  have regionOfTarget :=
    IRNode.Ancestor.of_getParentRegion!_eq_some dominance.parentRegion_dominated
  refine OperationPtr.ProperlyDominates.Ancestor (ancestorOfRegion.trans regionOfTarget) ?_
  grind

/-- A regional dominator of a hierarchically reachable operation is hierarchically reachable. -/
@[grind →]
theorem hierarchicallyReachable_dominator_of_hierarchicallyReachable_dominated
    (dominance : op₁.ProperlyDominatesInRegion op₂ region ctx)
    (reachable : op₂.HierarchicallyReachable ctx) :
    op₁.HierarchicallyReachable ctx := by
  cases dominance with
  | SameBlock dominance =>
    cases dominance <;> rename_i dominance <;>
      obtain ⟨dominatorParent, dominatedParent, _⟩ := dominance <;>
      exact OperationPtr.HierarchicallyReachable.of_parent_block
        (reachable.parent_block dominatedParent) dominatorParent
  | BlockDominance dominatorParent dominatedParent dominance =>
    exact OperationPtr.HierarchicallyReachable.of_parent_block
      (dominance.hierarchicallyReachable_dominator_of_hierarchicallyReachable_dominated
        (reachable.parent_block dominatedParent)) dominatorParent

end OperationPtr.ProperlyDominatesInRegion

/-- Proper dominance extends to descendants of a rooted dominated operation. -/
theorem OperationPtr.ProperlyDominates.of_ancestor_dominated {op₃ : OperationPtr}
    (dominance : op₁.ProperlyDominates op₂ ctx enclosingOk)
    (ancestry : op₂.Ancestor op₃ ctx)
    (rooted : op₃.RootedAt root ctx) :
    op₁.ProperlyDominates op₃ ctx enclosingOk := by
  cases dominance with
  | Ancestor dominatorAncestry distinct =>
    refine OperationPtr.ProperlyDominates.Ancestor (dominatorAncestry.trans ancestry) ?_
    grind
  | AncestorDominatedInRegion targetAncestry localDominance enclosingOk =>
    exact .AncestorDominatedInRegion (targetAncestry.trans ancestry) localDominance enclosingOk

/-- A dominator of a hierarchically reachable operation is hierarchically reachable. -/
@[grind →]
theorem OperationPtr.HierarchicallyReachable.of_dominates :
    op₁.HierarchicallyReachable ctx →
    op₂.Dominates op₁ ctx enclosingOk →
    op₂.HierarchicallyReachable ctx := by
  intro reachable dominance
  rcases dominance with same | dominance
  · simpa [same] using reachable
  · cases dominance with
    | Ancestor ancestry _ => exact reachable.of_ancestor ancestry
    | AncestorDominatedInRegion ancestry dominance =>
      exact dominance.hierarchicallyReachable_dominator_of_hierarchicallyReachable_dominated
        (reachable.of_ancestor ancestry)

/-- A dominator of a hierarchically reachable block is hierarchically reachable. -/
@[grind →]
theorem OperationPtr.HierarchicallyReachable.of_properlyDominatesBlock
    (reachable : block.HierarchicallyReachable ctx)
    (dominance : op.ProperlyDominatesBlock block ctx enclosingOk) :
    op.HierarchicallyReachable ctx := by
  cases dominance with
  | Ancestor ancestry => exact OperationPtr.HierarchicallyReachable.of_ancestor_block reachable ancestry
  | SameRegion parent dominance =>
    exact OperationPtr.HierarchicallyReachable.of_parent_block
      (dominance.hierarchicallyReachable_dominator_of_hierarchicallyReachable_dominated
        reachable) parent
  | AncestorOpDominated ancestry dominance =>
    exact (OperationPtr.HierarchicallyReachable.of_ancestor_block reachable ancestry).of_dominates
      (OperationPtr.dominates_of_properlyDominates dominance)

/-- An operation dominating the entry of a hierarchically reachable block in an SSA region
is itself hierarchically reachable. -/
@[grind →]
theorem OperationPtr.HierarchicallyReachable.of_dominatesIp_atStart
    (blockParent : block.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (reachable : block.HierarchicallyReachable ctx)
    (dominance : op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx) :
    op.HierarchicallyReachable ctx := by
  exact OperationPtr.HierarchicallyReachable.of_properlyDominatesBlock reachable
    (dominance.properlyDominatesBlock_of_atStart blockParent regionSSA)

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
chain of enclosing nodes ends at a root, and every enclosing block is
reachable from the region entry.
-/
theorem OperationPtr.ProperlyDominates.trans_of_reachable {op₃ : OperationPtr}
    (rooted : ∃ root, IRNode.RootedAt op₃ root ctx)
    (reachable : op₃.HierarchicallyReachable ctx) :
    op₁.ProperlyDominates op₂ ctx true →
    op₂.ProperlyDominates op₃ ctx true →
    op₁.ProperlyDominates op₃ ctx true := by
  obtain ⟨root, rooted⟩ := rooted
  intro first second
  cases second with
  | Ancestor ancestry _ =>
    exact first.of_ancestor_dominated ancestry rooted
  | @AncestorDominatedInRegion target region targetAncestry localSecond enclosingOk =>
    have targetRooted := rooted.of_ancestor targetAncestry
    cases first with
    | Ancestor ancestry distinct =>
      exact (localSecond.of_properAncestor_dominator
        (ancestry.toProperAncestor (by simpa using distinct)) targetRooted).of_ancestor_dominated
        targetAncestry rooted
    | @AncestorDominatedInRegion middle middleRegion middleAncestry localFirst _ =>
      by_cases same : middle = op₂
      · subst middle
        have sameRegion : middleRegion = region := by grind
        subst middleRegion
        have composed := localFirst.trans_of_reachable localSecond
          (by grind)
        exact .AncestorDominatedInRegion targetAncestry composed true
      · have middleOfRegion :=
          (middleAncestry.toProperAncestor (by simpa using same)).ancestor_of_parentRegion_descendant
            localSecond.parentRegion_dominator
        have regionOfTarget :=
          IRNode.Ancestor.of_getParentRegion!_eq_some localSecond.parentRegion_dominated
        exact .AncestorDominatedInRegion
          ((middleOfRegion.trans regionOfTarget).trans targetAncestry) localFirst true

/--
Proper dominance in a region is preserved when advancing the dominated operation to its next
operation in the same block.
-/
theorem OperationPtr.ProperlyDominatesInRegion.next {nextOp : OperationPtr}
    (dominance : op₁.ProperlyDominatesInRegion op₂ region ctx)
    (next : op₂.getNextOp! ctx.raw = some nextOp) :
    op₁.ProperlyDominatesInRegion nextOp region ctx := by
  obtain ⟨parent, opParent, blockParent⟩ :=
    OperationPtr.getParentRegion!_eq_some_iff.mp dominance.parentRegion_dominated
  obtain ⟨array, chain⟩ := ctx.wellFormed.opChain parent (by grind)
  have nextParent := chain.parent!_nextOp_eq (by grind) opParent next
  cases dominance with
  | SameBlock dominance =>
    cases dominance with
    | Ssa dominance =>
      have nextIndex := OperationPtr.idxInParent_next_eq op₂ ctx.raw nextOp next
        (by grind) (by grind) ctx.wellFormed
      exact .SameBlock (block := parent)
        (.Ssa (by grind [OperationPtr.ProperlyDominatesInSSACFGBlock]))
    | Graph dominance =>
      exact .SameBlock (block := parent)
        (.Graph (by grind [OperationPtr.ProperlyDominatesInGraphBlock]))
  | BlockDominance dominatorParent dominatedParent dominance =>
    exact .BlockDominance dominatorParent (by grind) dominance

grind_pattern OperationPtr.ProperlyDominatesInRegion.next =>
    op₁.ProperlyDominatesInRegion op₂ region ctx,
    op₂.getNextOp! ctx.raw, some nextOp where
  guard op₂.getNextOp! ctx.raw = some nextOp

/-- An operation properly dominates its next operation. -/
theorem OperationPtr.properlyDominates_of_next {nextOp : OperationPtr}
    (parentRegion : op.getParentRegion! ctx.raw = some region)
    (next : op.getNextOp! ctx.raw = some nextOp) :
    op.ProperlyDominates nextOp ctx enclosingOk := by
  obtain ⟨parent, opParent, blockParent⟩ :=
    OperationPtr.getParentRegion!_eq_some_iff.mp parentRegion
  obtain ⟨array, chain⟩ := ctx.wellFormed.opChain parent (by grind)
  have nextParent := chain.parent!_nextOp_eq (by grind) opParent next
  have nextIndex := OperationPtr.idxInParent_next_eq op ctx.raw nextOp next
    (by grind) (by grind) ctx.wellFormed
  apply OperationPtr.ProperlyDominates.AncestorDominatedInRegion .refl (region := region)
  apply OperationPtr.ProperlyDominatesInRegion.SameBlock (block := parent)
  cases regionSSA : region.hasSSADominance ctx with
  | false => exact .Graph (by grind [OperationPtr.ProperlyDominatesInGraphBlock])
  | true => exact .Ssa (by grind [OperationPtr.ProperlyDominatesInSSACFGBlock])

grind_pattern OperationPtr.properlyDominates_of_next =>
  op.ProperlyDominates nextOp ctx enclosingOk, op.getParentRegion! ctx.raw, some region,
  op.getNextOp! ctx.raw, some nextOp where
  guard op.getParentRegion! ctx.raw = some region
  guard op.getNextOp! ctx.raw = some nextOp

/--
If an operation `op₁` dominates an operation `op₂` in a region, it dominates the operation after
`op₂`, if it exists.
-/
theorem OperationPtr.dominates_next
    (parentRegion : op₂.getParentRegion! ctx.raw = some region) :
    op₁.Dominates op₂ ctx enclosingOk →
    op₂.getNextOp! ctx.raw = some op₂Next →
    op₁.Dominates op₂Next ctx enclosingOk := by
  intro dominance next
  obtain ⟨parent, opParent, blockParent⟩ :=
    OperationPtr.getParentRegion!_eq_some_iff.mp parentRegion
  obtain ⟨array, chain⟩ := ctx.wellFormed.opChain parent (by grind)
  have nextParent := chain.parent!_nextOp_eq (by grind) opParent next
  rcases dominance with rfl | dominance
  · exact Or.inr (OperationPtr.properlyDominates_of_next parentRegion next)
  · cases dominance with
    | Ancestor ancestry distinct =>
      by_cases same : op₁ = op₂Next
      · exact Or.inl same
      · exact Or.inr (.Ancestor
          (IRNode.Ancestor.of_same_parent_of_properAncestor (parent := .block parent)
            (ancestry.toProperAncestor (by simpa using distinct)) (by grind) (by grind)) same)
    | @AncestorDominatedInRegion ancestor localRegion ancestry localDominance enclosingOk =>
      by_cases same : ancestor = op₂
      · subst ancestor
        exact Or.inr (.AncestorDominatedInRegion .refl (localDominance.next next) enclosingOk)
      · exact Or.inr (.AncestorDominatedInRegion
          (IRNode.Ancestor.of_same_parent_of_properAncestor (parent := .block parent)
            (ancestry.toProperAncestor (by simpa using same)) (by grind) (by grind))
          localDominance enclosingOk)

grind_pattern OperationPtr.dominates_next =>
    op₁.Dominates op₂ ctx enclosingOk,
    op₂.getParentRegion! ctx.raw, some region,
    op₂.getNextOp! ctx.raw, some op₂Next where
  guard op₂.getParentRegion! ctx.raw = some region
  guard op₂.getNextOp! ctx.raw = some op₂Next

/-- Dominance excluding enclosing operations becomes proper at the next operation. -/
theorem OperationPtr.Dominates.properlyDominates_next {nextOp : OperationPtr}
    (dominance : op₁.Dominates op₂ ctx false)
    (parentRegion : op₂.getParentRegion! ctx.raw = some region)
    (next : op₂.getNextOp! ctx.raw = some nextOp) :
    op₁.ProperlyDominates nextOp ctx false := by
  obtain ⟨parent, opParent, blockParent⟩ :=
    OperationPtr.getParentRegion!_eq_some_iff.mp parentRegion
  obtain ⟨array, chain⟩ := ctx.wellFormed.opChain parent (by grind)
  have nextParent := chain.parent!_nextOp_eq (by grind) opParent next
  rcases dominance with rfl | dominance
  · exact OperationPtr.properlyDominates_of_next parentRegion next
  · cases dominance with | @AncestorDominatedInRegion ancestor localRegion ancestry dominance _ =>
      by_cases same : ancestor = op₂
      · subst ancestor
        exact .AncestorDominatedInRegion .refl (dominance.next next) false
      · exact .AncestorDominatedInRegion
          (IRNode.Ancestor.of_same_parent_of_properAncestor (parent := .block parent)
            (ancestry.toProperAncestor (by simpa using same)) (by grind) (by grind)) dominance false

grind_pattern OperationPtr.Dominates.properlyDominates_next =>
  op₁.Dominates op₂ ctx false, op₂.getParentRegion! ctx.raw, some region,
  op₂.getNextOp! ctx.raw, some nextOp where
  guard op₂.getParentRegion! ctx.raw = some region
  guard op₂.getNextOp! ctx.raw = some nextOp

/-- A dominator of a rooted operation properly dominates its next operation. -/
theorem OperationPtr.Dominates.properlyDominates_next_of_rooted {nextOp : OperationPtr}
    (dominance : op₁.Dominates op₂ ctx enclosingOk)
    (rooted : op₂.RootedAt root ctx)
    (parentRegion : op₂.getParentRegion! ctx.raw = some region)
    (next : op₂.getNextOp! ctx.raw = some nextOp) :
    op₁.ProperlyDominates nextOp ctx enclosingOk := by
  obtain ⟨parent, opParent, blockParent⟩ :=
    OperationPtr.getParentRegion!_eq_some_iff.mp parentRegion
  obtain ⟨array, chain⟩ := ctx.wellFormed.opChain parent (by grind)
  have nextParent := chain.parent!_nextOp_eq (by grind) opParent next
  rcases dominance with rfl | dominance
  · exact OperationPtr.properlyDominates_of_next parentRegion next
  · cases dominance with
    | Ancestor ancestry distinct =>
      have distinctNext : op₁ ≠ nextOp := by
        grind [OperationPtr.Ancestor.eq_of_parentRegion_ancestor,
          IRNode.Ancestor.of_getParentRegion!_eq_some]
      exact .Ancestor
        (IRNode.Ancestor.of_same_parent_of_properAncestor (parent := .block parent)
          (ancestry.toProperAncestor (by simpa using distinct)) (by grind) (by grind)) distinctNext
    | AncestorDominatedInRegion ancestry dominance enclosingOk =>
      have proper := OperationPtr.Dominates.properlyDominates_next
        (Or.inr (.AncestorDominatedInRegion ancestry dominance false)) parentRegion next
      cases proper with | AncestorDominatedInRegion ancestry dominance _ =>
        exact .AncestorDominatedInRegion ancestry dominance enclosingOk

grind_pattern OperationPtr.Dominates.properlyDominates_next_of_rooted =>
  op₁.Dominates op₂ ctx enclosingOk, op₂.RootedAt root ctx,
  op₂.getParentRegion! ctx.raw, some region, op₂.getNextOp! ctx.raw, some nextOp where
  guard op₂.getParentRegion! ctx.raw = some region
  guard op₂.getNextOp! ctx.raw = some nextOp

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
    exact OperationPtr.ProperlyDominatesInSSARegion.irrefl ⟨localDominance, opRegionSSA⟩

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
      exact OperationPtr.ProperlyDominatesInSSARegion.irrefl ⟨localDominance, op₂RegionSSA⟩
    · obtain ⟨reachableRegion, localReachable⟩ :=
        OperationPtr.HierarchicallyReachable.exists_locallyReachable op₂Reachable op₂ParentRegion
      have sameRegion : reachableRegion = region₂ :=
        Option.some.inj (localReachable.parentRegion.symm.trans op₂ParentRegion)
      subst reachableRegion
      have ssaForward : ancestor.ProperlyDominatesInSSARegion op₂ region₂ ctx :=
        ⟨localForward, op₂RegionSSA⟩
      exact ssaForward.asymm localReachable ⟨localDominance, op₂RegionSSA⟩

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

/-- If the target block's region encloses the dominator, its known parent properly dominates
the target block in that region. -/
theorem OperationPtr.ProperlyDominatesBlock.properlyDominatesInRegion_of_ancestor_region
    {parent : BlockPtr}
    (dominance : op.ProperlyDominatesBlock block ctx false)
    (rooted : block.RootedAt root ctx)
    (blockParent : block.getParent! ctx.raw = some region)
    (opParent : op.getParent! ctx.raw = some parent)
    (regionAncestry : region.Ancestor op ctx) :
    parent.ProperlyDominatesInRegion block region ctx := by
  cases dominance with
  | SameRegion _ dominance => grind
  | @AncestorOpDominated _ ancestor ancestry dominance =>
    cases dominance with
    | @AncestorDominatedInRegion middle localRegion middleAncestry localDominance _ =>
      have middleOfRegion :=
        ((middleAncestry.trans ancestry).toProperAncestor (by simp)).ancestor_of_parent_descendant
          (show (IRNode.block block).parent! ctx = some (.region region) by grind)
      have regionRooted : region.RootedAt root ctx :=
        rooted.of_ancestor (IRNode.Ancestor.of_parent (by grind))
      have opRooted := regionAncestry.rootedAt_iff.mp regionRooted
      have same := OperationPtr.Ancestor.eq_of_parentRegion_ancestor
        (middleOfRegion.trans regionAncestry) opRooted localDominance.parentRegion_dominator
        (IRNode.Ancestor.of_getParentRegion!_eq_some localDominance.parentRegion_dominated)
      subst middle
      cases (middleOfRegion.antisymm_of_rooted regionAncestry regionRooted)

grind_pattern OperationPtr.ProperlyDominatesBlock.properlyDominatesInRegion_of_ancestor_region =>
  op.ProperlyDominatesBlock block ctx false, block.RootedAt root ctx,
  op.getParent! ctx.raw, some parent, block.getParent! ctx.raw, some region,
  (IRNode.region region).Ancestor op ctx where
  guard op.getParent! ctx.raw = some parent
  guard block.getParent! ctx.raw = some region

/-- An argument of a rooted, locally reachable SSA block cannot dominate the point before
an operation that dominates the block entry. Reachability in enclosing regions is not required. -/
@[grind →]
theorem OperationPtr.DominatesIp.not_dominatesIp_before_of_mem_arguments
    (regionSSA : region.hasSSADominance ctx)
    (blockRooted : block.RootedAt root ctx)
    (blockReachable : block.LocallyReachable region ctx)
    (opDom : op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    ¬ value.DominatesIp (.before op) ctx := by
  obtain ⟨index, _, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
  intro valueDominance
  cases valueDominance with | BlockArg argumentInBounds ipParent dominance =>
    rename_i parent
    have opParent : op.getParent! ctx.raw = some parent := by grind
    have blockDominance : block.Dominates parent ctx := by grind
    have regionOfOp : region.Ancestor op ctx :=
      (blockDominance.ancestor_parent (IRNode.ProperAncestor.of_parent
        (show (IRNode.block block).parent! ctx = some (.region region) by grind))).trans
          (IRNode.Ancestor.of_parent (by grind))
    grind

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

/-- In a containing region, an operation dominates the point after a rooted operation exactly
when it dominates that operation. -/
axiom OperationPtr.DominatesIp.after_iff
    (rooted : op₂.RootedAt root ctx)
    (blockParent : block.getParent! ctx.raw = some region) :
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

/-- A value dominates the point before an operation exactly when it is in bounds and
properly dominates its user. -/
theorem ValuePtr.DominatesIp.before_iff {value : ValuePtr} :
    value.DominatesIp (.before op) ctx ↔
      value.InBounds ctx.raw ∧ value.ProperlyDominates op ctx := by
  constructor
  · intro dominance
    cases dominance <;> grind [ValuePtr.ProperlyDominates]
  · rintro ⟨inBounds, dominance⟩
    cases value with
    | opResult result => exact .OpResult (by grind) (.Before dominance)
    | blockArgument argument =>
      obtain ⟨parent, parentEq, dominance⟩ := dominance
      exact .BlockArg (by grind) (by grind) dominance

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
