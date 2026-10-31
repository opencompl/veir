module

public import Veir.Dominance.Lemmas.Path
public import Veir.Interfaces.RegionKindInterfaces

import all Veir.Dominance.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.InsertPoint

/-!
# Block Dominance Lemmas

Lemmas about block dominance, block reachability, and dominance at block entries and exits.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

namespace BlockPtr.ProperlyDominatesInSSACFGRegion

variable {dominator middle dominated : BlockPtr} {region : RegionPtr}

/-- A proper SSA dominator occurs on every entry-to-target path. -/
theorem mem_of_path
    (dominance : dominator.ProperlyDominatesInSSACFGRegion dominated region ctx)
    (entry : region.getFirstBlock! ctx.raw = some entryBlock)
    (path : region.Path ctx entryBlock dominated blocks) :
    dominator ∈ blocks := by
  obtain ⟨_, _, _, _, everyPath⟩ := dominance
  exact everyPath entryBlock blocks entry path

/-- A proper SSA dominator of a locally reachable block is locally reachable. -/
theorem locallyReachable_dominator_of_locallyReachable_dominated
    (dominance : dominator.ProperlyDominatesInSSACFGRegion dominated region ctx)
    (reachable : dominated.LocallyReachable region ctx) :
    dominator.LocallyReachable region ctx := by
  obtain ⟨entryBlock, blocks, entry, path⟩ := reachable.exists_path
  obtain ⟨_, _, _, prefixPath, _⟩ := path.split_of_mem (dominance.mem_of_path entry path)
  exact BlockPtr.LocallyReachable.of_path entry prefixPath

/-- Proper SSA dominance cannot hold in both directions when the target is locally reachable. -/
theorem not_dominated_of_locallyReachable_dominated
    (dominance : dominator.ProperlyDominatesInSSACFGRegion dominated region ctx)
    (reachable : dominated.LocallyReachable region ctx) :
    ¬ dominated.ProperlyDominatesInSSACFGRegion dominator region ctx := by
  intro reverse
  obtain ⟨entryBlock, blocks, entry, path⟩ := reachable.exists_path
  obtain ⟨pre, post, _, firstPath, _, absent⟩ := path.split_first_of_mem path.target_mem
  obtain ⟨before, after, split, toDominator, fromDominator⟩ :=
    firstPath.split_of_mem (dominance.mem_of_path entry firstPath)
  have inPrefix := reverse.mem_of_path entry toDominator
  have inSuffix := fromDominator.target_mem
  have distinct : dominator ≠ dominated := dominance.2.2.2.1
  -- The first path contains the target once; mutual dominance would put it on both
  -- sides of the split at the distinct dominator.
  have prefixCount := List.count_eq_zero_of_not_mem absent
  have beforeCount := List.count_pos_iff.mpr inPrefix
  have afterCount := List.count_pos_iff.mpr inSuffix
  have countEq := congrArg (List.count dominated) split
  simp only [List.count_append, List.count_cons] at countEq
  simp only [List.count_append, List.count_cons] at beforeCount afterCount
  grind

/-- Proper SSA dominance is transitive when the final block is locally reachable. -/
theorem trans_of_reachable
    (first : dominator.ProperlyDominatesInSSACFGRegion middle region ctx)
    (second : middle.ProperlyDominatesInSSACFGRegion dominated region ctx)
    (reachable : dominated.LocallyReachable region ctx) :
    dominator.ProperlyDominatesInSSACFGRegion dominated region ctx := by
  have distinct : dominator ≠ dominated := by
    intro same
    subst dominated
    exact first.not_dominated_of_locallyReachable_dominated
      (second.locallyReachable_dominator_of_locallyReachable_dominated reachable) second
  refine ⟨first.1, second.2.1, first.2.2.1, distinct, ?_⟩
  intro entryBlock blocks entry path
  obtain ⟨pre, post, split, prefixPath, _⟩ :=
    path.split_of_mem (second.mem_of_path entry path)
  have inPrefix := first.mem_of_path entry prefixPath
  grind

end BlockPtr.ProperlyDominatesInSSACFGRegion

namespace BlockPtr.ProperlyDominatesInRegion

variable {dominator dominated source predecessor successor : BlockPtr} {region : RegionPtr}

/-- Regional proper dominance is transitive when the final block is locally reachable. -/
theorem trans_of_reachable {middle : BlockPtr}
    (first : dominator.ProperlyDominatesInRegion middle region ctx)
    (second : middle.ProperlyDominatesInRegion dominated region ctx)
    (reachable : dominated.LocallyReachable region ctx) :
    dominator.ProperlyDominatesInRegion dominated region ctx := by
  cases first with
  | Ssa first =>
    cases second with
    | Ssa second => exact .Ssa (first.trans_of_reachable second reachable)
    | Graph second => grind [ProperlyDominatesInSSACFGRegion, ProperlyDominatesInGraphRegion]
  | Graph first =>
    cases second with
    | Ssa second => grind [ProperlyDominatesInSSACFGRegion, ProperlyDominatesInGraphRegion]
    | Graph second => exact .Graph (by grind [ProperlyDominatesInGraphRegion])

@[grind →]
theorem parent_dominator :
    dominator.ProperlyDominatesInRegion dominated region ctx →
    dominator.getParent! ctx.raw = region := by
  rintro (_|_)
  · grind [ProperlyDominatesInSSACFGRegion]
  · grind [ProperlyDominatesInGraphRegion]

@[grind →]
theorem parent_dominated :
    dominator.ProperlyDominatesInRegion dominated region ctx →
    dominated.getParent! ctx.raw = region := by
  rintro (_|_)
  · grind [ProperlyDominatesInSSACFGRegion]
  · grind [ProperlyDominatesInGraphRegion]

/-- Blocks related by same-region dominance share a root. -/
theorem rootedAt_iff
    (dominance : dominator.ProperlyDominatesInRegion dominated region ctx) :
    dominator.RootedAt root ctx ↔ dominated.RootedAt root ctx := by
  have dominatorParent := dominance.parent_dominator
  have dominatedParent := dominance.parent_dominated
  exact IRNode.Ancestor.rootedAt_iff_of_common_ancestor
    (ancestor := .region region) (.of_parent (by grind)) (.of_parent (by grind))

/--
If a `source` block properly dominates a distinct `target`, then it properly dominates
a distinct predecessor of that successor edge.
-/
theorem predecessor_of_dominates_successor
    (sourceNeTarget : source ≠ target)
    (successorEdge : successor ∈ target.getSuccessors! ctx.raw)
    (targetParent : target.getParent! ctx.raw = some region)
    (sourceDominatesSuccessor : source.ProperlyDominatesInRegion successor region ctx) :
    source.ProperlyDominatesInRegion target region ctx := by
  have sourceParent : source.getParent! ctx.raw = some region := by grind
  cases sourceDominatesSuccessor with
  | Graph graphDominance =>
    apply Graph
    grind [ProperlyDominatesInGraphRegion]
  | Ssa ssaDominance =>
    apply Ssa
    refine ⟨ssaDominance.1, targetParent, ssaDominance.2.2.1, sourceNeTarget, ?_⟩
    intro entry blocks hfirstBlock hPath
    have extendedPath := hPath.append
      (RegionPtr.Path.of_successor successorEdge targetParent ssaDominance.2.1)
    have inExtendedPath := ssaDominance.mem_of_path hfirstBlock extendedPath
    have sourceNeSuccessor := ssaDominance.2.2.2.1
    simpa [sourceNeSuccessor] using inExtendedPath

end BlockPtr.ProperlyDominatesInRegion

namespace BlockPtr.Dominates

variable {source predecessor successor : BlockPtr} {region : RegionPtr}

/-- Every proper enclosing region of a block dominator encloses the dominated block. -/
@[grind →]
theorem ancestor_parent {target : BlockPtr}
    (dominance : source.Dominates target ctx)
    (regionAncestry : (IRNode.region region).ProperAncestor source ctx) :
    region.Ancestor target ctx := by
  rcases dominance with rfl | dominance
  · exact regionAncestry.toAncestor
  · cases dominance with
    | Ancestor targetAncestry _ => exact regionAncestry.toAncestor.trans targetAncestry
    | AncestorDominatedInRegion ancestor localRegion targetAncestry localDominance =>
      exact (IRNode.Ancestor.of_same_parent_of_properAncestor regionAncestry
        (parent := .region localRegion) (by grind) (by grind)).trans targetAncestry

/-- Dominance between rooted blocks in one region reduces to equality or regional proper dominance. -/
theorem eq_or_properlyDominatesInRegion_of_same_parent_region {target : BlockPtr}
    (dominance : source.Dominates target ctx)
    (rooted : target.RootedAt root ctx)
    (sourceParent : source.getParent! ctx.raw = some region)
    (targetParent : target.getParent! ctx.raw = some region) :
    source = target ∨ source.ProperlyDominatesInRegion target region ctx := by
  rcases dominance with same | dominance
  · exact Or.inl same
  · cases dominance <;> grind

grind_pattern eq_or_properlyDominatesInRegion_of_same_parent_region =>
  source.Dominates target ctx, target.RootedAt root ctx,
  source.getParent! ctx.raw, target.getParent! ctx.raw, some region where
  guard source.getParent! ctx.raw = some region
  guard target.getParent! ctx.raw = some region

/--
If a distinct block dominates a successor, it also dominates the predecessor
of that successor edge.
-/
theorem predecessor_of_dominates_successor
    (predecessorParent :
      predecessor.getParent! ctx.raw = some region)
    (successorParent : successor.getParent! ctx.raw = some region)
    (sourceNeSuccessor : source ≠ successor)
    (successorEdge : successor ∈ predecessor.getSuccessors! ctx.raw)
    (sourceDominatesSuccessor : source.Dominates successor ctx) :
    source.Dominates predecessor ctx := by
  unfold Dominates at sourceDominatesSuccessor ⊢
  rcases sourceDominatesSuccessor with (heq|sourceDominatesSuccessor); grind
  by_cases source = predecessor; grind
  right
  cases sourceDominatesSuccessor with
  | Ancestor ancestry _ =>
    apply ProperlyDominates.Ancestor (hNe := by grind)
    have properAncestry := ancestry.proper_of_ne (by simpa)
    exact IRNode.Ancestor.of_same_parent_of_properAncestor properAncestry
      (parent := .region region) (by grind) (by grind)
  | AncestorDominatedInRegion ancestor localRegion ancestry localDominance =>
    by_cases ancestor = successor
    · subst ancestor
      apply ProperlyDominates.AncestorDominatedInRegion predecessor region .refl
      grind [ProperlyDominatesInRegion.predecessor_of_dominates_successor]
    · have properAncestry := ancestry.proper_of_ne (by grind)
      apply ProperlyDominates.AncestorDominatedInRegion ancestor (h := localDominance)
      exact IRNode.Ancestor.of_same_parent_of_properAncestor (parent := .region region)
        properAncestry (by grind) (by grind)

/-- Block dominance extends to descendants of the dominated block. -/
theorem of_ancestor_dominated {a b c : BlockPtr}
    (dominance : a.Dominates b ctx) (ancestry : b.Ancestor c ctx) :
    a.Dominates c ctx := by
  by_cases same : a = c
  · exact Or.inl same
  apply Or.inr
  rcases dominance with rfl | dominance
  · exact .Ancestor ancestry same
  · cases dominance with
    | Ancestor upper _ => exact .Ancestor (upper.trans ancestry) same
    | AncestorDominatedInRegion ancestor region upper localDominance =>
      exact .AncestorDominatedInRegion ancestor region (upper.trans ancestry) localDominance true

grind_pattern of_ancestor_dominated =>
  a.Dominates b ctx, (IRNode.block b).Ancestor c ctx

/-- Block dominance is transitive when the final block is hierarchically reachable. -/
theorem trans_of_reachable {a b c : BlockPtr}
    (first : a.Dominates b ctx) (second : b.Dominates c ctx)
    (reachable : c.HierarchicallyReachable ctx) : a.Dominates c ctx := by
  rcases first with rfl | first
  · exact second
  rcases second with rfl | second
  · exact Or.inr first
  cases second with
  | Ancestor ancestry _ => exact BlockPtr.Dominates.of_ancestor_dominated (Or.inr first) ancestry
  | AncestorDominatedInRegion target region targetAncestry localSecond =>
    cases first with
    | Ancestor ancestry distinct =>
      have ancestorOfRegion :=
        (ancestry.toProperAncestor (by simpa using distinct)).ancestor_of_parent_descendant
          (show (IRNode.block b).parent! ctx = some (.region region) by grind)
      have regionOfTarget : region.Ancestor target ctx := .of_parent (by grind)
      exact (show a.Dominates a ctx from Or.inl rfl).of_ancestor_dominated
        ((ancestorOfRegion.trans regionOfTarget).trans targetAncestry)
    | AncestorDominatedInRegion middle middleRegion middleAncestry localFirst =>
      by_cases same : middle = b
      · subst middle
        have sameRegion : middleRegion = region := by grind
        subst middleRegion
        exact Or.inr (.AncestorDominatedInRegion target region targetAncestry
          (localFirst.trans_of_reachable localSecond
            ((reachable.of_ancestor targetAncestry).locallyReachable localSecond.parent_dominated)) true)
      · have middleOfRegion :=
          (middleAncestry.toProperAncestor (by simpa using same)).ancestor_of_parent_descendant
            (show (IRNode.block b).parent! ctx = some (.region region) by grind)
        have regionOfTarget : region.Ancestor target ctx := .of_parent (by grind)
        exact Or.inr (.AncestorDominatedInRegion middle middleRegion
          ((middleOfRegion.trans regionOfTarget).trans targetAncestry) localFirst true)

grind_pattern trans_of_reachable =>
  a.Dominates c ctx, a.Dominates b ctx, b.Dominates c ctx, c.HierarchicallyReachable ctx

end BlockPtr.Dominates

/-- Proper regional SSA dominance excludes reverse global dominance of a rooted, reachable target. -/
@[grind →]
theorem BlockPtr.ProperlyDominatesInRegion.not_dominates_reverse
    {source target : BlockPtr} {region : RegionPtr}
    (dominance : source.ProperlyDominatesInRegion target region ctx)
    (ssa : region.hasSSADominance ctx)
    (rooted : target.RootedAt root ctx)
    (reachable : target.LocallyReachable region ctx) :
    ¬ target.Dominates source ctx := by
  cases dominance with
  | Graph dominance => grind [BlockPtr.ProperlyDominatesInGraphRegion]
  | Ssa dominance =>
    intro reverse
    have sourceRooted := (BlockPtr.ProperlyDominatesInRegion.Ssa dominance).rootedAt_iff.mpr rooted
    rcases reverse.eq_or_properlyDominatesInRegion_of_same_parent_region
        sourceRooted dominance.2.1 dominance.1 with same | reverse
    · exact dominance.2.2.2.1 same.symm
    · cases reverse with
      | Ssa reverse => exact dominance.not_dominated_of_locallyReachable_dominated reachable reverse
      | Graph reverse => grind [BlockPtr.ProperlyDominatesInGraphRegion,
          BlockPtr.ProperlyDominatesInSSACFGRegion]

/-! ## Block reachability -/

variable {region : RegionPtr} {block succ : BlockPtr} {op : OperationPtr}
variable {root : IRNode} {value : ValuePtr}

/-- A hierarchically reachable block is locally reachable in some parent region. -/
@[grind .]
theorem BlockPtr.HierarchicallyReachable.exists_locallyReachable {block : BlockPtr} :
  block.HierarchicallyReachable ctx →
  block.getParent! ctx.raw = some region →
  ∃ region, block.LocallyReachable region ctx := by
  intro reachable parent
  exact ⟨region, reachable.locallyReachable parent⟩

/-- A locally reachable block in the same region as a hierarchically reachable block
is hierarchically reachable, since their enclosing blocks coincide. -/
theorem BlockPtr.HierarchicallyReachable.of_same_region {source target : BlockPtr}
    (reachable : target.HierarchicallyReachable ctx)
    (localReachable : source.LocallyReachable region ctx)
    (targetParent : target.getParent! ctx.raw = some region) :
    source.HierarchicallyReachable ctx := by
  intro ancestor ancestry ancestorRegion parent
  by_cases same : ancestor = source
  · subst ancestor
    have regionEq : ancestorRegion = region :=
      Option.some.inj (parent.symm.trans localReachable.parent)
    subst ancestorRegion
    exact localReachable
  · have targetAncestry := IRNode.Ancestor.of_same_parent_of_properAncestor
      (ancestry.toProperAncestor (by simpa using same))
      (show (IRNode.block source).parent! ctx = some (.region region) by
        simp only [IRNode.parent!_block, localReachable.parent, Option.map_some])
      (show (IRNode.block target).parent! ctx = some (.region region) by
        simp only [IRNode.parent!_block, targetParent, Option.map_some])
    exact reachable ancestor targetAncestry ancestorRegion parent

/-- A proper SSA dominator of a hierarchically reachable block is hierarchically reachable. -/
theorem BlockPtr.ProperlyDominatesInSSACFGRegion.hierarchicallyReachable_dominator_of_hierarchicallyReachable_dominated
    {dominator dominated : BlockPtr}
    (dominance : dominator.ProperlyDominatesInSSACFGRegion dominated region ctx)
    (reachable : dominated.HierarchicallyReachable ctx) :
    dominator.HierarchicallyReachable ctx := by
  have localReachable := reachable.locallyReachable dominance.2.1
  exact reachable.of_same_region
    (dominance.locallyReachable_dominator_of_locallyReachable_dominated localReachable)
    dominance.2.1

/-- A regional dominator of a hierarchically reachable block is hierarchically reachable. -/
@[grind →]
theorem BlockPtr.ProperlyDominatesInRegion.hierarchicallyReachable_dominator_of_hierarchicallyReachable_dominated
    {dominator dominated : BlockPtr}
    (dominance : dominator.ProperlyDominatesInRegion dominated region ctx)
    (reachable : dominated.HierarchicallyReachable ctx) :
    dominator.HierarchicallyReachable ctx := by
  cases dominance with
  | Ssa dominance =>
    exact dominance.hierarchicallyReachable_dominator_of_hierarchicallyReachable_dominated
      reachable
  | Graph dominance =>
    obtain ⟨dominatorParent, dominatedParent, noSSA⟩ := dominance
    grind

/-! ## Dominance at block insertion points -/

/-- Properly dominating an SSA block's first operation, excluding enclosing operations,
properly dominates the block. -/
theorem OperationPtr.ProperlyDominates.properlyDominatesBlock_of_firstOp {firstOp : OperationPtr}
    (blockParent : block.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (first : block.getFirstOp! ctx.raw = some firstOp)
    (dominance : op.ProperlyDominates firstOp ctx false) :
    op.ProperlyDominatesBlock block ctx false := by
  have blockInBounds : block.InBounds ctx.raw := by
    grind [BlockPtr.getParent!_of_not_inBounds]
  have firstParent : firstOp.getParent! ctx.raw = some block := by grind
  cases dominance with
  | @AncestorDominatedInRegion ancestor localRegion ancestry localDominance _ =>
    by_cases same : ancestor = firstOp
    · subst ancestor
      cases localDominance with
      | SameBlock localDominance =>
        have firstIndex := OperationPtr.idxInParent_eq_zero_of_getFirstOp!
          (by grind) blockInBounds first
        cases localDominance <;>
          grind [OperationPtr.ProperlyDominatesInSSACFGBlock,
            OperationPtr.ProperlyDominatesInGraphBlock]
      | @BlockDominance dominatorBlock dominatedBlock dominatorParent dominatedParent blockDominance =>
        have sameBlock : dominatedBlock = block := by grind
        subst dominatedBlock
        exact .SameRegion dominatorParent blockDominance
    · have properAncestry := ancestry.toProperAncestor (by simpa using same)
      have ancestorOfBlock := properAncestry.ancestor_of_parent_descendant
        (show (IRNode.operation firstOp).parent! ctx = some (.block block) by grind)
      exact .AncestorOpDominated ancestorOfBlock
        (.AncestorDominatedInRegion .refl localDominance false)

/-- An operation properly dominating a successor block dominates its predecessor's exit. -/
theorem OperationPtr.ProperlyDominatesBlock.dominatesIp_predecessor_exit
    (dominance : op.ProperlyDominatesBlock succ ctx enclosingOk)
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    op.DominatesIp (.atEnd block) ctx enclosingOk := by
  have ancestorOfPredecessor {ancestor : OperationPtr}
      (ancestry : ancestor.Ancestor succ ctx) : ancestor.Ancestor block ctx := by
    apply IRNode.Ancestor.of_same_parent_of_properAncestor
      (ancestry.toProperAncestor (by simp)) (parent := .region region) <;> grind
  cases dominance with
  | Ancestor ancestry =>
    exact .AtEndOtherBlock (.Ancestor (ancestorOfPredecessor ancestry))
  | SameRegion dominatorParent dominance =>
    by_cases sameBlock : op.getParent! ctx.raw = some block
    · exact .AtEndSameBlock sameBlock
    · exact .AtEndOtherBlock (.SameRegion dominatorParent
        (dominance.predecessor_of_dominates_successor (by grind) hsucc (by grind)))
  | AncestorOpDominated ancestry dominance =>
    exact .AtEndOtherBlock (.AncestorOpDominated (ancestorOfPredecessor ancestry) dominance)

/-- Dominating an SSA block's start, excluding enclosing operations, properly dominates the block. -/
theorem OperationPtr.DominatesIp.properlyDominatesBlock_of_atStart
    (blockParent : block.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (dominance : op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx) :
    op.ProperlyDominatesBlock block ctx false := by
  have blockInBounds : block.InBounds ctx.raw := by
    grind [BlockPtr.getParent!_of_not_inBounds]
  cases first : block.getFirstOp! ctx.raw with
  | none =>
    simp only [InsertPoint.atStart!_eq, first] at dominance
    cases dominance with
    | AtEndSameBlock opParent =>
      obtain ⟨array, chain⟩ := ctx.wellFormed.opChain block blockInBounds
      grind
    | AtEndOtherBlock dominance => exact dominance
  | some firstOp =>
    simp only [InsertPoint.atStart!_eq, first] at dominance
    cases dominance with
    | Before dominance =>
      exact dominance.properlyDominatesBlock_of_firstOp blockParent regionSSA first

grind_pattern OperationPtr.DominatesIp.properlyDominatesBlock_of_atStart =>
  op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx false,
  block.getParent! ctx.raw, some region, region.hasSSADominance ctx where
  guard block.getParent! ctx.raw = some region
  guard region.hasSSADominance ctx = true

/-- In an SSA region, an operation dominating a successor block's entry also dominates
the predecessor's exit. No CFG reachability is required. -/
theorem OperationPtr.DominatesIp.predecessor_exit_of_successor_entry
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    op.DominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
    op.DominatesIp (.atEnd block) ctx := by
  intro dominance
  have blockDominance := dominance.properlyDominatesBlock_of_atStart succParent regionSSA
  exact blockDominance.dominatesIp_predecessor_exit blockParent succParent hsucc

/-- In an SSA region, a value dominating a successor block's entry dominates the
predecessor's exit or is an argument of the successor. -/
theorem ValuePtr.DominatesIp.predecessor_exit_of_successor_entry {value : ValuePtr}
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    value.DominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
    value.DominatesIp (.atEnd block) ctx ∨ value ∈ succ.getArguments! ctx.raw := by
  intro dominance
  cases dominance with
  | OpResult resultInBounds dominance =>
    exact Or.inl (.OpResult resultInBounds
      (dominance.predecessor_exit_of_successor_entry blockParent succParent regionSSA hsucc))
  | BlockArg argumentInBounds ipParent dominance =>
    rename_i argument ipBlock
    have succInBounds : succ.InBounds ctx.raw := by
      grind [BlockPtr.getParent!_of_not_inBounds]
    have ipParentEq := InsertPoint.block!_atStart!_eq ctx.wellFormed succInBounds
    by_cases same : argument.block = succ
    · exact Or.inr ((BlockArgumentPtr.block_of_mem_getArguments! (by grind)).mp same)
    · exact Or.inl (.BlockArg argumentInBounds (by simp)
        (BlockPtr.Dominates.predecessor_of_dominates_successor
          blockParent succParent same hsucc (by grind)))

/-- An argument of a block dominates any insertion point belonging to that block. -/
theorem BlockPtr.argument_dominatesIp {ip : InsertPoint}
    (ipParent : ip.block! ctx.raw = some block)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    value.DominatesIp ip ctx := by
  obtain ⟨index, _, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
  exact .BlockArg (by grind) ipParent (Or.inl BlockPtr.getArgument_block)

/-- An argument of an in-bounds block dominates the entry of that block. -/
theorem BlockPtr.argument_dominatesIp_atStart
    (blockInBounds : block.InBounds ctx.raw)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    value.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx := by
  exact BlockPtr.argument_dominatesIp
    (InsertPoint.block!_atStart!_eq (by grind) blockInBounds) hMem

end Veir
