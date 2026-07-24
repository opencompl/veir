module

public import Veir.Dominance.InsertPoint

/-!
# Propositional Value Dominance Lemmas

Lemmas about block-argument and operation-result availability. The underlying
definitions live in `Veir.Dominance.Basic`.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

namespace BlockPtr

variable {block : BlockPtr} {region : RegionPtr}

/-- A block entry dominates the start of that block. -/
theorem dominatesIp_atStart
    (blockParent : (block.get! ctx.raw).parent = some region)
    (blockInBounds : block.InBounds ctx.raw) :
    block.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx := by
  have pointBlock :
      (InsertPoint.atStart! block ctx.raw).block! ctx.raw = some block :=
    InsertPoint.block!_atStart!_eq ctx.wellFormed blockInBounds
  exact ⟨region, InsertPoint.atStart! block ctx.raw, block,
    blockParent, InsertPoint.LiftToRegion.here pointBlock blockParent,
    pointBlock, BlockPtr.Dominates.refl blockParent⟩

/-- A block entry sees the same target block immediately before and after an operation. -/
theorem dominatesIp_after_iff_before
    {source : BlockPtr} {op : OperationPtr} {opBlock : BlockPtr}
    (opParent : (op.get! ctx.raw).parent = some opBlock)
    (opInBounds : op.InBounds ctx.raw) :
    source.DominatesIp
        (InsertPoint.after op ctx.raw opBlock opParent opInBounds) ctx ↔
      source.DominatesIp (InsertPoint.before op) ctx := by
  constructor
  · rintro ⟨sourceRegion, afterLift, target, sourceParent,
      afterLifting, afterBlock, blockDominance⟩
    obtain ⟨originalBlock, currentRegion, originalBlockEq, originalBlockParent⟩ :=
      afterLifting.source_parent
    have originalBlockIsOpBlock : originalBlock = opBlock := by
      have afterPointBlock :=
        InsertPoint.block!_after_eq ctx.wellFormed opParent opInBounds
      grind
    subst originalBlock
    obtain ⟨beforeLift, beforeLifting⟩ :=
      afterLifting.exists_before_of_after opParent opInBounds
    have liftedBlocksEq := InsertPoint.LiftToRegion.block_eq_before_after
      opParent originalBlockParent opInBounds beforeLifting afterLifting
    refine ⟨sourceRegion, beforeLift, target, sourceParent,
      beforeLifting, ?_, blockDominance⟩
    rw [liftedBlocksEq, afterBlock]
  · rintro ⟨sourceRegion, beforeLift, target, sourceParent,
      beforeLifting, beforeBlock, blockDominance⟩
    obtain ⟨originalBlock, currentRegion, originalBlockEq, originalBlockParent⟩ :=
      beforeLifting.source_parent
    have originalBlockIsOpBlock : originalBlock = opBlock := by
      simp only [InsertPoint.block!_before_eq] at originalBlockEq
      grind
    subst originalBlock
    obtain ⟨afterLift, afterLifting⟩ :=
      beforeLifting.exists_after_of_before opParent opInBounds
    have liftedBlocksEq := InsertPoint.LiftToRegion.block_eq_before_after
      opParent originalBlockParent opInBounds beforeLifting afterLifting
    refine ⟨sourceRegion, afterLift, target, sourceParent,
      afterLifting, ?_, blockDominance⟩
    rw [← liftedBlocksEq, beforeBlock]

end BlockPtr

namespace OpResultPtr

variable {result : OpResultPtr} {owner : OperationPtr}
variable {block : BlockPtr} {region : RegionPtr}

/--
If an operation result dominates the point before an operation, its recorded
owner dominates that point as an operation. Projection of the target point
accounts for nested regions; direct graph-region self uses remain allowed.
-/
theorem owner_dominatesIp_of_dominatesIp_before
    {target : OperationPtr}
    (resultOwner : (result.get! ctx.raw).owner = owner)
    (resultDominance :
      result.DominatesIp (InsertPoint.before target) ctx) :
    owner.DominatesIp (InsertPoint.before target) ctx := by
  obtain ⟨_, ownerBlock, ownerRegion, lifted, recordedOwnerParent,
    ownerBlockParent, targetLifting, ownerPointDominance, _⟩ :=
    resultDominance
  rw [resultOwner] at recordedOwnerParent ownerPointDominance
  cases targetLifting with
  | before targetProjection =>
      cases targetProjection with
      | here targetParent targetBlockParent =>
          exact ownerPointDominance
      | @step _ _ targetBlock targetRegion parent _ _
          targetParent targetBlockParent regionNe regionParent tail =>
          have ownerNeTarget : owner ≠ target := by
            intro ownerEq
            subst owner
            have targetBlockEq : targetBlock = ownerBlock := by grind
            subst targetBlock
            have : targetRegion = ownerRegion := by grind
            exact regionNe this
          obtain ⟨projectionBlock, projectionParent,
            projectionBlockParent⟩ := tail.parent_region
          have ownerProjection :=
            OperationPtr.dominates_of_dominatesIp_before
              projectionParent projectionBlockParent ownerPointDominance
          have targetAncestor :=
            (OperationPtr.FirstAncestorOpInRegion.step targetParent
              targetBlockParent regionNe regionParent tail).toAncestorOpInRegion
          have ownerTarget : owner.Dominates target ctx :=
            OperationPtr.dominates_of_ancestorOpInRegion ownerProjection
              targetAncestor
          exact OperationPtr.dominatesIp_before ⟨ownerTarget, ownerNeTarget⟩

/-- The operation owner of a dominating result also dominates the target operation. -/
theorem owner_dominates_of_dominatesIp_before
    {target : OperationPtr}
    (resultOwner : (result.get! ctx.raw).owner = owner)
    (resultDominance :
      result.DominatesIp (InsertPoint.before target) ctx) :
    owner.Dominates target ctx := by
  have ownerPointDominance :=
    owner_dominatesIp_of_dominatesIp_before resultOwner resultDominance
  obtain ⟨_, _, _, _, _, _, targetLifting, _, _⟩ := resultDominance
  obtain ⟨targetBlock, targetRegion, targetPointBlock, targetBlockParent⟩ :=
    targetLifting.source_parent
  have targetParent : (target.get! ctx.raw).parent = some targetBlock := by
    simpa using targetPointBlock
  exact OperationPtr.dominates_of_dominatesIp_before targetParent
    targetBlockParent ownerPointDominance

/-- An in-bounds result belongs to the result array of its recorded owner. -/
theorem mem_getResults_of_owner
    (resultInBounds : result.InBounds ctx.raw)
    (resultOwner : (result.get! ctx.raw).owner = owner) :
    ValuePtr.opResult result ∈ owner.getResults! ctx.raw := by
  have resultIndexInBounds : result.index < result.op.getNumResults! ctx.raw :=
    result.inBounds_OperationPtr_getNumResults! ctx.raw resultInBounds
  have recordedOwner : (result.get! ctx.raw).owner = result.op := by
    have ownerAtIndex :=
      (ctx.wellFormed.operations result.op (by
        grind [OpResultPtr.inBounds_def])).result_owner
        result.index resultIndexInBounds
    have resultEq : result.op.getResult result.index = result :=
      (OperationPtr.eq_getResult_of_OpResultPtr_op_eq
        (op := result.op) rfl).symm
    rw [resultEq] at ownerAtIndex
    exact ownerAtIndex
  have ownerEq : result.op = owner := by grind
  have pointerEq : result = owner.getResult result.index :=
    OperationPtr.eq_getResult_of_OpResultPtr_op_eq ownerEq
  exact OperationPtr.getResults!.mem_iff_exists_index.mpr
    ⟨result.index, by simpa [← ownerEq] using resultIndexInBounds,
      congrArg ValuePtr.opResult pointerEq.symm⟩

/-- Membership in an operation's results identifies that operation as the defining op. -/
theorem _root_.Veir.ValuePtr.getDefiningOp!_eq_some_of_mem_getResults
    {value : ValuePtr} {op : OperationPtr}
    (valueMem : value ∈ op.getResults! ctx.raw) :
    value.getDefiningOp! ctx.raw = some op := by
  obtain ⟨index, indexInBounds, resultEq⟩ :=
    OperationPtr.getResults!.mem_iff_exists_index.mp valueMem
  rw [← resultEq] at valueMem ⊢
  have valueInBounds :=
    OperationPtr.getResults!_mem_inBounds
      (ValuePtr.opResult (op.getResult index)) valueMem
  have resultInBounds : (op.getResult index).InBounds ctx.raw := by
    simpa [ValuePtr.InBounds] using valueInBounds
  have opInBounds : op.InBounds ctx.raw := by
    have := OpResultPtr.operation_inBounds_of_inBounds resultInBounds
    simpa using this
  simp only [ValuePtr.getDefiningOp!_opResult]
  congr 1
  exact (ctx.wellFormed.operations op opInBounds).result_owner
    index indexInBounds

/-- An operation result dominates the point immediately after its owner. -/
theorem dominatesIp_after
    (resultInBounds : result.InBounds ctx.raw)
    (resultOwner : (result.get! ctx.raw).owner = owner)
    (ownerParent : (owner.get! ctx.raw).parent = some block)
    (blockParent : (block.get! ctx.raw).parent = some region)
    (ownerInBounds : owner.InBounds ctx.raw) :
    result.DominatesIp
      (InsertPoint.after owner ctx.raw block ownerParent ownerInBounds) ctx := by
  let point := InsertPoint.after owner ctx.raw block ownerParent ownerInBounds
  have pointBlock : point.block! ctx.raw = some block :=
    InsertPoint.block!_after_eq ctx.wellFormed ownerParent ownerInBounds
  have lifted : point.LiftToRegion region point ctx :=
    InsertPoint.LiftToRegion.here pointBlock blockParent
  have ownerDominance : owner.DominatesIp point ctx :=
    (OperationPtr.dominatesIp_iff ownerParent ownerInBounds).2
      OperationPtr.dominates_refl
  refine ⟨resultInBounds, ?_⟩
  change (let resultOwner := (result.get! ctx.raw).owner
    ∃ resultBlock resultRegion lifted,
      (resultOwner.get! ctx.raw).parent = some resultBlock ∧
      (resultBlock.get! ctx.raw).parent = some resultRegion ∧
      point.LiftToRegion resultRegion lifted ctx ∧
      resultOwner.DominatesIp lifted ctx ∧
      (point = .before resultOwner ∨ lifted ≠ .before resultOwner))
  rw [resultOwner]
  refine ⟨block, region, point, ownerParent, blockParent, lifted,
    ownerDominance, ?_⟩
  by_cases pointEq : point = .before owner
  · exact Or.inl pointEq
  · exact Or.inr pointEq

/--
An operation result dominates the point after an operation exactly when it
already dominates the point before it, or it is a result of that operation.
-/
theorem dominatesIp_after_iff_before_or_mem
    {op : OperationPtr} {opBlock : BlockPtr} {opRegion : RegionPtr}
    (opParent : (op.get! ctx.raw).parent = some opBlock)
    (opBlockParent : (opBlock.get! ctx.raw).parent = some opRegion)
    (opInBounds : op.InBounds ctx.raw) :
    result.DominatesIp
        (InsertPoint.after op ctx.raw opBlock opParent opInBounds) ctx ↔
      result.DominatesIp (InsertPoint.before op) ctx ∨
        ValuePtr.opResult result ∈ op.getResults! ctx.raw := by
  let owner := (result.get! ctx.raw).owner
  change
    (result.InBounds ctx.raw ∧
      ∃ ownerBlock ownerRegion afterLift,
        (owner.get! ctx.raw).parent = some ownerBlock ∧
        (ownerBlock.get! ctx.raw).parent = some ownerRegion ∧
        (InsertPoint.after op ctx.raw opBlock opParent opInBounds).LiftToRegion
          ownerRegion afterLift ctx ∧
        owner.DominatesIp afterLift ctx ∧
        (InsertPoint.after op ctx.raw opBlock opParent opInBounds = .before owner ∨
          afterLift ≠ .before owner)) ↔
    (result.InBounds ctx.raw ∧
      ∃ ownerBlock ownerRegion beforeLift,
        (owner.get! ctx.raw).parent = some ownerBlock ∧
        (ownerBlock.get! ctx.raw).parent = some ownerRegion ∧
        (InsertPoint.before op).LiftToRegion ownerRegion beforeLift ctx ∧
        owner.DominatesIp beforeLift ctx ∧
        (InsertPoint.before op = .before owner ∨ beforeLift ≠ .before owner)) ∨
      ValuePtr.opResult result ∈ op.getResults! ctx.raw
  constructor
  · rintro ⟨resultInBounds, ownerBlock, ownerRegion, afterLift,
      ownerParent, ownerBlockParent, afterLifting, ownerDominance, availability⟩
    by_cases ownerEq : owner = op
    · right
      exact mem_getResults_of_owner resultInBounds ownerEq
    · left
      obtain ⟨beforeLift, beforeLifting⟩ :=
        afterLifting.exists_before_of_after opParent opInBounds
      rcases InsertPoint.LiftToRegion.before_after
          opParent opBlockParent opInBounds beforeLifting afterLifting with
        ⟨rfl, rfl, rfl⟩ | ⟨ownerRegionNe, beforeAfterEq⟩
      · have ownerBefore : owner.DominatesIp (InsertPoint.before op) ctx :=
          (OperationPtr.dominatesIp_after_iff_before_or_eq
            opParent opBlockParent opInBounds).mp ownerDominance
            |>.resolve_right ownerEq
        refine ⟨resultInBounds, ownerBlock, ownerRegion, .before op,
          ownerParent, ownerBlockParent, beforeLifting, ownerBefore, ?_⟩
        exact Or.inr (by
          intro pointEq
          exact ownerEq (InsertPoint.before.inj pointEq).symm)
      · subst beforeLift
        refine ⟨resultInBounds, ownerBlock, ownerRegion, afterLift,
          ownerParent, ownerBlockParent, beforeLifting, ownerDominance, ?_⟩
        rcases availability with afterPointEq | afterLiftNe
        · exfalso
          have ownerBlockEq : ownerBlock = opBlock := by
            have afterBlock := InsertPoint.block!_after_eq
              ctx.wellFormed opParent opInBounds
            have ownerPointBlock :
                (InsertPoint.before owner).block! ctx.raw = some ownerBlock := by
              simpa using ownerParent
            rw [afterPointEq, ownerPointBlock] at afterBlock
            exact Option.some.inj afterBlock
          subst ownerBlock
          have : ownerRegion = opRegion := by grind
          exact ownerRegionNe this
        · exact Or.inr afterLiftNe
  · rintro (beforeDominance | resultMem)
    · obtain ⟨resultInBounds, ownerBlock, ownerRegion, beforeLift,
        ownerParent, ownerBlockParent, beforeLifting, ownerDominance, availability⟩ :=
        beforeDominance
      obtain ⟨afterLift, afterLifting⟩ :=
        beforeLifting.exists_after_of_before opParent opInBounds
      rcases InsertPoint.LiftToRegion.before_after
          opParent opBlockParent opInBounds beforeLifting afterLifting with
        ⟨rfl, rfl, rfl⟩ | ⟨ownerRegionNe, beforeAfterEq⟩
      · have ownerAfter :
            owner.DominatesIp
              (InsertPoint.after op ctx.raw opBlock opParent opInBounds) ctx :=
          (OperationPtr.dominatesIp_after_iff_before_or_eq
            opParent opBlockParent opInBounds).mpr (Or.inl ownerDominance)
        refine ⟨resultInBounds, ownerBlock, ownerRegion,
          InsertPoint.after op ctx.raw opBlock opParent opInBounds,
          ownerParent, ownerBlockParent, afterLifting, ownerAfter, ?_⟩
        by_cases afterPointEq :
            InsertPoint.after op ctx.raw opBlock opParent opInBounds = .before owner
        · exact Or.inl afterPointEq
        · exact Or.inr afterPointEq
      · rw [beforeAfterEq] at ownerDominance availability
        refine ⟨resultInBounds, ownerBlock, ownerRegion, afterLift,
          ownerParent, ownerBlockParent, afterLifting, ownerDominance, ?_⟩
        · rcases availability with beforePointEq | afterLiftNe
          · exfalso
            have ownerBlockEq : ownerBlock = opBlock := by
              have ownerPointBlock :
                  (InsertPoint.before owner).block! ctx.raw = some ownerBlock := by
                simpa using ownerParent
              have opPointBlock :
                  (InsertPoint.before op).block! ctx.raw = some opBlock := by
                simpa using opParent
              rw [beforePointEq, ownerPointBlock] at opPointBlock
              exact Option.some.inj opPointBlock
            subst ownerBlock
            have : ownerRegion = opRegion := by grind
            exact ownerRegionNe this
          · exact Or.inr afterLiftNe
    · have valueInBounds : (ValuePtr.opResult result).InBounds ctx.raw :=
        OperationPtr.getResults!_mem_inBounds _ resultMem
      have resultInBounds : result.InBounds ctx.raw := by
        simpa [ValuePtr.InBounds] using valueInBounds
      obtain ⟨index, indexInBounds, resultEq⟩ :=
        OperationPtr.getResults!.mem_iff_exists_index.mp resultMem
      have pointerEq : op.getResult index = result :=
        ValuePtr.opResult.inj resultEq
      have resultOwner : (result.get! ctx.raw).owner = op := by
        rw [← pointerEq]
        exact (ctx.wellFormed.operations op opInBounds).result_owner
          index indexInBounds
      exact dominatesIp_after resultInBounds resultOwner opParent
        opBlockParent opInBounds

end OpResultPtr

namespace BlockArgumentPtr

variable {argument : BlockArgumentPtr} {block : BlockPtr} {region : RegionPtr}

/-- An in-bounds block argument belongs to the argument array of its recorded owner. -/
theorem mem_getArguments_of_owner
    (argumentInBounds : argument.InBounds ctx.raw)
    (argumentOwner : (argument.get! ctx.raw).owner = block) :
    ValuePtr.blockArgument argument ∈ block.getArguments! ctx.raw := by
  have argumentIndexInBounds :
      argument.index < argument.block.getNumArguments! ctx.raw := by
    grind [BlockArgumentPtr.inBounds_def]
  have recordedOwner : (argument.get! ctx.raw).owner = argument.block := by
    have ownerAtIndex := (ctx.wellFormed.blocks argument.block (by
      grind [BlockArgumentPtr.inBounds_def])).argument_owners
      argument.index argumentIndexInBounds
    rw [BlockPtr.getArgument_block_index] at ownerAtIndex
    exact ownerAtIndex
  have blockEq : argument.block = block := by grind
  have pointerEq : block.getArgument argument.index = argument := by
    rw [← blockEq]
    exact BlockPtr.getArgument_block_index
  exact BlockPtr.getArguments!.mem_iff_exists_index.mpr
    ⟨argument.index, by simpa [← blockEq] using argumentIndexInBounds,
      congrArg ValuePtr.blockArgument pointerEq⟩

/-- A block argument dominates the start of its owning block. -/
theorem dominatesIp_atStart
    (argumentInBounds : argument.InBounds ctx.raw)
    (argumentOwner : (argument.get! ctx.raw).owner = block)
    (blockParent : (block.get! ctx.raw).parent = some region)
    (blockInBounds : block.InBounds ctx.raw) :
    argument.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx := by
  exact ⟨argumentInBounds, by
    simp only [argumentOwner]
    exact BlockPtr.dominatesIp_atStart blockParent blockInBounds⟩

end BlockArgumentPtr

namespace OpResultPtr

variable {ctx : WfIRContext OpCode}
variable {result : OpResultPtr}

/-- Operation-result dominance propagates from a verified successor entry to its predecessor. -/
theorem dominatesIp_predecessor_end_of_successor_entry
    {predecessor successor : BlockPtr} {cfgRegion : RegionPtr}
    (ctxVerified : ctx.Verified)
    (predecessorParent :
      (predecessor.get! ctx.raw).parent = some cfgRegion)
    (predecessorInBounds : predecessor.InBounds ctx.raw)
    (successorEdge : successor ∈ predecessor.getSuccessors! ctx.raw)
    (successorDominance :
      result.DominatesIp (InsertPoint.atStart! successor ctx.raw) ctx) :
    result.DominatesIp (InsertPoint.atEnd predecessor) ctx := by
  let owner := (result.get! ctx.raw).owner
  change result.InBounds ctx.raw ∧
    ∃ ownerBlock ownerRegion successorLift,
      (owner.get! ctx.raw).parent = some ownerBlock ∧
      (ownerBlock.get! ctx.raw).parent = some ownerRegion ∧
      (InsertPoint.atStart! successor ctx.raw).LiftToRegion
        ownerRegion successorLift ctx ∧
      owner.DominatesIp successorLift ctx ∧
      (InsertPoint.atStart! successor ctx.raw = .before owner ∨
        successorLift ≠ .before owner) at successorDominance
  obtain ⟨resultInBounds, ownerBlock, ownerRegion, successorLift,
    ownerParent, ownerBlockParent, successorLifting,
    ownerDominance, availability⟩ := successorDominance
  obtain ⟨predecessorLift, predecessorLifting,
      localPoints | ancestorPoint⟩ :=
    successorLifting.exists_predecessor_end_of_successor_entry
      ctxVerified predecessorParent predecessorInBounds successorEdge
  change result.InBounds ctx.raw ∧
    ∃ ownerBlock ownerRegion predecessorLift,
      (owner.get! ctx.raw).parent = some ownerBlock ∧
      (ownerBlock.get! ctx.raw).parent = some ownerRegion ∧
      (InsertPoint.atEnd predecessor).LiftToRegion
        ownerRegion predecessorLift ctx ∧
      owner.DominatesIp predecessorLift ctx ∧
      (InsertPoint.atEnd predecessor = .before owner ∨
        predecessorLift ≠ .before owner)
  rcases localPoints with ⟨rfl, rfl, rfl⟩
  · have ownerAtPredecessorEnd :
        owner.DominatesIp (InsertPoint.atEnd predecessor) ctx :=
      ctxVerified.op_dominatesIp_successor_entry
        predecessorParent predecessorInBounds successorEdge ownerDominance
    refine ⟨resultInBounds, ownerBlock, ownerRegion, .atEnd predecessor,
      ownerParent, ownerBlockParent, predecessorLifting,
      ownerAtPredecessorEnd, ?_⟩
    by_cases pointEq : InsertPoint.atEnd predecessor = .before owner
    · exact Or.inl pointEq
    · exact Or.inr pointEq
  · rcases ancestorPoint with ⟨ownerRegionNe, successorPredecessorEq⟩
    subst predecessorLift
    refine ⟨resultInBounds, ownerBlock, ownerRegion, successorLift,
      ownerParent, ownerBlockParent, predecessorLifting,
      ownerDominance, ?_⟩
    rcases availability with successorPointEq | successorLiftNe
    · exfalso
      have successorParent :
          (successor.get! ctx.raw).parent = some cfgRegion :=
        ctxVerified.successor_parent predecessorInBounds predecessorParent successorEdge
      have successorBlock :
          (InsertPoint.atStart! successor ctx.raw).block! ctx.raw =
            some successor := by
        have successorInBounds : successor.InBounds ctx.raw := by
          grind [Block.default_parent_eq, BlockPtr.get!_of_not_inBounds]
        exact InsertPoint.block!_atStart!_eq
          ctx.wellFormed successorInBounds
      have ownerPointBlock :
          (InsertPoint.before owner).block! ctx.raw = some ownerBlock := by
        simpa using ownerParent
      rw [successorPointEq, ownerPointBlock] at successorBlock
      have ownerBlockEq : ownerBlock = successor :=
        Option.some.inj successorBlock
      subst ownerBlock
      have : ownerRegion = cfgRegion := by grind
      exact ownerRegionNe this
    · exact Or.inr successorLiftNe

end OpResultPtr

namespace BlockArgumentPtr

variable {ctx : WfIRContext OpCode}
variable {argument : BlockArgumentPtr}

/--
Block-argument dominance at a verified successor either propagates to the
predecessor or identifies the successor's own argument.
-/
theorem dominatesIp_predecessor_end_or_mem_of_successor_entry
    {predecessor successor : BlockPtr} {cfgRegion : RegionPtr}
    (ctxVerified : ctx.Verified)
    (predecessorParent :
      (predecessor.get! ctx.raw).parent = some cfgRegion)
    (predecessorInBounds : predecessor.InBounds ctx.raw)
    (successorEdge : successor ∈ predecessor.getSuccessors! ctx.raw)
    (successorDominance :
      argument.DominatesIp (InsertPoint.atStart! successor ctx.raw) ctx) :
    argument.DominatesIp (InsertPoint.atEnd predecessor) ctx ∨
      ValuePtr.blockArgument argument ∈ successor.getArguments! ctx.raw := by
  let owner := (argument.get! ctx.raw).owner
  change argument.InBounds ctx.raw ∧
    ∃ ownerRegion successorLift target,
      (owner.get! ctx.raw).parent = some ownerRegion ∧
      (InsertPoint.atStart! successor ctx.raw).LiftToRegion
        ownerRegion successorLift ctx ∧
      successorLift.block! ctx.raw = some target ∧
      owner.Dominates target ctx at successorDominance
  obtain ⟨argumentInBounds, ownerRegion, successorLift, target,
    ownerParent, successorLifting, successorLiftBlock, blockDominance⟩ :=
    successorDominance
  obtain ⟨predecessorLift, predecessorLifting,
      localPoints | ancestorPoint⟩ :=
    successorLifting.exists_predecessor_end_of_successor_entry
      ctxVerified predecessorParent predecessorInBounds successorEdge
  rcases localPoints with ⟨rfl, rfl, rfl⟩
  · have successorParent :
        (successor.get! ctx.raw).parent = some ownerRegion :=
      ctxVerified.successor_parent predecessorInBounds predecessorParent successorEdge
    have successorInBounds : successor.InBounds ctx.raw := by
      grind [Block.default_parent_eq, BlockPtr.get!_of_not_inBounds]
    have targetEq : target = successor := by
      have successorBlock := InsertPoint.block!_atStart!_eq
        ctx.wellFormed successorInBounds
      grind
    subst target
    by_cases ownerEq : owner = successor
    · right
      exact mem_getArguments_of_owner argumentInBounds ownerEq
    · left
      have ownerDominatesPredecessor : owner.Dominates predecessor ctx :=
        BlockPtr.Dominates.predecessor_of_dominates_successor
          ownerParent predecessorParent successorParent ownerEq
          successorEdge blockDominance
      exact ⟨argumentInBounds, ownerRegion, .atEnd predecessor, predecessor,
        ownerParent, predecessorLifting, by simp, ownerDominatesPredecessor⟩
  · rcases ancestorPoint with ⟨_, successorPredecessorEq⟩
    subst predecessorLift
    left
    exact ⟨argumentInBounds, ownerRegion, successorLift, target,
      ownerParent, predecessorLifting, successorLiftBlock, blockDominance⟩

end BlockArgumentPtr

end Veir
