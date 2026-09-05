module

public import Veir.Rewriter.Basic
public import Veir.Rewriter.LinkedList.WellFormed
public import Veir.IR.DeallocLemmas

public section

namespace Veir

set_option maxHeartbeats 400000
set_option maxRecDepth 8000

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

@[grind =]
theorem Rewriter.detachOp_veir_inBounds
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (ptr : Veir.GenericPtr) :
    ptr.InBounds (Rewriter.detachOp ctx op hctx hIn hasParent).spec ↔
      ptr.InBounds ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split <;> grind

@[simp]
theorem BlockPtr.firstUse!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (block : Veir.BlockPtr) :
    (block.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).firstUse =
      (block.get! ctx.spec).firstUse := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals
    simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
      Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
      Sim.OperationPtr.setParent_spec,
      BlockPtr.firstUse!_BlockPtr_setFirstOp, BlockPtr.firstUse!_BlockPtr_setLastOp,
      BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
      BlockPtr.get!_OperationPtr_setParent]

@[simp]
theorem OperationPtr.parent!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operation : Veir.OperationPtr) :
    (operation.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).parent =
      if operation = op.spec then none else (operation.get! ctx.spec).parent := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals
    simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
      Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
      Sim.OperationPtr.setParent_spec,
      OperationPtr.get!_BlockPtr_setFirstOp, OperationPtr.get!_BlockPtr_setLastOp,
      OperationPtr.parent!_OperationPtr_setNextOp,
      OperationPtr.parent!_OperationPtr_setPrevOp,
      OperationPtr.parent!_OperationPtr_setParent]
    split <;> rfl

theorem BlockPtr.firstOp!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (block : Veir.BlockPtr) :
    (block.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).firstOp =
      if (op.spec.get! ctx.spec).prev = none ∧
          some block = (op.spec.get! ctx.spec).parent then
        (op.spec.get! ctx.spec).next
      else (block.get! ctx.spec).firstOp := by
  have hPrevIB : (op.getPrevOp ctx hIn).InBounds ctx := by grind
  have hParentIB : (op.getParent ctx hIn).InBounds ctx := by grind
  have hPrevNone : (op.getPrevOp ctx hIn).toOption = none ↔
      (op.spec.get! ctx.spec).prev = none := by
    rw [Sim.OptionOperationPtr.toOption_none_iff_spec_none hPrevIB,
      Sim.OperationPtr.getPrevOp_spec ctx op hIn]
    rw [OperationPtr.get!_eq_get]
  have hNextSpec := Sim.OperationPtr.getNextOp_spec ctx op hIn
  have hNextSpecBang : (op.getNextOp ctx hIn).spec =
      (op.spec.get! ctx.spec).next := by
    rw [OperationPtr.get!_eq_get]
    exact hNextSpec
  have hParentSome : (op.getParent ctx hIn).spec =
      some ((op.getParent ctx hIn).toOption.get hasParent).spec := by
    apply Sim.OptionBlockPtr.toOption_some hParentIB
    exact (Option.some_get hasParent).symm
  rw [Sim.OperationPtr.getParent_spec ctx op hIn] at hParentSome
  have hParentSomeBang : (op.spec.get! ctx.spec).parent =
      some ((op.getParent ctx hIn).toOption.get hasParent).spec := by
    rw [OperationPtr.get!_eq_get]
    exact hParentSome
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split
  next prev hprev =>
    have hp : (op.spec.get! ctx.spec).prev ≠ none := by
      intro hp
      have hnone := hPrevNone.mpr hp
      simpa [hprev] using hnone
    split <;>
    simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
      Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
      Sim.OperationPtr.setParent_spec,
      BlockPtr.firstOp!_BlockPtr_setFirstOp, BlockPtr.firstOp!_BlockPtr_setLastOp,
      BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
      BlockPtr.get!_OperationPtr_setParent]
    all_goals rw [if_neg (fun h => hp h.1)]
  next hprev =>
    have hp : (op.spec.get! ctx.spec).prev = none := hPrevNone.mp hprev
    split <;>
      simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
        Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
        Sim.OperationPtr.setParent_spec,
        BlockPtr.firstOp!_BlockPtr_setFirstOp, BlockPtr.firstOp!_BlockPtr_setLastOp,
        BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
        BlockPtr.get!_OperationPtr_setParent]
    all_goals
      by_cases hb : some block = (op.spec.get! ctx.spec).parent
      · simp only [hp, true_and]
        rw [if_pos hb]
        have hpb : ((op.getParent ctx hIn).toOption.get hasParent).spec = block := by
          rw [hParentSomeBang] at hb
          exact Option.some.inj hb.symm
        rw [if_pos hpb, hNextSpecBang]
      · simp only [hp, true_and]
        rw [if_neg hb]
        have hpb : ((op.getParent ctx hIn).toOption.get hasParent).spec ≠ block := by
          intro hpb
          apply hb
          rw [hParentSomeBang, hpb]
        rw [if_neg hpb]

theorem Rewriter.detachOperands.loop_wellFormed
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr) (off : Int64) (index : UInt64)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : op.InBounds ctx)
    (hIndex : index.toNat < op.spec.getNumOperands! ctx.spec)
    (hoff : off = Buffed.Operation.Offsets.operands op.spec ctx.spec)
    (wf : ctx.spec.WellFormed missingOperands missingSuccessors)
    (hMissing : ∀ i, i ≤ index.toNat → OpOperandPtr.mk op.spec i ∉ missingOperands) :
    (Rewriter.detachOperands.loop ctx op off index hCtx hOp hIndex hoff).spec.WellFormed
      (missingOperands.insertMany
        ((0...=index.toNat).toList.map (fun i => OpOperandPtr.mk op.spec i)))
      missingSuccessors := by
  simp only [Rewriter.detachOperands.loop_def]
  fun_induction Rewriter.detachOperands.loopSim generalizing missingOperands missingSuccessors
  case case1 =>
    let use := op.getOperandPtrAt _ off 0 (by assumption) (by assumption)
    have hUseSpec : use.spec = OpOperandPtr.mk op.spec 0 := rfl
    have hwf := Sim.IRContext.wellFormed_OpOperandPtr_removeFromCurrent
      (use := use) (useInBounds := by
        dsimp [use]
        rw [Sim.OperationPtr.getOperandPtrAt_eq_getOperandPtr]
        exact Sim.OperationPtr.getOpOperand_inBounds op (by assumption) 0 (by assumption))
      (ctxInBounds := wf.inBounds)
      (useMissing := by simpa [hUseSpec] using hMissing 0 (by simp)) wf
    simpa [use, hUseSpec, Nat.toList_rcc_eq_singleton,
      Std.ExtHashSet.insertMany_list_singleton] using hwf
  case case2 =>
    rename_i _ _ _ currentCtx currentIndex hCtxCur hOpCur hIndexCur hoffCur currentCtx' hne ih
    have hCurrentPos : 0 < currentIndex.toNat := by
      have hneNat : currentIndex.toNat ≠ 0 := by
        intro hz
        apply hne
        apply UInt64.toNat_inj.mp
        simpa using hz
      omega
    have hCurrentLt := UInt64.toNat_lt currentIndex
    have hPred : (currentIndex - 1).toNat = currentIndex.toNat - 1 := by
      rw [UInt64.toNat_sub]
      change (2 ^ 64 - 1 + currentIndex.toNat) % 2 ^ 64 = currentIndex.toNat - 1
      have heq : 2 ^ 64 - 1 + currentIndex.toNat =
          2 ^ 64 + (currentIndex.toNat - 1) := by omega
      rw [heq, Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    let use := op.getOperandPtrAt currentCtx off currentIndex (by assumption) (by assumption)
    have hUseSpec : use.spec = OpOperandPtr.mk op.spec currentIndex.toNat := rfl
    have hwfRemoved := Sim.IRContext.wellFormed_OpOperandPtr_removeFromCurrent
      (use := use) (useInBounds := by
        dsimp [use]
        rw [Sim.OperationPtr.getOperandPtrAt_eq_getOperandPtr]
        exact Sim.OperationPtr.getOpOperand_inBounds op (by assumption) currentIndex (by assumption))
      (ctxInBounds := wf.inBounds)
      (useMissing := by
        rw [hUseSpec]
        exact hMissing currentIndex.toNat (Nat.le_refl _)) wf
    have hwfRec := ih hwfRemoved (by
      intro i hi
      simp only [Std.ExtHashSet.mem_insert, hUseSpec, not_or]
      constructor
      · simp only [beq_iff_eq, OpOperandPtr.mk.injEq, true_and]
        rw [hPred] at hi
        omega
      · apply hMissing i
        rw [hPred] at hi
        omega)
    have hSets :
        (missingOperands.insert use.spec).insertMany
            ((0...=(currentIndex - 1).toNat).toList.map
              (fun i => OpOperandPtr.mk op.spec i)) =
          missingOperands.insertMany
            ((0...=currentIndex.toNat).toList.map
              (fun i => OpOperandPtr.mk op.spec i)) := by
      rw [hUseSpec, Nat.toList_rcc_eq_toList_rco, hPred]
      have hSucc : currentIndex.toNat - 1 + 1 = currentIndex.toNat := by omega
      rw [hSucc, Nat.toList_rcc_eq_append (Nat.zero_le _), List.map_append,
        List.map_singleton, Std.ExtHashSet.insertMany_append,
        Std.ExtHashSet.insertMany_list_singleton,
        Std.ExtHashSet.insertMany_list_insert_comm]
    rw [hSets] at hwfRec
    exact hwfRec

theorem BlockPtr.lastOp!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (block : Veir.BlockPtr) :
    (block.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).lastOp =
      if (op.spec.get! ctx.spec).next = none ∧
          some block = (op.spec.get! ctx.spec).parent then
        (op.spec.get! ctx.spec).prev
      else (block.get! ctx.spec).lastOp := by
  have hNextIB : (op.getNextOp ctx hIn).InBounds ctx := by grind
  have hParentIB : (op.getParent ctx hIn).InBounds ctx := by grind
  have hNextNone : (op.getNextOp ctx hIn).toOption = none ↔
      (op.spec.get! ctx.spec).next = none := by
    rw [Sim.OptionOperationPtr.toOption_none_iff_spec_none hNextIB,
      Sim.OperationPtr.getNextOp_spec ctx op hIn]
    rw [OperationPtr.get!_eq_get]
  have hPrevSpec := Sim.OperationPtr.getPrevOp_spec ctx op hIn
  have hPrevSpecBang : (op.getPrevOp ctx hIn).spec =
      (op.spec.get! ctx.spec).prev := by
    rw [OperationPtr.get!_eq_get]
    exact hPrevSpec
  have hParentSome : (op.getParent ctx hIn).spec =
      some ((op.getParent ctx hIn).toOption.get hasParent).spec := by
    apply Sim.OptionBlockPtr.toOption_some hParentIB
    exact (Option.some_get hasParent).symm
  rw [Sim.OperationPtr.getParent_spec ctx op hIn] at hParentSome
  have hParentSomeBang : (op.spec.get! ctx.spec).parent =
      some ((op.getParent ctx hIn).toOption.get hasParent).spec := by
    rw [OperationPtr.get!_eq_get]
    exact hParentSome
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split
  next prev hprev =>
    split
    next next hnext =>
      have hn : (op.spec.get! ctx.spec).next ≠ none := by
        intro hn
        have := hNextNone.mpr hn
        simp [hnext] at this
      simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
        Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
        Sim.OperationPtr.setParent_spec,
        BlockPtr.lastOp!_BlockPtr_setFirstOp, BlockPtr.lastOp!_BlockPtr_setLastOp,
        BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
        BlockPtr.get!_OperationPtr_setParent]
      rw [if_neg (fun h => hn h.1)]
    next hnext =>
      have hn : (op.spec.get! ctx.spec).next = none := hNextNone.mp hnext
      simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
        Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
        Sim.OperationPtr.setParent_spec,
        BlockPtr.lastOp!_BlockPtr_setFirstOp, BlockPtr.lastOp!_BlockPtr_setLastOp,
        BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
        BlockPtr.get!_OperationPtr_setParent]
      by_cases hb : some block = (op.spec.get! ctx.spec).parent
      · simp only [hn, true_and]
        rw [if_pos hb]
        have hpb : ((op.getParent ctx hIn).toOption.get hasParent).spec = block := by
          rw [hParentSomeBang] at hb
          exact Option.some.inj hb.symm
        rw [if_pos hpb]
        have hp := Sim.OptionOperationPtr.toOption_some
          (by grind : (op.getPrevOp ctx hIn).InBounds ctx) hprev
        change some prev.spec = (op.spec.get! ctx.spec).prev
        exact hp.symm.trans hPrevSpecBang
      · simp only [hn, true_and]
        rw [if_neg hb]
        have hpb : ((op.getParent ctx hIn).toOption.get hasParent).spec ≠ block := by
          intro hpb
          apply hb
          rw [hParentSomeBang, hpb]
        rw [if_neg hpb]
  next hprev =>
    split
    next next hnext =>
      have hn : (op.spec.get! ctx.spec).next ≠ none := by
        intro hn
        have := hNextNone.mpr hn
        simp [hnext] at this
      simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
        Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
        Sim.OperationPtr.setParent_spec,
        BlockPtr.lastOp!_BlockPtr_setFirstOp, BlockPtr.lastOp!_BlockPtr_setLastOp,
        BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
        BlockPtr.get!_OperationPtr_setParent]
      rw [if_neg (fun h => hn h.1)]
    next hnext =>
      have hn : (op.spec.get! ctx.spec).next = none := hNextNone.mp hnext
      simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
        Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
        Sim.OperationPtr.setParent_spec,
        BlockPtr.lastOp!_BlockPtr_setFirstOp, BlockPtr.lastOp!_BlockPtr_setLastOp,
        BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
        BlockPtr.get!_OperationPtr_setParent]
      by_cases hb : some block = (op.spec.get! ctx.spec).parent
      · simp only [hn, true_and]
        rw [if_pos hb]
        have hpb : ((op.getParent ctx hIn).toOption.get hasParent).spec = block := by
          rw [hParentSomeBang] at hb
          exact Option.some.inj hb.symm
        rw [if_pos hpb]
        have hp := (Sim.OptionOperationPtr.toOption_none_iff_spec_none
          (by grind : (op.getPrevOp ctx hIn).InBounds ctx)).mp hprev
        simpa [hp] using hPrevSpecBang
      · simp only [hn, true_and]
        rw [if_neg hb]
        have hpb : ((op.getParent ctx hIn).toOption.get hasParent).spec ≠ block := by
          intro hpb
          apply hb
          rw [hParentSomeBang, hpb]
        rw [if_neg hpb]

theorem OperationPtr.prev!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operation : Veir.OperationPtr) :
    (operation.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).prev =
      if some operation = (op.spec.get! ctx.spec).next then
        (op.spec.get! ctx.spec).prev
      else if operation = op.spec then none else (operation.get! ctx.spec).prev := by
  have hPrevIB : (op.getPrevOp ctx hIn).InBounds ctx := by grind
  have hNextIB : (op.getNextOp ctx hIn).InBounds ctx := by grind
  have hPrevSpec : (op.getPrevOp ctx hIn).spec =
      (op.spec.get! ctx.spec).prev := by
    rw [Sim.OperationPtr.getPrevOp_spec ctx op hIn, OperationPtr.get!_eq_get]
  have hNextSpec : (op.getNextOp ctx hIn).spec =
      (op.spec.get! ctx.spec).next := by
    rw [Sim.OperationPtr.getNextOp_spec ctx op hIn, OperationPtr.get!_eq_get]
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals
    simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
      Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
      Sim.OperationPtr.setParent_spec,
      OperationPtr.get!_BlockPtr_setFirstOp, OperationPtr.get!_BlockPtr_setLastOp,
      OperationPtr.prev!_OperationPtr_setNextOp,
      OperationPtr.prev!_OperationPtr_setPrevOp,
      OperationPtr.prev!_OperationPtr_setParent]
  next prev hprev next hnext =>
    have hp := Sim.OptionOperationPtr.toOption_some hPrevIB hprev
    have hn := Sim.OptionOperationPtr.toOption_some hNextIB hnext
    have hp' : (op.spec.get! ctx.spec).prev = some prev.spec := hPrevSpec.symm.trans hp
    have hn' : (op.spec.get! ctx.spec).next = some next.spec := hNextSpec.symm.trans hn
    have hnRaw := hn'
    rw [OperationPtr.get!_eq_get (hin := hIn.ib)] at hnRaw
    simp [hp', hn', hnRaw, Sim.OperationPtr.toO, Sim.OptionOperationPtr.none]
  next prev hprev hnext =>
    have hp := Sim.OptionOperationPtr.toOption_some hPrevIB hprev
    have hn := (Sim.OptionOperationPtr.toOption_none_iff_spec_none hNextIB).mp hnext
    have hp' : (op.spec.get! ctx.spec).prev = some prev.spec := hPrevSpec.symm.trans hp
    have hn' : (op.spec.get! ctx.spec).next = none := hNextSpec.symm.trans hn
    simp [hp', hn', Sim.OperationPtr.toO, Sim.OptionOperationPtr.none]
  next hprev next hnext =>
    have hp := (Sim.OptionOperationPtr.toOption_none_iff_spec_none hPrevIB).mp hprev
    have hn := Sim.OptionOperationPtr.toOption_some hNextIB hnext
    have hp' : (op.spec.get! ctx.spec).prev = none := hPrevSpec.symm.trans hp
    have hn' : (op.spec.get! ctx.spec).next = some next.spec := hNextSpec.symm.trans hn
    have hpRaw := hp'
    rw [OperationPtr.get!_eq_get (hin := hIn.ib)] at hpRaw
    simp [hp', hpRaw, hn', Sim.OperationPtr.toO, Sim.OptionOperationPtr.none]
  next hprev hnext =>
    have hp := (Sim.OptionOperationPtr.toOption_none_iff_spec_none hPrevIB).mp hprev
    have hn := (Sim.OptionOperationPtr.toOption_none_iff_spec_none hNextIB).mp hnext
    have hp' : (op.spec.get! ctx.spec).prev = none := hPrevSpec.symm.trans hp
    have hn' : (op.spec.get! ctx.spec).next = none := hNextSpec.symm.trans hn
    simp [hp', hn', Sim.OperationPtr.toO, Sim.OptionOperationPtr.none]

theorem OperationPtr.next!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operation : Veir.OperationPtr) :
    (operation.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).next =
      if some operation = (op.spec.get! ctx.spec).prev then
        (op.spec.get! ctx.spec).next
      else if operation = op.spec then none else (operation.get! ctx.spec).next := by
  have hPrevIB : (op.getPrevOp ctx hIn).InBounds ctx := by grind
  have hNextIB : (op.getNextOp ctx hIn).InBounds ctx := by grind
  have hPrevSpec : (op.getPrevOp ctx hIn).spec =
      (op.spec.get! ctx.spec).prev := by
    rw [Sim.OperationPtr.getPrevOp_spec ctx op hIn, OperationPtr.get!_eq_get]
  have hNextSpec : (op.getNextOp ctx hIn).spec =
      (op.spec.get! ctx.spec).next := by
    rw [Sim.OperationPtr.getNextOp_spec ctx op hIn, OperationPtr.get!_eq_get]
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals
    simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
      Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
      Sim.OperationPtr.setParent_spec,
      OperationPtr.get!_BlockPtr_setFirstOp, OperationPtr.get!_BlockPtr_setLastOp,
      OperationPtr.next!_OperationPtr_setNextOp,
      OperationPtr.next!_OperationPtr_setPrevOp,
      OperationPtr.next!_OperationPtr_setParent]
  next prev hprev next hnext =>
    have hp := Sim.OptionOperationPtr.toOption_some hPrevIB hprev
    have hn := Sim.OptionOperationPtr.toOption_some hNextIB hnext
    have hp' : (op.spec.get! ctx.spec).prev = some prev.spec := hPrevSpec.symm.trans hp
    have hn' : (op.spec.get! ctx.spec).next = some next.spec := hNextSpec.symm.trans hn
    have hnRaw := hn'
    rw [OperationPtr.get!_eq_get (hin := hIn.ib)] at hnRaw
    simp [hp', hn', hnRaw, Sim.OperationPtr.toO, Sim.OptionOperationPtr.none]
  next prev hprev hnext =>
    have hp := Sim.OptionOperationPtr.toOption_some hPrevIB hprev
    have hn := (Sim.OptionOperationPtr.toOption_none_iff_spec_none hNextIB).mp hnext
    have hp' : (op.spec.get! ctx.spec).prev = some prev.spec := hPrevSpec.symm.trans hp
    have hn' : (op.spec.get! ctx.spec).next = none := hNextSpec.symm.trans hn
    have hnRaw := hn'
    rw [OperationPtr.get!_eq_get (hin := hIn.ib)] at hnRaw
    simp [hp', hn', hnRaw, Sim.OperationPtr.toO, Sim.OptionOperationPtr.none]
  next hprev next hnext =>
    have hp := (Sim.OptionOperationPtr.toOption_none_iff_spec_none hPrevIB).mp hprev
    have hn := Sim.OptionOperationPtr.toOption_some hNextIB hnext
    have hp' : (op.spec.get! ctx.spec).prev = none := hPrevSpec.symm.trans hp
    have hn' : (op.spec.get! ctx.spec).next = some next.spec := hNextSpec.symm.trans hn
    simp [hp', hn', Sim.OperationPtr.toO, Sim.OptionOperationPtr.none]
  next hprev hnext =>
    have hp := (Sim.OptionOperationPtr.toOption_none_iff_spec_none hPrevIB).mp hprev
    have hn := (Sim.OptionOperationPtr.toOption_none_iff_spec_none hNextIB).mp hnext
    have hp' : (op.spec.get! ctx.spec).prev = none := hPrevSpec.symm.trans hp
    have hn' : (op.spec.get! ctx.spec).next = none := hNextSpec.symm.trans hn
    simp [hp', hn', Sim.OperationPtr.toO, Sim.OptionOperationPtr.none]

@[simp]
theorem OpOperandPtr.get!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operand : Veir.OpOperandPtr) :
    operand.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec =
      operand.get! ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec,
    OpOperandPtr.get!_BlockPtr_setFirstOp, OpOperandPtr.get!_BlockPtr_setLastOp,
    OpOperandPtr.get!_OperationPtr_setNextOp, OpOperandPtr.get!_OperationPtr_setPrevOp,
    OpOperandPtr.get!_OperationPtr_setParent]

@[simp]
theorem BlockOperandPtr.get!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operand : Veir.BlockOperandPtr) :
    operand.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec =
      operand.get! ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec,
    BlockOperandPtr.get!_BlockPtr_setFirstOp, BlockOperandPtr.get!_BlockPtr_setLastOp,
    BlockOperandPtr.get!_OperationPtr_setNextOp, BlockOperandPtr.get!_OperationPtr_setPrevOp,
    BlockOperandPtr.get!_OperationPtr_setParent]

@[simp]
theorem OpResultPtr.get!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (result : Veir.OpResultPtr) :
    result.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec =
      result.get! ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec,
    OpResultPtr.get!_BlockPtr_setFirstOp, OpResultPtr.get!_BlockPtr_setLastOp,
    OpResultPtr.get!_OperationPtr_setNextOp, OpResultPtr.get!_OperationPtr_setPrevOp,
    OpResultPtr.get!_OperationPtr_setParent]

@[simp]
theorem BlockArgumentPtr.get!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (argument : Veir.BlockArgumentPtr) :
    argument.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec =
      argument.get! ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec,
    BlockArgumentPtr.get!_BlockPtr_setFirstOp, BlockArgumentPtr.get!_BlockPtr_setLastOp,
    BlockArgumentPtr.get!_OperationPtr_setNextOp,
    BlockArgumentPtr.get!_OperationPtr_setPrevOp,
    BlockArgumentPtr.get!_OperationPtr_setParent]

@[simp]
theorem RegionPtr.get!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (region : Veir.RegionPtr) :
    region.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec =
      region.get! ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec,
    RegionPtr.get!_BlockPtr_setFirstOp, RegionPtr.get!_BlockPtr_setLastOp,
    RegionPtr.get!_OperationPtr_setNextOp, RegionPtr.get!_OperationPtr_setPrevOp,
    RegionPtr.get!_OperationPtr_setParent]

@[simp]
theorem ValuePtr.getFirstUse!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (value : Veir.ValuePtr) :
    value.getFirstUse! (Rewriter.detachOp ctx op hctx hIn hasParent).spec =
      value.getFirstUse! ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec,
    ValuePtr.getFirstUse!_BlockPtr_setFirstOp, ValuePtr.getFirstUse!_BlockPtr_setLastOp,
    ValuePtr.getFirstUse!_OperationPtr_setNextOp,
    ValuePtr.getFirstUse!_OperationPtr_setPrevOp,
    ValuePtr.getFirstUse!_OperationPtr_setParent]

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operation : Veir.OperationPtr) :
    operation.getNumResults! (Rewriter.detachOp ctx op hctx hIn hasParent).spec =
      operation.getNumResults! ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec]
  all_goals grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operation : Veir.OperationPtr) :
    operation.getNumRegions! (Rewriter.detachOp ctx op hctx hIn hasParent).spec =
      operation.getNumRegions! ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec]
  all_goals grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operation : Veir.OperationPtr) (i : Nat) :
    operation.getRegion! (Rewriter.detachOp ctx op hctx hIn hasParent).spec i =
      operation.getRegion! ctx.spec i := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec]
  all_goals grind

@[simp, grind =]
theorem OperationPtr.capResults!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operation : Veir.OperationPtr) :
    (operation.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).capResults =
      (operation.get! ctx.spec).capResults := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec]
  all_goals grind

@[simp, grind =]
theorem OperationPtr.capRegions!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (operation : Veir.OperationPtr) :
    (operation.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).capRegions =
      (operation.get! ctx.spec).capRegions := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec]
  all_goals grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (block : Veir.BlockPtr) :
    block.getNumArguments! (Rewriter.detachOp ctx op hctx hIn hasParent).spec =
      block.getNumArguments! ctx.spec := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec]
  all_goals grind

@[simp, grind =]
theorem BlockPtr.capArguments!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (block : Veir.BlockPtr) :
    (block.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).capArguments =
      (block.get! ctx.spec).capArguments := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec]
  all_goals grind

@[simp]
theorem BlockPtr.prev!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (block : Veir.BlockPtr) :
    (block.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).prev =
      (block.get! ctx.spec).prev := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec,
    BlockPtr.prev!_BlockPtr_setFirstOp, BlockPtr.prev!_BlockPtr_setLastOp,
    BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
    BlockPtr.get!_OperationPtr_setParent]

@[simp]
theorem BlockPtr.next!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (block : Veir.BlockPtr) :
    (block.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).next =
      (block.get! ctx.spec).next := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec,
    BlockPtr.next!_BlockPtr_setFirstOp, BlockPtr.next!_BlockPtr_setLastOp,
    BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
    BlockPtr.get!_OperationPtr_setParent]

@[simp]
theorem BlockPtr.parent!_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (block : Veir.BlockPtr) :
    (block.get! (Rewriter.detachOp ctx op hctx hIn hasParent).spec).parent =
      (block.get! ctx.spec).parent := by
  simp only [Rewriter.detachOp_def, Rewriter.detachOpSim,
    Rewriter.unsetParentAndNeighbors_def, Rewriter.unsetParentAndNeighborsSim]
  split <;> split
  all_goals simp only [Sim.BlockPtr.setFirstOp_spec, Sim.BlockPtr.setLastOp_spec,
    Sim.OperationPtr.setNextOp_spec, Sim.OperationPtr.setPrevOp_spec,
    Sim.OperationPtr.setParent_spec,
    BlockPtr.parent!_BlockPtr_setFirstOp, BlockPtr.parent!_BlockPtr_setLastOp,
    BlockPtr.get!_OperationPtr_setNextOp, BlockPtr.get!_OperationPtr_setPrevOp,
    BlockPtr.get!_OperationPtr_setParent]

attribute [grind =] BlockPtr.firstUse!_detachOp BlockPtr.firstOp!_detachOp
  BlockPtr.lastOp!_detachOp BlockPtr.prev!_detachOp BlockPtr.next!_detachOp
  BlockPtr.parent!_detachOp OperationPtr.prev!_detachOp OperationPtr.next!_detachOp
  OperationPtr.parent!_detachOp OpOperandPtr.get!_detachOp BlockOperandPtr.get!_detachOp
  OpResultPtr.get!_detachOp BlockArgumentPtr.get!_detachOp RegionPtr.get!_detachOp
  ValuePtr.getFirstUse!_detachOp

theorem BlockPtr.opChain_detachOp_other
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (hWf : BlockPtr.OpChain block ctx.spec array)
    (hWf' : BlockPtr.OpChain block' ctx.spec array')
    (hParent : (op.spec.get! ctx.spec).parent = some block')
    (hNe : block ≠ block') :
    BlockPtr.OpChain block (Rewriter.detachOp ctx op hctx hIn hasParent).spec array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx.spec) hWf <;>
    grind [BlockPtr.OpChain]

theorem BlockPtr.OpChain.prev_ne_self
    (ctx : IRContext OpInfo) (block : BlockPtr) (array : Array OperationPtr)
    (missingOps : Std.ExtHashSet OperationPtr) (op : OperationPtr)
    (hWf : block.OpChain ctx array missingOps)
    (hop : op.InBounds ctx)
    (hmissing : op ∉ missingOps)
    (hparent : (op.get! ctx).parent = some block) :
    (op.get! ctx).prev ≠ some op := by
  have opMem : op ∈ array := (hWf.allOpsInChain op hop hparent).mpr hmissing
  intro heq
  have ⟨i, hi⟩ := Array.getElem_of_mem opMem
  have hopEq : array[i]'(by grind) = op := by grind
  have hiPos : i > 0 := by grind [BlockPtr.OpChain]
  have hprev := hWf.prev i hiPos (by grind)
  have : op = array[i - 1]'(by grind) := by grind
  grind [BlockPtr.OpChain_array_injective]

theorem BlockPtr.OpChain.next_ne_self
    (ctx : IRContext OpInfo) (block : BlockPtr) (array : Array OperationPtr)
    (missingOps : Std.ExtHashSet OperationPtr) (op : OperationPtr)
    (hWf : block.OpChain ctx array missingOps)
    (hop : op.InBounds ctx)
    (hmissing : op ∉ missingOps)
    (hparent : (op.get! ctx).parent = some block) :
    (op.get! ctx).next ≠ some op := by
  have opMem : op ∈ array := (hWf.allOpsInChain op hop hparent).mpr hmissing
  intro heq
  have ⟨i, hi⟩ := Array.getElem?_of_mem opMem
  have hnext : array[i + 1]? = some op := by grind [BlockPtr.OpChain]
  grind [BlockPtr.OpChain_array_injective]

set_option maxHeartbeats 800000 in
theorem BlockPtr.opChain_detachOp_self
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (hWf : BlockPtr.OpChain block ctx.spec array)
    (hParent : (op.spec.get! ctx.spec).parent = some block) :
    BlockPtr.OpChain block (Rewriter.detachOp ctx op hctx hIn hasParent).spec
      (array.erase op.spec) := by
  have opInArray : op.spec ∈ array := by grind [BlockPtr.OpChain]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem opInArray
  constructor
  case prev =>
    rw [← hi]
    intros i' hi₁' hi₂'
    simp only [BlockPtr.OpChain.erase_getElem_array_eq_eraseIdx hWf]
    by_cases i' < i
    · simp (disch := grind) only [Array.getElem_eraseIdx_of_lt]
      simp only [OperationPtr.prev!_detachOp]
      grind (instances := 2000) [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
    · by_cases i' = i
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
  case next =>
    rw [← hi]
    intros i' hi'
    simp only [BlockPtr.OpChain.erase_getElem_array_eq_eraseIdx hWf]
    by_cases i' > i
    · simp (disch := grind) only [Array.getElem_eraseIdx_of_ge,
        Array.getElem?_eraseIdx_of_ge]
      simp only [OperationPtr.next!_detachOp]
      grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
    · by_cases i' = i
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
  all_goals grind [BlockPtr.OpChain]

theorem ValuePtr.defUse_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (hWf : ValuePtr.DefUse value ctx.spec array missingUses) :
    ValuePtr.DefUse value (Rewriter.detachOp ctx op hctx hIn hasParent).spec
      array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx.spec) <;> grind

theorem BlockPtr.defUse_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (hWf : BlockPtr.DefUse block ctx.spec array missingUses) :
    BlockPtr.DefUse block (Rewriter.detachOp ctx op hctx hIn hasParent).spec
      array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx.spec) <;> grind

theorem RegionPtr.blockChain_detachOp
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds) (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome)
    (hWf : RegionPtr.BlockChain region ctx.spec array) :
    RegionPtr.BlockChain region (Rewriter.detachOp ctx op hctx hIn hasParent).spec array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx.spec) hWf <;> grind

theorem Rewriter.detachOp_WellFormed
    (ctx : Sim.IRContext OpInfo)
    (wf : ctx.spec.WellFormed missingOperands missingSuccessors)
    (hctx : ctx.spec.FieldsInBounds) (op : Sim.OperationPtr)
    (hIn : op.InBounds ctx)
    (hasParent : (op.getParent ctx hIn).toOption.isSome) :
    (Rewriter.detachOp ctx op hctx hIn hasParent).spec.WellFormed
      missingOperands missingSuccessors := by
  have hParentIB : (op.getParent ctx hIn).InBounds ctx := by grind
  have hParentSome : (op.getParent ctx hIn).spec =
      some ((op.getParent ctx hIn).toOption.get hasParent).spec := by
    apply Sim.OptionBlockPtr.toOption_some hParentIB
    exact (Option.some_get hasParent).symm
  rw [Sim.OperationPtr.getParent_spec ctx op hIn] at hParentSome
  have hParent : (op.spec.get! ctx.spec).parent =
      some ((op.getParent ctx hIn).toOption.get hasParent).spec := by
    rw [OperationPtr.get!_eq_get]
    exact hParentSome
  constructor
  case inBounds => exact Rewriter.detachOp_fieldsInBounds hctx
  case valueDefUseChains =>
    intro value hvalue
    have ⟨array, harray⟩ := wf.valueDefUseChains value (by grind)
    refine ⟨array, ?_⟩
    apply ValuePtr.defUse_detachOp ctx op hctx hIn hasParent
    apply cast (a := harray)
    congr
    ext use
    rw [OpOperandPtr.get!_detachOp]
  case blockDefUseChains =>
    intro block hblock
    have ⟨array, harray⟩ := wf.blockDefUseChains block (by grind)
    refine ⟨array, ?_⟩
    apply BlockPtr.defUse_detachOp ctx op hctx hIn hasParent
    apply cast (a := harray)
    congr
    ext use
    rw [BlockOperandPtr.get!_detachOp]
  case opChain =>
    intro block' hBlock'
    have ⟨array', harray'⟩ := wf.opChain block' (by grind)
    let block := ((op.getParent ctx hIn).toOption.get hasParent).spec
    by_cases hEq : block = block'
    · subst block'
      exact ⟨array'.erase op.spec,
        BlockPtr.opChain_detachOp_self ctx op hctx hIn hasParent harray' hParent⟩
    · have ⟨array, harray⟩ := wf.opChain block (by grind)
      exact ⟨array', BlockPtr.opChain_detachOp_other ctx op hctx hIn hasParent
        harray' harray hParent (Ne.symm hEq)⟩
  case blockChain =>
    intro region hregion
    have ⟨array, harray⟩ := wf.blockChain region (by grind)
    exact ⟨array, RegionPtr.blockChain_detachOp ctx op hctx hIn hasParent harray⟩
  case operations =>
    intro op' hop'
    have hopOld : op'.InBounds ctx.spec := by grind
    have hWf := wf.operations op' hopOld
    constructor
    case inBounds => grind
    case result_index =>
      intro i hi
      have hi' : i < op'.getNumResults! ctx.spec := by simpa using hi
      simpa using hWf.result_index i hi'
    case result_owner =>
      intro i hi
      have hi' : i < op'.getNumResults! ctx.spec := by simpa using hi
      simpa using hWf.result_owner i hi'
    case operand_owner =>
      intro i hi
      rw [Rewriter.detachOp_preserves_numOperands hctx] at hi
      simpa using hWf.operand_owner i hi
    case blockOperand_owner =>
      intro i hi
      rw [Rewriter.detachOp_preserves_numSuccessors hctx] at hi
      simpa using hWf.blockOperand_owner i hi
    case regions_unique =>
      intro i hi j hj hne
      have hi' : i < op'.getNumRegions! ctx.spec := by simpa using hi
      have hj' : j < op'.getNumRegions! ctx.spec := by simpa using hj
      intro heq
      have heqBang : op'.getRegion!
          (Rewriter.detachOp ctx op hctx hIn hasParent).spec i =
          op'.getRegion! (Rewriter.detachOp ctx op hctx hIn hasParent).spec j := by
        rw [OperationPtr.getRegion!_eq_getRegion
          (ctx := (Rewriter.detachOp ctx op hctx hIn hasParent).spec)
          (op := op') (index := i) (hin := hop') (iInBounds := by grind),
          OperationPtr.getRegion!_eq_getRegion
          (ctx := (Rewriter.detachOp ctx op hctx hIn hasParent).spec)
          (op := op') (index := j) (hin := hop') (iInBounds := by grind)]
        exact heq
      rw [OperationPtr.getRegion!_detachOp, OperationPtr.getRegion!_detachOp] at heqBang
      apply hWf.regions_unique i hi' j hj' hne
      rw [← OperationPtr.getRegion!_eq_getRegion
          (ctx := ctx.spec) (op := op') (index := i) (hin := hopOld)
          (iInBounds := by grind),
        ← OperationPtr.getRegion!_eq_getRegion
          (ctx := ctx.spec) (op := op') (index := j) (hin := hopOld)
          (iInBounds := by grind)]
      exact heqBang
    case region_parent =>
      intro region regionInBounds
      have regionOld : region.InBounds ctx.spec := by grind
      simpa using hWf.region_parent region regionOld
    case opChain_of_parent_none =>
      have ⟨chain, hchain⟩ := wf.opChain
        ((op.getParent ctx hIn).toOption.get hasParent).spec (by grind)
      intro hnone
      rw [OperationPtr.prev!_detachOp, OperationPtr.next!_detachOp]
      by_cases heq : op' = op.spec
      · subst op'
        have hPrevNe := BlockPtr.OpChain.prev_ne_self _ _ _ _ _ hchain hIn.ib
          (by simp) hParent
        have hNextNe := BlockPtr.OpChain.next_ne_self _ _ _ _ _ hchain hIn.ib
          (by simp) hParent
        simp [Ne.symm hNextNe, Ne.symm hPrevNe]
      · have hOldParent : (op'.get! ctx.spec).parent = none := by
          rw [OperationPtr.parent!_detachOp] at hnone
          simpa [heq] using hnone
        have hold := hWf.opChain_of_parent_none hOldParent
        grind [BlockPtr.OpChain_next_ne, BlockPtr.OpChain_prev_ne]
    case capResults_eq_numResults => simpa using hWf.capResults_eq_numResults
    case capRegions_eq_numRegions => simpa using hWf.capRegions_eq_numRegions
    case capOperands_eq_numOperands =>
      simpa only [Rewriter.detachOp_preserves_capOperands hctx,
        Rewriter.detachOp_preserves_numOperands hctx] using hWf.capOperands_eq_numOperands
    case capBlockOperands_eq_numSuccessors =>
      simpa only [Rewriter.detachOp_preserves_capBlockOperands hctx,
        Rewriter.detachOp_preserves_numSuccessors hctx] using
          hWf.capBlockOperands_eq_numSuccessors
  case blocks =>
    intro block hblock
    have hWf := wf.blocks block (by grind)
    apply BlockPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind
  case regions =>
    intro region hregion
    have hWf := wf.regions region (by grind)
    apply RegionPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Rewriter.detachOpIfAttached_WellFormed
    (ctx : Sim.IRContext OpInfo)
    (wf : ctx.spec.WellFormed missingOperands missingSuccessors)
    (hctx : ctx.spec.FieldsInBounds) (op : Sim.OperationPtr)
    (hIn : op.InBounds ctx) :
    (Rewriter.detachOpIfAttached ctx op hctx hIn).spec.WellFormed
      missingOperands missingSuccessors := by
  simp only [Rewriter.detachOpIfAttached_def, Rewriter.detachOpIfAttachedSim]
  split
  · apply Rewriter.detachOp_WellFormed <;> assumption
  · exact wf

theorem Rewriter.detachOperands_wellFormed
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : op.InBounds ctx)
    (hCap : (op.spec.get! ctx.spec).capOperands =
      op.spec.getNumOperands! ctx.spec)
    (wf : ctx.spec.WellFormed missingOperands missingSuccessors)
    (hMissing : ∀ i, OpOperandPtr.mk op.spec i ∉ missingOperands) :
    (Rewriter.detachOperands ctx op hCtx hOp hCap).spec.WellFormed
      (missingOperands.insertMany
        ((0...op.spec.getNumOperands! ctx.spec).toList.map
          (fun i => OpOperandPtr.mk op.spec i)))
      missingSuccessors := by
  let numOperands := op.getNumOperands ctx hOp
  have hNumLt : op.spec.getNumOperands! ctx.spec < UInt64.size := by
    have henc := ctx.sim.encoding_op op.spec hOp.ib
    rw [← hCap, henc.numOperands]
    exact UInt64.toNat_lt _
  have hNum : numOperands.toNat = op.spec.getNumOperands! ctx.spec := by
    dsimp [numOperands]
    rw [Sim.OperationPtr.getNumOperands_eq_getNumOperands! ctx op hOp,
      Sim.OperationPtr.getNumOperands!_spec (ctx := ctx) op (ib := hOp), hCap]
    exact UInt64.toNat_ofNat_of_lt hNumLt
  simp only [Rewriter.detachOperands_def, Rewriter.detachOperandsSim]
  split
  next hz =>
    have hZero : op.spec.getNumOperands! ctx.spec = 0 := by
      rw [← hNum]
      exact congrArg UInt64.toNat hz
    simpa [hZero] using wf
  next hz =>
    have hPos : 0 < numOperands.toNat := by
      have hneNat : numOperands.toNat ≠ 0 := by
        intro hzero
        apply hz
        apply UInt64.toNat_inj.mp
        simpa using hzero
      omega
    have hNumBound := UInt64.toNat_lt numOperands
    have hPred : (numOperands - 1).toNat = numOperands.toNat - 1 := by
      rw [UInt64.toNat_sub]
      change (2 ^ 64 - 1 + numOperands.toNat) % 2 ^ 64 = numOperands.toNat - 1
      have heq : 2 ^ 64 - 1 + numOperands.toNat =
          2 ^ 64 + (numOperands.toNat - 1) := by omega
      rw [heq, Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hwfLoop := Rewriter.detachOperands.loop_wellFormed
      (ctx := ctx) (op := op) (off := op.getOperandsOffset ctx (by grind))
      (index := numOperands - 1) (hCtx := hCtx) (hOp := hOp)
      (hIndex := by rw [hPred, hNum]; omega) (hoff := by grind) (wf := wf)
      (hMissing := by
        intro i hi
        exact hMissing i)
    have hRange :
        ((0...=(numOperands - 1).toNat).toList.map
          (fun i => OpOperandPtr.mk op.spec i)) =
        ((0...op.spec.getNumOperands! ctx.spec).toList.map
          (fun i => OpOperandPtr.mk op.spec i)) := by
      rw [Nat.toList_rcc_eq_toList_rco, hPred, hNum]
      have hSucc : op.spec.getNumOperands! ctx.spec - 1 + 1 =
          op.spec.getNumOperands! ctx.spec := by omega
      rw [hSucc]
    rw [hRange] at hwfLoop
    exact hwfLoop

theorem Rewriter.detachBlockOperands.loop_wellFormed
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr) (index : UInt64)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : op.InBounds ctx)
    (hIndex : index.toNat < op.spec.getNumSuccessors! ctx.spec)
    (wf : ctx.spec.WellFormed missingOperands missingSuccessors)
    (hMissing : ∀ i, i ≤ index.toNat →
      BlockOperandPtr.mk op.spec i ∉ missingSuccessors) :
    (Rewriter.detachBlockOperands.loop ctx op index hCtx hOp hIndex).spec.WellFormed
      missingOperands
      (missingSuccessors.insertMany
        ((0...=index.toNat).toList.map (fun i => BlockOperandPtr.mk op.spec i))) := by
  simp only [Rewriter.detachBlockOperands.loop_def]
  fun_induction Rewriter.detachBlockOperands.loopSim generalizing missingOperands missingSuccessors
  case case1 =>
    let use := op.getBlockOperandPtr _ 0 (by assumption)
    have hUseSpec : use.spec = BlockOperandPtr.mk op.spec 0 := rfl
    have hwf := Sim.IRContext.wellFormed_BlockOperandPtr_removeFromCurrent
      (use := use) (useInBounds := by
        dsimp [use]
        exact Sim.OperationPtr.getBlockOperand_inBounds op (by assumption) 0 (by assumption))
      (ctxInBounds := wf.inBounds)
      (useMissing := by simpa [hUseSpec] using hMissing 0 (by simp)) wf
    simpa [use, hUseSpec, Nat.toList_rcc_eq_singleton,
      Std.ExtHashSet.insertMany_list_singleton] using hwf
  case case2 =>
    rename_i _ _ _ currentCtx currentIndex hCtxCur hOpCur hIndexCur currentCtx' hne ih
    have hCurrentPos : 0 < currentIndex.toNat := by
      have hneNat : currentIndex.toNat ≠ 0 := by
        intro hz
        apply hne
        apply UInt64.toNat_inj.mp
        simpa using hz
      omega
    have hCurrentLt := UInt64.toNat_lt currentIndex
    have hPred : (currentIndex - 1).toNat = currentIndex.toNat - 1 := by
      rw [UInt64.toNat_sub]
      change (2 ^ 64 - 1 + currentIndex.toNat) % 2 ^ 64 = currentIndex.toNat - 1
      have heq : 2 ^ 64 - 1 + currentIndex.toNat =
          2 ^ 64 + (currentIndex.toNat - 1) := by omega
      rw [heq, Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    let use := op.getBlockOperandPtr currentCtx currentIndex (by assumption)
    have hUseSpec : use.spec = BlockOperandPtr.mk op.spec currentIndex.toNat := rfl
    have hwfRemoved := Sim.IRContext.wellFormed_BlockOperandPtr_removeFromCurrent
      (use := use) (useInBounds := by
        dsimp [use]
        exact Sim.OperationPtr.getBlockOperand_inBounds op (by assumption) currentIndex
          (by assumption))
      (ctxInBounds := wf.inBounds)
      (useMissing := by
        rw [hUseSpec]
        exact hMissing currentIndex.toNat (Nat.le_refl _)) wf
    have hwfRec := ih hwfRemoved (by
      intro i hi
      simp only [Std.ExtHashSet.mem_insert, hUseSpec, not_or]
      constructor
      · simp only [beq_iff_eq, BlockOperandPtr.mk.injEq, true_and]
        rw [hPred] at hi
        omega
      · apply hMissing i
        rw [hPred] at hi
        omega)
    have hSets :
        (missingSuccessors.insert use.spec).insertMany
            ((0...=(currentIndex - 1).toNat).toList.map
              (fun i => BlockOperandPtr.mk op.spec i)) =
          missingSuccessors.insertMany
            ((0...=currentIndex.toNat).toList.map
              (fun i => BlockOperandPtr.mk op.spec i)) := by
      rw [hUseSpec, Nat.toList_rcc_eq_toList_rco, hPred]
      have hSucc : currentIndex.toNat - 1 + 1 = currentIndex.toNat := by omega
      rw [hSucc, Nat.toList_rcc_eq_append (Nat.zero_le _), List.map_append,
        List.map_singleton, Std.ExtHashSet.insertMany_append,
        Std.ExtHashSet.insertMany_list_singleton,
        Std.ExtHashSet.insertMany_list_insert_comm]
    rw [hSets] at hwfRec
    exact hwfRec

theorem Rewriter.detachBlockOperands_wellFormed
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : op.InBounds ctx)
    (hCap : (op.spec.get! ctx.spec).capBlockOperands =
      op.spec.getNumSuccessors! ctx.spec)
    (wf : ctx.spec.WellFormed missingOperands missingSuccessors)
    (hMissing : ∀ i, BlockOperandPtr.mk op.spec i ∉ missingSuccessors) :
    (Rewriter.detachBlockOperands ctx op hCtx hOp hCap).spec.WellFormed
      missingOperands
      (missingSuccessors.insertMany
        ((0...op.spec.getNumSuccessors! ctx.spec).toList.map
          (fun i => BlockOperandPtr.mk op.spec i))) := by
  let numSuccessors := op.getNumSuccessors ctx hOp
  have hNumLt : op.spec.getNumSuccessors! ctx.spec < UInt64.size := by
    have henc := ctx.sim.encoding_op op.spec hOp.ib
    rw [← hCap, henc.numBlockOperands]
    exact UInt64.toNat_lt _
  have hNum : numSuccessors.toNat = op.spec.getNumSuccessors! ctx.spec := by
    dsimp [numSuccessors]
    rw [Sim.OperationPtr.getNumSuccessors_eq_getNumSuccessors! ctx op hOp,
      Sim.OperationPtr.getNumSuccessors!_spec (ctx := ctx) op (ib := hOp), hCap]
    exact UInt64.toNat_ofNat_of_lt hNumLt
  simp only [Rewriter.detachBlockOperands_def, Rewriter.detachBlockOperandsSim]
  split
  next hz =>
    have hZero : op.spec.getNumSuccessors! ctx.spec = 0 := by
      rw [← hNum]
      exact congrArg UInt64.toNat hz
    simpa [hZero] using wf
  next hz =>
    have hPos : 0 < numSuccessors.toNat := by
      have hneNat : numSuccessors.toNat ≠ 0 := by
        intro hzero
        apply hz
        apply UInt64.toNat_inj.mp
        simpa using hzero
      omega
    have hNumBound := UInt64.toNat_lt numSuccessors
    have hPred : (numSuccessors - 1).toNat = numSuccessors.toNat - 1 := by
      rw [UInt64.toNat_sub]
      change (2 ^ 64 - 1 + numSuccessors.toNat) % 2 ^ 64 = numSuccessors.toNat - 1
      have heq : 2 ^ 64 - 1 + numSuccessors.toNat =
          2 ^ 64 + (numSuccessors.toNat - 1) := by omega
      rw [heq, Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hwfLoop := Rewriter.detachBlockOperands.loop_wellFormed
      (ctx := ctx) (op := op) (index := numSuccessors - 1)
      (hCtx := hCtx) (hOp := hOp)
      (hIndex := by rw [hPred, hNum]; omega) (wf := wf)
      (hMissing := by
        intro i hi
        exact hMissing i)
    have hRange :
        ((0...=(numSuccessors - 1).toNat).toList.map
          (fun i => BlockOperandPtr.mk op.spec i)) =
        ((0...op.spec.getNumSuccessors! ctx.spec).toList.map
          (fun i => BlockOperandPtr.mk op.spec i)) := by
      rw [Nat.toList_rcc_eq_toList_rco, hPred, hNum]
      have hSucc : op.spec.getNumSuccessors! ctx.spec - 1 + 1 =
          op.spec.getNumSuccessors! ctx.spec := by omega
      rw [hSucc]
    rw [hRange] at hwfLoop
    exact hwfLoop

theorem OpResultPtr.firstUse!_OpOperandPtr_removeFromCurrent_eq_none_of_firstUse!_eq_none
    (ctx : Sim.IRContext OpInfo) (operand : Sim.OpOperandPtr)
    (operandIn : operand.InBounds ctx) (ctxIn : ctx.spec.FieldsInBounds)
    (result : Veir.OpResultPtr)
    (hctx : ctx.spec.WellFormed missingUses missingSuccessors)
    (hmissing : operand.spec ∉ missingUses)
    (resultIn : result.InBounds ctx.spec)
    (h : (result.get! ctx.spec).firstUse = none) :
    (result.get! (operand.removeFromCurrent ctx operandIn ctxIn).spec).firstUse = none := by
  have ⟨useArray, hUseArray⟩ := hctx.valueDefUseChains (result : ValuePtr) (by grind)
  have ⟨useArray', hUseArray'⟩ := hctx.valueDefUseChains
    (operand.spec.get! ctx.spec).value (by grind)
  have hne : (result : ValuePtr) ≠ (operand.spec.get! ctx.spec).value := by
    grind [ValuePtr.DefUse]
  have hEmpty : useArray = #[] := by
    grind [ValuePtr.DefUse.getFirstUse!_none_iff hUseArray]
  have operandInArray : operand.spec ∈ useArray' := by
    grind [ValuePtr.DefUse]
  have hPreserved := Sim.ValuePtr.defUse_removeFromCurrent_other hne
    (useIb := operandIn) hUseArray hUseArray'
    (hvalue := operandInArray) (ctxInBounds := hctx.inBounds)
  grind [ValuePtr.DefUse.getFirstUse!_none_iff hPreserved]

theorem OpResultPtr.firstUse!_detachOperands_loop_eq_none_of_firstUse!_eq_none
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (off : Int64) (index : UInt64) (result : Veir.OpResultPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumOperands! ctx.spec)
    (hoff : off = Buffed.Operation.Offsets.operands operation.spec ctx.spec)
    (hctx : ctx.spec.WellFormed missingUses missingSuccessors)
    (hMissingUses : ∀ i, i ≤ index.toNat →
      OpOperandPtr.mk operation.spec i ∉ missingUses)
    (resIn : result.InBounds ctx.spec)
    (h : (result.get! ctx.spec).firstUse = none) :
    (result.get! (Rewriter.detachOperands.loop ctx operation off index
      hCtx hOp hIndex hoff).spec).firstUse = none := by
  simp only [Rewriter.detachOperands.loop_def]
  fun_induction Rewriter.detachOperands.loopSim generalizing missingUses missingSuccessors
  case case1 =>
    let use := operation.getOperandPtrAt _ off 0 (by assumption) (by assumption)
    have hUseSpec : use.spec = OpOperandPtr.mk operation.spec 0 := rfl
    apply OpResultPtr.firstUse!_OpOperandPtr_removeFromCurrent_eq_none_of_firstUse!_eq_none
      (ctx := _) (operand := use) (result := result)
      (operandIn := by
        dsimp [use]
        rw [Sim.OperationPtr.getOperandPtrAt_eq_getOperandPtr]
        exact Sim.OperationPtr.getOpOperand_inBounds operation (by assumption) 0
          (by assumption))
      (ctxIn := hctx.inBounds) hctx
    · rw [hUseSpec]
      exact hMissingUses 0 (by simp)
    · exact resIn
    · exact h
  case case2 =>
    rename_i _ _ _ currentCtx currentIndex hCtxCur hOpCur hIndexCur hoffCur currentCtx' hne ih
    have hCurrentPos : 0 < currentIndex.toNat := by
      have hneNat : currentIndex.toNat ≠ 0 := by
        intro hz
        apply hne
        apply UInt64.toNat_inj.mp
        simpa using hz
      omega
    have hCurrentLt := UInt64.toNat_lt currentIndex
    have hPred : (currentIndex - 1).toNat = currentIndex.toNat - 1 := by
      rw [UInt64.toNat_sub]
      change (2 ^ 64 - 1 + currentIndex.toNat) % 2 ^ 64 = currentIndex.toNat - 1
      have heq : 2 ^ 64 - 1 + currentIndex.toNat =
          2 ^ 64 + (currentIndex.toNat - 1) := by omega
      rw [heq, Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    let use := operation.getOperandPtrAt currentCtx off currentIndex
      (by assumption) (by assumption)
    have hUseSpec : use.spec = OpOperandPtr.mk operation.spec currentIndex.toNat := rfl
    have hUseIn : use.InBounds currentCtx := by
      dsimp [use]
      rw [Sim.OperationPtr.getOperandPtrAt_eq_getOperandPtr]
      exact Sim.OperationPtr.getOpOperand_inBounds operation (by assumption) currentIndex
        (by assumption)
    have hwfRemoved := Sim.IRContext.wellFormed_OpOperandPtr_removeFromCurrent
      (use := use) (useInBounds := hUseIn) (ctxInBounds := hctx.inBounds)
      (useMissing := by
        rw [hUseSpec]
        exact hMissingUses currentIndex.toNat (Nat.le_refl _)) hctx
    have hNoneRemoved :=
      OpResultPtr.firstUse!_OpOperandPtr_removeFromCurrent_eq_none_of_firstUse!_eq_none
        (ctx := currentCtx) (operand := use) (result := result)
        (operandIn := hUseIn) (ctxIn := hctx.inBounds) hctx
        (by rw [hUseSpec]; exact hMissingUses currentIndex.toNat (Nat.le_refl _))
        resIn h
    apply ih hwfRemoved
    · intro i hi
      simp only [Std.ExtHashSet.mem_insert, hUseSpec, not_or]
      constructor
      · simp only [beq_iff_eq, OpOperandPtr.mk.injEq, true_and]
        rw [hPred] at hi
        omega
      · apply hMissingUses i
        rw [hPred] at hi
        omega
    · grind
    · exact hNoneRemoved

theorem OpResultPtr.firstUse!_detachOperands_eq_none_of_firstUse!_eq_none
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (result : Veir.OpResultPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capOperands =
      operation.spec.getNumOperands! ctx.spec)
    (hctx : ctx.spec.WellFormed missingUses missingSuccessors)
    (hMissingUses : ∀ i, OpOperandPtr.mk operation.spec i ∉ missingUses)
    (resIn : result.InBounds ctx.spec)
    (h : (result.get! ctx.spec).firstUse = none) :
    (result.get! (Rewriter.detachOperands ctx operation hCtx hOp hCap).spec).firstUse = none := by
  let numOperands := operation.getNumOperands ctx hOp
  have hNumLt : operation.spec.getNumOperands! ctx.spec < UInt64.size := by
    have henc := ctx.sim.encoding_op operation.spec hOp.ib
    rw [← hCap, henc.numOperands]
    exact UInt64.toNat_lt _
  have hNum : numOperands.toNat = operation.spec.getNumOperands! ctx.spec := by
    dsimp [numOperands]
    rw [Sim.OperationPtr.getNumOperands_eq_getNumOperands! ctx operation hOp,
      Sim.OperationPtr.getNumOperands!_spec (ctx := ctx) operation (ib := hOp), hCap]
    exact UInt64.toNat_ofNat_of_lt hNumLt
  simp only [Rewriter.detachOperands_def, Rewriter.detachOperandsSim]
  split
  · exact h
  · apply OpResultPtr.firstUse!_detachOperands_loop_eq_none_of_firstUse!_eq_none
      (hctx := hctx) (hMissingUses := by intro i hi; exact hMissingUses i)
      (resIn := resIn) (h := h)

@[simp]
theorem OpResultPtr.firstUse!_detachBlockOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (index : UInt64) (result : Veir.OpResultPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumSuccessors! ctx.spec) :
    (result.get! (Rewriter.detachBlockOperands.loop ctx operation index
      hCtx hOp hIndex).spec).firstUse = (result.get! ctx.spec).firstUse := by
  simp only [Rewriter.detachBlockOperands.loop_def]
  fun_induction Rewriter.detachBlockOperands.loopSim
  case case1 =>
    rename_i _ _ _ currentCtx hCtxCur hOpCur hIndexCur currentCtx'
    dsimp [currentCtx']
    rw [Sim.OpResultPtr.get!_BlockOperandPtr_removeFromCurrent]
  case case2 =>
    rename_i _ _ _ currentCtx currentIndex hCtxCur hOpCur hIndexCur currentCtx' hne ih
    rw [ih]
    dsimp [currentCtx']
    rw [Sim.OpResultPtr.get!_BlockOperandPtr_removeFromCurrent]

@[simp]
theorem OpResultPtr.firstUse!_detachBlockOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (result : Veir.OpResultPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capBlockOperands =
      operation.spec.getNumSuccessors! ctx.spec) :
    (result.get! (Rewriter.detachBlockOperands ctx operation hCtx hOp hCap).spec).firstUse =
      (result.get! ctx.spec).firstUse := by
  simp only [Rewriter.detachBlockOperands_def, Rewriter.detachBlockOperandsSim]
  split
  · rfl
  · apply OpResultPtr.firstUse!_detachBlockOperands_loop

@[simp]
theorem ValuePtr.getFirstUse!_detachOpIfAttached
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (value : Veir.ValuePtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx) :
    value.getFirstUse! (Rewriter.detachOpIfAttached ctx operation hCtx hOp).spec =
      value.getFirstUse! ctx.spec := by
  simp only [Rewriter.detachOpIfAttached_def, Rewriter.detachOpIfAttachedSim]
  split
  · apply ValuePtr.getFirstUse!_detachOp
  · rfl

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOpIfAttached
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx) :
    op'.getNumResults! (Rewriter.detachOpIfAttached ctx operation hCtx hOp).spec =
      op'.getNumResults! ctx.spec := by
  simp only [Rewriter.detachOpIfAttached_def, Rewriter.detachOpIfAttachedSim]
  split
  · apply OperationPtr.getNumResults!_detachOp
  · rfl

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (off : Int64) (index : UInt64) (op' : Veir.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumOperands! ctx.spec)
    (hoff : off = Buffed.Operation.Offsets.operands operation.spec ctx.spec) :
    op'.getNumResults! (Rewriter.detachOperands.loop ctx operation off index
      hCtx hOp hIndex hoff).spec = op'.getNumResults! ctx.spec := by
  simp only [Rewriter.detachOperands.loop_def]
  fun_induction Rewriter.detachOperands.loopSim
  case case1 =>
    rename_i _ _ _ currentCtx hCtxCur hOpCur hIndexCur hoffCur currentCtx'
    dsimp [currentCtx']
    rw [Sim.OperationPtr.getNumResults!_OpOperandPtr_removeFromCurrent]
  case case2 =>
    rename_i _ _ _ currentCtx currentIndex hCtxCur hOpCur hIndexCur hoffCur currentCtx' hne ih
    rw [ih]
    dsimp [currentCtx']
    rw [Sim.OperationPtr.getNumResults!_OpOperandPtr_removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capOperands =
      operation.spec.getNumOperands! ctx.spec) :
    op'.getNumResults! (Rewriter.detachOperands ctx operation hCtx hOp hCap).spec =
      op'.getNumResults! ctx.spec := by
  simp only [Rewriter.detachOperands_def, Rewriter.detachOperandsSim]
  split
  · rfl
  · apply OperationPtr.getNumResults!_detachOperands_loop

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachBlockOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (index : UInt64) (op' : Veir.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumSuccessors! ctx.spec) :
    op'.getNumResults! (Rewriter.detachBlockOperands.loop ctx operation index
      hCtx hOp hIndex).spec = op'.getNumResults! ctx.spec := by
  simp only [Rewriter.detachBlockOperands.loop_def]
  fun_induction Rewriter.detachBlockOperands.loopSim
  case case1 =>
    rename_i _ _ _ currentCtx hCtxCur hOpCur hIndexCur currentCtx'
    dsimp [currentCtx']
    rw [Sim.OperationPtr.getNumResults!_BlockOperandPtr_removeFromCurrent]
  case case2 =>
    rename_i _ _ _ currentCtx currentIndex hCtxCur hOpCur hIndexCur currentCtx' hne ih
    rw [ih]
    dsimp [currentCtx']
    rw [Sim.OperationPtr.getNumResults!_BlockOperandPtr_removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachBlockOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capBlockOperands =
      operation.spec.getNumSuccessors! ctx.spec) :
    op'.getNumResults! (Rewriter.detachBlockOperands ctx operation hCtx hOp hCap).spec =
      op'.getNumResults! ctx.spec := by
  simp only [Rewriter.detachBlockOperands_def, Rewriter.detachBlockOperandsSim]
  split
  · rfl
  · apply OperationPtr.getNumResults!_detachBlockOperands_loop

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (off : Int64) (index : UInt64) (op' : Veir.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumOperands! ctx.spec)
    (hoff : off = Buffed.Operation.Offsets.operands operation.spec ctx.spec) :
    op'.getNumOperands! (Rewriter.detachOperands.loop ctx operation off index
      hCtx hOp hIndex hoff).spec = op'.getNumOperands! ctx.spec := by
  simp only [Rewriter.detachOperands.loop_def]
  fun_induction Rewriter.detachOperands.loopSim <;>
    grind [Sim.OperationPtr.getNumOperands!_OpOperandPtr_removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capOperands =
      operation.spec.getNumOperands! ctx.spec) :
    op'.getNumOperands! (Rewriter.detachOperands ctx operation hCtx hOp hCap).spec =
      op'.getNumOperands! ctx.spec := by
  simp only [Rewriter.detachOperands_def, Rewriter.detachOperandsSim]
  split
  · rfl
  · apply OperationPtr.getNumOperands!_detachOperands_loop

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachBlockOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (index : UInt64) (op' : Veir.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumSuccessors! ctx.spec) :
    op'.getNumOperands! (Rewriter.detachBlockOperands.loop ctx operation index
      hCtx hOp hIndex).spec = op'.getNumOperands! ctx.spec := by
  simp only [Rewriter.detachBlockOperands.loop_def]
  fun_induction Rewriter.detachBlockOperands.loopSim <;>
    grind [Sim.OperationPtr.getNumOperands!_BlockOperandPtr_removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachBlockOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capBlockOperands =
      operation.spec.getNumSuccessors! ctx.spec) :
    op'.getNumOperands! (Rewriter.detachBlockOperands ctx operation hCtx hOp hCap).spec =
      op'.getNumOperands! ctx.spec := by
  simp only [Rewriter.detachBlockOperands_def, Rewriter.detachBlockOperandsSim]
  split
  · rfl
  · apply OperationPtr.getNumOperands!_detachBlockOperands_loop

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachBlockOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (index : UInt64) (op' : Veir.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumSuccessors! ctx.spec) :
    op'.getNumSuccessors! (Rewriter.detachBlockOperands.loop ctx operation index
      hCtx hOp hIndex).spec = op'.getNumSuccessors! ctx.spec := by
  simp only [Rewriter.detachBlockOperands.loop_def]
  fun_induction Rewriter.detachBlockOperands.loopSim <;>
    grind [Sim.OperationPtr.getNumSuccessors!_BlockOperandPtr_removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachBlockOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capBlockOperands =
      operation.spec.getNumSuccessors! ctx.spec) :
    op'.getNumSuccessors! (Rewriter.detachBlockOperands ctx operation hCtx hOp hCap).spec =
      op'.getNumSuccessors! ctx.spec := by
  simp only [Rewriter.detachBlockOperands_def, Rewriter.detachBlockOperandsSim]
  split
  · rfl
  · apply OperationPtr.getNumSuccessors!_detachBlockOperands_loop

@[simp]
theorem OperationPtr.parent!_detachOpIfAttached_self
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx) :
    (operation.spec.get! (Rewriter.detachOpIfAttached ctx operation hCtx hOp).spec).parent =
      none := by
  simp only [Rewriter.detachOpIfAttached_def, Rewriter.detachOpIfAttachedSim]
  split
  · rw [OperationPtr.parent!_detachOp]
    simp
  · have hParentIB : (operation.getParent ctx hOp).InBounds ctx := by grind
    have hParentSpec := Sim.OperationPtr.getParent_spec ctx operation hOp
    grind [Sim.OptionBlockPtr.toOption_none_iff_spec_none,
      OperationPtr.get!_eq_get]

@[simp]
theorem OperationPtr.parent!_detachOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (off : Int64) (index : UInt64) (op' : Veir.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumOperands! ctx.spec)
    (hoff : off = Buffed.Operation.Offsets.operands operation.spec ctx.spec) :
    (op'.get! (Rewriter.detachOperands.loop ctx operation off index
      hCtx hOp hIndex hoff).spec).parent = (op'.get! ctx.spec).parent := by
  simp only [Rewriter.detachOperands.loop_def]
  fun_induction Rewriter.detachOperands.loopSim <;>
    grind [Sim.OperationPtr.parent!_OpOperandPtr_removeFromCurrent]

@[simp]
theorem OperationPtr.parent!_detachOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capOperands =
      operation.spec.getNumOperands! ctx.spec) :
    (op'.get! (Rewriter.detachOperands ctx operation hCtx hOp hCap).spec).parent =
      (op'.get! ctx.spec).parent := by
  simp only [Rewriter.detachOperands_def, Rewriter.detachOperandsSim]
  split
  · rfl
  · apply OperationPtr.parent!_detachOperands_loop

@[simp]
theorem OperationPtr.parent!_detachBlockOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (index : UInt64) (op' : Veir.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumSuccessors! ctx.spec) :
    (op'.get! (Rewriter.detachBlockOperands.loop ctx operation index
      hCtx hOp hIndex).spec).parent = (op'.get! ctx.spec).parent := by
  simp only [Rewriter.detachBlockOperands.loop_def]
  fun_induction Rewriter.detachBlockOperands.loopSim <;>
    grind [Sim.OperationPtr.parent!_BlockOperandPtr_removeFromCurrent]

@[simp]
theorem OperationPtr.parent!_detachBlockOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capBlockOperands =
      operation.spec.getNumSuccessors! ctx.spec) :
    (op'.get! (Rewriter.detachBlockOperands ctx operation hCtx hOp hCap).spec).parent =
      (op'.get! ctx.spec).parent := by
  simp only [Rewriter.detachBlockOperands_def, Rewriter.detachBlockOperandsSim]
  split
  · rfl
  · apply OperationPtr.parent!_detachBlockOperands_loop

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (off : Int64) (index : UInt64) (op' : Veir.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumOperands! ctx.spec)
    (hoff : off = Buffed.Operation.Offsets.operands operation.spec ctx.spec) :
    op'.getNumRegions! (Rewriter.detachOperands.loop ctx operation off index
      hCtx hOp hIndex hoff).spec = op'.getNumRegions! ctx.spec := by
  simp only [Rewriter.detachOperands.loop_def]
  fun_induction Rewriter.detachOperands.loopSim <;>
    grind [Sim.OperationPtr.getNumRegions!_OpOperandPtr_removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capOperands =
      operation.spec.getNumOperands! ctx.spec) :
    op'.getNumRegions! (Rewriter.detachOperands ctx operation hCtx hOp hCap).spec =
      op'.getNumRegions! ctx.spec := by
  simp only [Rewriter.detachOperands_def, Rewriter.detachOperandsSim]
  split
  · rfl
  · apply OperationPtr.getNumRegions!_detachOperands_loop

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachBlockOperands_loop
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (index : UInt64) (op' : Veir.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : operation.InBounds ctx)
    (hIndex : index.toNat < operation.spec.getNumSuccessors! ctx.spec) :
    op'.getNumRegions! (Rewriter.detachBlockOperands.loop ctx operation index
      hCtx hOp hIndex).spec = op'.getNumRegions! ctx.spec := by
  simp only [Rewriter.detachBlockOperands.loop_def]
  fun_induction Rewriter.detachBlockOperands.loopSim <;>
    grind [Sim.OperationPtr.getNumRegions!_BlockOperandPtr_removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachBlockOperands
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx)
    (hCap : (operation.spec.get! ctx.spec).capBlockOperands =
      operation.spec.getNumSuccessors! ctx.spec) :
    op'.getNumRegions! (Rewriter.detachBlockOperands ctx operation hCtx hOp hCap).spec =
      op'.getNumRegions! ctx.spec := by
  simp only [Rewriter.detachBlockOperands_def, Rewriter.detachBlockOperandsSim]
  split
  · rfl
  · apply OperationPtr.getNumRegions!_detachBlockOperands_loop

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOpIfAttached
    (ctx : Sim.IRContext OpInfo) (operation : Sim.OperationPtr)
    (op' : Veir.OperationPtr) (hCtx : ctx.spec.FieldsInBounds)
    (hOp : operation.InBounds ctx) :
    op'.getNumRegions! (Rewriter.detachOpIfAttached ctx operation hCtx hOp).spec =
      op'.getNumRegions! ctx.spec := by
  simp only [Rewriter.detachOpIfAttached_def, Rewriter.detachOpIfAttachedSim]
  split
  · apply OperationPtr.getNumRegions!_detachOp
  · rfl

theorem Rewriter.eraseOpDeallocatedSpec_wellFormed
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (wf : ctx.spec.WellFormed)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : op.InBounds ctx)
    (hOpers : (op.spec.get! ctx.spec).capOperands =
      op.spec.getNumOperands! ctx.spec)
    (hBlOpers : (op.spec.get! ctx.spec).capBlockOperands =
      op.spec.getNumSuccessors! ctx.spec)
    (noRegions : op.spec.getNumRegions! ctx.spec = 0)
    (noUses : op.spec.hasUses! ctx.spec = false) :
    let ctx₀ := Rewriter.detachOpIfAttached ctx op hCtx hOp
    let ctx₁ := Rewriter.detachOperands ctx₀ op (by grind) (by grind [generic_ptr_grind])
      (by grind)
    let ctx₂ := Rewriter.detachBlockOperands ctx₁ op (by grind)
      (by grind [generic_ptr_grind]) (by grind [detachOperands_def, detachOperandsSim])
    ∀ hOpAfter : op.spec.InBounds ctx₂.spec,
      (op.spec.dealloc ctx₂.spec hOpAfter).WellFormed := by
  dsimp only
  let ctx₀ := Rewriter.detachOpIfAttached ctx op hCtx hOp
  have wf₀ : ctx₀.spec.WellFormed := by
    exact Rewriter.detachOpIfAttached_WellFormed ctx wf hCtx op hOp
  have hOp₀ : op.InBounds ctx₀ := by grind [generic_ptr_grind]
  have hCap₀ : (op.spec.get! ctx₀.spec).capOperands =
      op.spec.getNumOperands! ctx₀.spec := by
    exact (wf₀.operations op.spec hOp₀.ib).capOperands_eq_numOperands
  let ctx₁ := Rewriter.detachOperands ctx₀ op wf₀.inBounds hOp₀ hCap₀
  have wf₁ : ctx₁.spec.WellFormed
      ((∅ : Std.ExtHashSet OpOperandPtr).insertMany
        ((0...op.spec.getNumOperands! ctx₀.spec).toList.map
          (fun i => OpOperandPtr.mk op.spec i))) (∅ : Std.ExtHashSet BlockOperandPtr) := by
    exact Rewriter.detachOperands_wellFormed ctx₀ op wf₀.inBounds hOp₀ hCap₀
      wf₀ (by simp)
  have hOp₁ : op.InBounds ctx₁ := by grind [generic_ptr_grind]
  have hCap₁ : (op.spec.get! ctx₁.spec).capBlockOperands =
      op.spec.getNumSuccessors! ctx₁.spec := by
    exact (wf₁.operations op.spec hOp₁.ib).capBlockOperands_eq_numSuccessors
  let ctx₂ := Rewriter.detachBlockOperands ctx₁ op wf₁.inBounds hOp₁ hCap₁
  have wf₂ : ctx₂.spec.WellFormed
      ((∅ : Std.ExtHashSet OpOperandPtr).insertMany
        ((0...op.spec.getNumOperands! ctx₀.spec).toList.map
          (fun i => OpOperandPtr.mk op.spec i)))
      ((∅ : Std.ExtHashSet BlockOperandPtr).insertMany
        ((0...op.spec.getNumSuccessors! ctx₁.spec).toList.map
          (fun i => BlockOperandPtr.mk op.spec i))) := by
    exact Rewriter.detachBlockOperands_wellFormed ctx₁ op wf₁.inBounds hOp₁ hCap₁
      wf₁ (by simp)
  have wfMissing : ctx₂.spec.WellFormed
      (Std.ExtHashSet.fromOperands ctx₂.spec op.spec)
      (Std.ExtHashSet.fromSuccessors ctx₂.spec op.spec) := by
    apply cast (a := wf₂)
    congr
    · simp only [Std.ExtHashSet.fromOperands,
        Std.ExtHashSet.insertMany_empty_eq_ofList, OperationPtr.getOpOperand_def]
      congr 3
      grind [detachOperands_def, detachOperandsSim]
    · simp only [Std.ExtHashSet.fromSuccessors,
        Std.ExtHashSet.insertMany_empty_eq_ofList, OperationPtr.getBlockOperand_def]
      congr 3
      grind [detachOperands_def, detachOperandsSim]
  have hOp₂ : op.InBounds ctx₂ := by grind [generic_ptr_grind]
  have hNoUses₂ : ¬ op.spec.hasUses ctx₂.spec := by
    simp only [← OperationPtr.hasUses!_eq_hasUses (hin := hOp₂.ib), Bool.not_eq_true]
    rw [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
    intro index hindex
    simp only [ValuePtr.hasUses!_def, ValuePtr.getFirstUse!_opResult_eq,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    rw [OpResultPtr.firstUse!_detachBlockOperands]
    apply OpResultPtr.firstUse!_detachOperands_eq_none_of_firstUse!_eq_none
      (ctx := ctx₀) (operation := op) (result := op.spec.getResult index)
      (hctx := wf₀) (hMissingUses := by simp)
    · grind
    · have hindex₀ : index < op.spec.getNumResults! ctx.spec := by
        simpa only [ctx₂, OperationPtr.getNumResults!_detachBlockOperands,
          ctx₁, OperationPtr.getNumResults!_detachOperands,
          ctx₀, OperationPtr.getNumResults!_detachOpIfAttached] using hindex
      have hNoUses :=
        (OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false).mp
          noUses index hindex₀
      simp only [ValuePtr.hasUses!_def, ValuePtr.getFirstUse!_opResult_eq,
        Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hNoUses
      change (ValuePtr.opResult (op.spec.getResult index)).getFirstUse! ctx₀.spec = none
      exact (ValuePtr.getFirstUse!_detachOpIfAttached ctx op
        (ValuePtr.opResult (op.spec.getResult index)) hCtx hOp).trans hNoUses
  intro hOpAfter
  apply IRContext.wellFormed_OperationPtr_dealloc wfMissing hNoUses₂
  · simp only [ctx₂, OperationPtr.parent!_detachBlockOperands,
      ctx₁, OperationPtr.parent!_detachOperands,
      ctx₀, OperationPtr.parent!_detachOpIfAttached_self]
  · simpa only [ctx₂, OperationPtr.getNumRegions!_detachBlockOperands,
      ctx₁, OperationPtr.getNumRegions!_detachOperands,
      ctx₀, OperationPtr.getNumRegions!_detachOpIfAttached] using noRegions

@[grind .]
theorem Rewriter.eraseOp_deallocFieldsInBounds
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (wf : ctx.spec.WellFormed)
    (noRegions : op.spec.getNumRegions! ctx.spec = 0)
    (noUses : op.spec.hasUses! ctx.spec = false) :
    Rewriter.EraseOpDeallocFieldsInBounds ctx op := by
  intro hCtx hOp hOpers hBlOpers
  dsimp only
  intro hOpAfter
  exact (Rewriter.eraseOpDeallocatedSpec_wellFormed ctx op wf hCtx hOp
    hOpers hBlOpers noRegions noUses hOpAfter.ib).inBounds

theorem Rewriter.eraseOp_WellFormed
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (wf : ctx.spec.WellFormed)
    (hCtx : ctx.spec.FieldsInBounds) (hOp : op.InBounds ctx)
    (hOpers : (op.spec.get! ctx.spec).capOperands =
      op.spec.getNumOperands! ctx.spec)
    (hBlOpers : (op.spec.get! ctx.spec).capBlockOperands =
      op.spec.getNumSuccessors! ctx.spec)
    (noRegions : op.spec.getNumRegions! ctx.spec = 0)
    (noUses : op.spec.hasUses! ctx.spec = false)
    (hDealloc : Rewriter.EraseOpDeallocFieldsInBounds ctx op := by grind) :
    (Rewriter.eraseOp ctx op hCtx hOp hOpers hBlOpers hDealloc).spec.WellFormed := by
  simp only [Rewriter.eraseOp_def, Rewriter.eraseOpSim]
  have hOpAfter : op.InBounds
      (Rewriter.detachBlockOperands
        (Rewriter.detachOperands (Rewriter.detachOpIfAttached ctx op hCtx hOp) op
          (by grind) (by grind [generic_ptr_grind]) (by grind)) op
        (by grind) (by grind [generic_ptr_grind])
        (by grind [detachOperands_def, detachOperandsSim])) := by
    apply (Sim.GenericPtr.iff_operation op).mp
    rw [Rewriter.detachBlockOperands_inBounds]
    rw [Rewriter.detachOperands_inBounds]
    rw [Rewriter.detachOpIfAttached_inBounds]
    exact (Sim.GenericPtr.iff_operation op).mpr hOp
  exact Rewriter.eraseOpDeallocatedSpec_wellFormed ctx op wf hCtx hOp
    hOpers hBlOpers noRegions noUses hOpAfter.ib

end Veir
