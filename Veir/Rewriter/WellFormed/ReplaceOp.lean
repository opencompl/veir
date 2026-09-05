module

public import Veir.Rewriter.Basic
public import Veir.Rewriter.LinkedList.WellFormed
public import Veir.Rewriter.WellFormed.EraseOp
public import Veir.IR.Buffed.RawAccessorFootprints

public section

namespace Veir

set_option maxRecDepth 4000
set_option maxHeartbeats 500000

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
variable {ctx : Sim.IRContext OpInfo}

theorem Sim.OperationPtr.getResultPtr_impl_ne_of_spec_ne
    (fromOp toOp : Sim.OperationPtr) (fromIndex toIndex : UInt64)
    (fromIn : fromOp.InBounds ctx) (toIn : toOp.InBounds ctx)
    (fromIndexIn : fromIndex.toNat < fromOp.spec.getNumResults! ctx.spec)
    (toIndexIn : toIndex.toNat < toOp.spec.getNumResults! ctx.spec)
    (hne : fromOp.spec ≠ toOp.spec) :
    (fromOp.getResultPtr ctx fromIndex fromIn).impl ≠
      (toOp.getResultPtr ctx toIndex toIn).impl := by
  let fromResult := fromOp.getResultPtr ctx fromIndex fromIn
  let toResult := toOp.getResultPtr ctx toIndex toIn
  have hFromIn : fromResult.InBounds ctx := by grind
  have hToIn : toResult.InBounds ctx := by grind
  have hFromOp : fromResult.spec.op = fromOp.spec := rfl
  have hToOp : toResult.spec.op = toOp.spec := rfl
  have hFromSlot := Sim.OpResultPtr.slot_included fromResult.spec hFromIn.ib
  have hToSlot := Sim.OpResultPtr.slot_included toResult.spec hToIn.ib
  have hDisjoint := Sim.disjoint_operation_operation (ctx := ctx) fromOp.spec toOp.spec
    fromIn.ib toIn.ib hne
  have hFromFlat := Sim.OpResultPtr.toFlat_eq_impl_toNat hFromIn
  have hToFlat := Sim.OpResultPtr.toFlat_eq_impl_toNat hToIn
  intro heq
  have hImplNat := congrArg UInt64.toNat heq
  have hFlatEq : fromResult.spec.toFlatNat ctx.spec =
      toResult.spec.toFlatNat ctx.spec := by
    grind [OpResultPtr.toFlat, OpResultPtr.toFlatNat]
  rw [hFromOp] at hFromSlot
  rw [hToOp] at hToSlot
  have hSize : (0 : Int) < Buffed.OpResult.sizeNat := by decide
  have hFromMem : (fromResult.spec.toFlatNat ctx.spec : Int) ∈
      fromOp.spec.rangeInt ctx.spec := by
    grind [IsIncludedI, mem_range_int]
  have hToMem : (toResult.spec.toFlatNat ctx.spec : Int) ∈
      toOp.spec.rangeInt ctx.spec := by
    grind [IsIncludedI, mem_range_int]
  have hNotTo := isDisjointI_mem_left hDisjoint
    (fromResult.spec.toFlatNat ctx.spec : Int) hFromMem
  apply hNotTo
  simpa only [hFlatEq] using hToMem

theorem Rewriter.replaceUse_spec_ne_of_impl_ne
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (hImpl : (use.getValue ctx useIn).impl ≠ newValue.impl) :
    (use.spec.get! ctx.spec).value ≠ newValue.spec := by
  intro hspec
  apply hImpl
  have hget : (use.getValue ctx useIn).spec = (use.spec.get! ctx.spec).value := by grind
  have hgetIb : (use.getValue ctx useIn).InBounds ctx := by grind
  grind

@[grind =]
theorem Rewriter.replaceUse_veir_inBounds (ptr : Veir.GenericPtr)
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) :
    ptr.InBounds (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec ↔
      ptr.InBounds ctx.spec := by
  simp only [Rewriter.replaceUse_def, Rewriter.replaceUseSim]
  split
  · rfl
  · rw [Sim.OpOperandPtr.insertIntoCurrent_veir_inBounds,
      Sim.OpOperandPtr.setValue_veir_inBounds,
      Sim.OpOperandPtr.removeFromCurrent_veir_inBounds]

theorem Rewriter.replaceUse_DefUse_newValue
    {oldValue : Veir.ValuePtr} {newValue : Sim.ValuePtr}
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hImpl : (use.getValue ctx useIn).impl ≠ newValue.impl)
    (useOfOldValue : (use.spec.get! ctx.spec).value = oldValue)
    (valuesNe : newValue.spec ≠ oldValue)
    (hNew : newValue.spec.DefUse ctx.spec newArray)
    (hOld : oldValue.DefUse ctx.spec oldArray) :
    newValue.spec.DefUse (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec
      (#[use.spec] ++ newArray) := by
  let ctx₁ := use.removeFromCurrent ctx useIn ctxIn
  have useIn₁ : use.InBounds ctx₁ := by
    have hGeneric : (Sim.GenericPtr.fromOpOperand use).InBounds ctx :=
      (Sim.GenericPtr.iff_opOperand use).mpr useIn
    have := (Sim.OpOperandPtr.removeFromCurrent_inBounds
      (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromOpOperand use)).mpr hGeneric
    exact (Sim.GenericPtr.iff_opOperand use).mp this
  have newIn₁ : newValue.InBounds ctx₁ := by
    have hGeneric : (Sim.GenericPtr.fromValue newValue).InBounds ctx :=
      (Sim.GenericPtr.iff_value newValue).mpr newIn
    have := (Sim.OpOperandPtr.removeFromCurrent_inBounds
      (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromValue newValue)).mpr hGeneric
    exact (Sim.GenericPtr.iff_value newValue).mp this
  let ctx₂ := use.setValue ctx₁ newValue useIn₁ newIn₁
  have useIn₂ : use.InBounds ctx₂ := by
    have hGeneric : (Sim.GenericPtr.fromOpOperand use).InBounds ctx₁ :=
      (Sim.GenericPtr.iff_opOperand use).mpr useIn₁
    have := (Sim.OpOperandPtr.setValue_inBounds ctx₁ use (.fromOpOperand use) newValue
      useIn₁ newIn₁).mpr hGeneric
    exact (Sim.GenericPtr.iff_opOperand use).mp this
  have ctx₂In : ctx₂.spec.FieldsInBounds := ctx₂.fieldsInBounds
  have useMem : use.spec ∈ oldArray := by
    have hmem := hOld.allUsesInChain use.spec useIn.ib useOfOldValue
    exact hmem.mpr (by simp)
  have hRemoved : newValue.spec.DefUse ctx₁.spec newArray := by
    exact Sim.ValuePtr.defUse_removeFromCurrent_other
      (ctx := ctx) (use := use) (array := newArray) (array' := oldArray)
      (value := newValue.spec) (value' := oldValue) (missingUses := ∅) (missingUses' := ∅)
      valuesNe (hvalue := useMem) useIn hNew hOld
  have hSet : newValue.spec.DefUse ctx₂.spec newArray
      (Std.ExtHashSet.ofList [use.spec]) := by
    dsimp only [ctx₂]
    rw [Sim.OpOperandPtr.setValue_spec]
    exact ValuePtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
      (useInBounds := useIn₁.ib) (useOfOtherValue := by
        dsimp only [ctx₁]
        rw [Sim.OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
        simp only
        rw [useOfOldValue]
        exact Ne.symm valuesNe) hRemoved
  have hInserted := Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_self_empty
    (ctx := ctx₂) (use := use) (ctxInBounds := ctx₂In) useIn₂ hSet
  have hspec : (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec =
      (use.insertIntoCurrent ctx₂ useIn₂ ctx₂In).spec := by
    simp only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte, ctx₂, ctx₁]
  rw [hspec]
  exact hInserted

theorem Rewriter.replaceUse_DefUse_oldValue
    {oldValue : Veir.ValuePtr} {newValue : Sim.ValuePtr}
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hImpl : (use.getValue ctx useIn).impl ≠ newValue.impl)
    (useOfOldValue : (use.spec.get! ctx.spec).value = oldValue)
    (valuesNe : oldValue ≠ newValue.spec)
    (hOld : oldValue.DefUse ctx.spec oldArray)
    (hNew : newValue.spec.DefUse ctx.spec newArray) :
    oldValue.DefUse (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec
      (oldArray.erase use.spec) := by
  let ctx₁ := use.removeFromCurrent ctx useIn ctxIn
  have useIn₁ : use.InBounds ctx₁ := by
    apply (Sim.GenericPtr.iff_opOperand use).mp
    exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
      (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromOpOperand use)).mpr
      ((Sim.GenericPtr.iff_opOperand use).mpr useIn)
  have newIn₁ : newValue.InBounds ctx₁ := by
    apply (Sim.GenericPtr.iff_value newValue).mp
    exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
      (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromValue newValue)).mpr
      ((Sim.GenericPtr.iff_value newValue).mpr newIn)
  let ctx₂ := use.setValue ctx₁ newValue useIn₁ newIn₁
  have useIn₂ : use.InBounds ctx₂ := by
    apply (Sim.GenericPtr.iff_opOperand use).mp
    exact (Sim.OpOperandPtr.setValue_inBounds ctx₁ use (.fromOpOperand use) newValue
      useIn₁ newIn₁).mpr ((Sim.GenericPtr.iff_opOperand use).mpr useIn₁)
  have useMem : use.spec ∈ oldArray := by
    exact (hOld.allUsesInChain use.spec useIn.ib useOfOldValue).mpr (by simp)
  have hOldRemoved : oldValue.DefUse ctx₁.spec (oldArray.erase use.spec)
      (Std.ExtHashSet.ofList [use.spec]) := by
    have hset : (∅ : Std.ExtHashSet OpOperandPtr).insert use.spec =
        Std.ExtHashSet.ofList [use.spec] := by
      ext other
      simp
    rw [← hset]
    exact Sim.ValuePtr.defUse_removeFromCurrent_self
      (ctx := ctx) (use := use) (array := oldArray) (missingUses := ∅)
      useMem useIn hOld
  have hNewRemoved : newValue.spec.DefUse ctx₁.spec newArray := by
    exact Sim.ValuePtr.defUse_removeFromCurrent_other
      (ctx := ctx) (use := use) (array := newArray) (array' := oldArray)
      (value := newValue.spec) (value' := oldValue) (missingUses := ∅) (missingUses' := ∅)
      (Ne.symm valuesNe) (hvalue := useMem) useIn hNew hOld
  have hOldSet : oldValue.DefUse ctx₂.spec (oldArray.erase use.spec) := by
    dsimp only [ctx₂]
    rw [Sim.OpOperandPtr.setValue_spec]
    exact ValuePtr.DefUse.OpOperandPtr_setValue_other_empty
      (useOfOtherValue := by
        dsimp only [ctx₁]
        rw [Sim.OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
        simp only
        rw [useOfOldValue]
        exact valuesNe) hOldRemoved
  have hNewSet : newValue.spec.DefUse ctx₂.spec newArray
      (Std.ExtHashSet.ofList [use.spec]) := by
    dsimp only [ctx₂]
    rw [Sim.OpOperandPtr.setValue_spec]
    exact ValuePtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
      (useInBounds := useIn₁.ib) (useOfOtherValue := by
        dsimp only [ctx₁]
        rw [Sim.OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
        simp only
        rw [useOfOldValue]
        exact valuesNe) hNewRemoved
  have hInserted := Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_other
    (ctx := ctx₂) (use := use) (value := oldValue) (value' := newValue.spec)
    (array := oldArray.erase use.spec) (array' := newArray)
    (missingUses := ∅) (missingUses' := Std.ExtHashSet.ofList [use.spec])
    (ctxInBounds := ctx₂.fieldsInBounds)
    useIn₂ valuesNe (hvalue := by simp) hOldSet hNewSet
  have hspec : (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec =
      (use.insertIntoCurrent ctx₂ useIn₂ ctx₂.fieldsInBounds).spec := by
    simp only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte, ctx₂, ctx₁]
  rw [hspec]
  exact hInserted

theorem Rewriter.replaceUse_DefUse_otherValue
    {oldValue value : Veir.ValuePtr} {newValue : Sim.ValuePtr}
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hImpl : (use.getValue ctx useIn).impl ≠ newValue.impl)
    (useOfOldValue : (use.spec.get! ctx.spec).value = oldValue)
    (hOld : oldValue.DefUse ctx.spec oldArray)
    (hNew : newValue.spec.DefUse ctx.spec newArray)
    (hValue : value.DefUse ctx.spec array)
    (valueNeOld : value ≠ oldValue) (valueNeNew : value ≠ newValue.spec)
    (valuesNe : oldValue ≠ newValue.spec) :
    value.DefUse (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec array := by
  let ctx₁ := use.removeFromCurrent ctx useIn ctxIn
  have useIn₁ : use.InBounds ctx₁ := by
    apply (Sim.GenericPtr.iff_opOperand use).mp
    exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
      (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromOpOperand use)).mpr
      ((Sim.GenericPtr.iff_opOperand use).mpr useIn)
  have newIn₁ : newValue.InBounds ctx₁ := by
    apply (Sim.GenericPtr.iff_value newValue).mp
    exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
      (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromValue newValue)).mpr
      ((Sim.GenericPtr.iff_value newValue).mpr newIn)
  let ctx₂ := use.setValue ctx₁ newValue useIn₁ newIn₁
  have useIn₂ : use.InBounds ctx₂ := by
    apply (Sim.GenericPtr.iff_opOperand use).mp
    exact (Sim.OpOperandPtr.setValue_inBounds ctx₁ use (.fromOpOperand use) newValue
      useIn₁ newIn₁).mpr ((Sim.GenericPtr.iff_opOperand use).mpr useIn₁)
  have useMem : use.spec ∈ oldArray := by
    exact (hOld.allUsesInChain use.spec useIn.ib useOfOldValue).mpr (by simp)
  have hValueRemoved : value.DefUse ctx₁.spec array := by
    exact Sim.ValuePtr.defUse_removeFromCurrent_other
      (ctx := ctx) (use := use) (array := array) (array' := oldArray)
      (value := value) (value' := oldValue) (missingUses := ∅) (missingUses' := ∅)
      valueNeOld (hvalue := useMem) useIn hValue hOld
  have hNewRemoved : newValue.spec.DefUse ctx₁.spec newArray := by
    exact Sim.ValuePtr.defUse_removeFromCurrent_other
      (ctx := ctx) (use := use) (array := newArray) (array' := oldArray)
      (value := newValue.spec) (value' := oldValue) (missingUses := ∅) (missingUses' := ∅)
      (Ne.symm valuesNe) (hvalue := useMem) useIn hNew hOld
  have hValueSet : value.DefUse ctx₂.spec array := by
    dsimp only [ctx₂]
    rw [Sim.OpOperandPtr.setValue_spec]
    exact ValuePtr.DefUse.OpOperandPtr_setValue_other_of_value_ne
      (value := newValue.spec) (useInBounds := useIn₁.ib)
      (useOfOtherValue' := by
        dsimp only [ctx₁]
        rw [Sim.OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
        simp only
        rw [useOfOldValue]
        exact Ne.symm valueNeOld)
      (valueNe := Ne.symm valueNeNew) hValueRemoved
  have hNewSet : newValue.spec.DefUse ctx₂.spec newArray
      (Std.ExtHashSet.ofList [use.spec]) := by
    dsimp only [ctx₂]
    rw [Sim.OpOperandPtr.setValue_spec]
    exact ValuePtr.DefUse.OpOperandPtr_setValue_self_ofList_singleton_of_value!_ne_self
      (useInBounds := useIn₁.ib) (useOfOtherValue := by
        dsimp only [ctx₁]
        rw [Sim.OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
        simp only
        rw [useOfOldValue]
        exact valuesNe) hNewRemoved
  have hInserted := Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_other
    (ctx := ctx₂) (use := use) (value := value) (value' := newValue.spec)
    (array := array) (array' := newArray) (missingUses := ∅)
    (missingUses' := Std.ExtHashSet.ofList [use.spec])
    (ctxInBounds := ctx₂.fieldsInBounds)
    useIn₂ valueNeNew (hvalue := by simp) hValueSet hNewSet
  have hspec : (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec =
      (use.insertIntoCurrent ctx₂ useIn₂ ctx₂.fieldsInBounds).spec := by
    simp only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte, ctx₂, ctx₁]
  rw [hspec]
  exact hInserted

theorem Rewriter.replaceUse_BlockDefUse
    {block : Veir.BlockPtr}
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hWF : block.DefUse ctx.spec array missingUses) :
    block.DefUse (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec array missingUses := by
  by_cases hImpl : (use.getValue ctx useIn).impl = newValue.impl
  · simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte] using hWF
  · let ctx₁ := use.removeFromCurrent ctx useIn ctxIn
    have useIn₁ : use.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromOpOperand use)).mpr
        ((Sim.GenericPtr.iff_opOperand use).mpr useIn)
    have newIn₁ : newValue.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_value newValue).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromValue newValue)).mpr
        ((Sim.GenericPtr.iff_value newValue).mpr newIn)
    let ctx₂ := use.setValue ctx₁ newValue useIn₁ newIn₁
    have useIn₂ : use.InBounds ctx₂ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.setValue_inBounds ctx₁ use (.fromOpOperand use) newValue
        useIn₁ newIn₁).mpr ((Sim.GenericPtr.iff_opOperand use).mpr useIn₁)
    have hRemoved := Sim.BlockPtr.defUse_OpOperandPtr_removeFromCurrent
      (ctx := ctx) (use := use) (useInBounds := useIn) (ctxInBounds := ctxIn) hWF
    have hSet : block.DefUse ctx₂.spec array missingUses := by
      apply BlockPtr.DefUse.unchanged (ctx := ctx₁.spec) (ctx' := ctx₂.spec) hRemoved
      · exact (Sim.OpOperandPtr.setValue_veir_inBounds ctx₁ use (.block block) newValue
          useIn₁ newIn₁).mpr hRemoved.blockInBounds
      · dsimp only [ctx₂]
        rw [Sim.OpOperandPtr.setValue_spec]
        simp
      · intro usePtr usePtrIn _
        exact (Sim.OpOperandPtr.setValue_veir_inBounds ctx₁ use (.blockOperand usePtr) newValue
          useIn₁ newIn₁).mpr usePtrIn
      · intros
        dsimp only [ctx₂]
        rw [Sim.OpOperandPtr.setValue_spec]
        simp
      · intro usePtr usePtrIn _
        exact (Sim.OpOperandPtr.setValue_veir_inBounds ctx₁ use (.blockOperand usePtr) newValue
          useIn₁ newIn₁).mp usePtrIn
      · intros
        dsimp only [ctx₂]
        rw [Sim.OpOperandPtr.setValue_spec]
        simp
    have hInserted := Sim.BlockPtr.defUse_OpOperandPtr_insertIntoCurrent
      (ctx := ctx₂) (use := use) (useInBounds := useIn₂)
      (ctxInBounds := ctx₂.fieldsInBounds) hSet
    simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte,
      ctx₂, ctx₁] using hInserted

theorem Rewriter.replaceUse_OpChain
    {block : Veir.BlockPtr}
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hWF : block.OpChain ctx.spec array) :
    block.OpChain (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec array := by
  by_cases hImpl : (use.getValue ctx useIn).impl = newValue.impl
  · simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte] using hWF
  · let ctx₁ := use.removeFromCurrent ctx useIn ctxIn
    have useIn₁ : use.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromOpOperand use)).mpr
        ((Sim.GenericPtr.iff_opOperand use).mpr useIn)
    have newIn₁ : newValue.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_value newValue).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromValue newValue)).mpr
        ((Sim.GenericPtr.iff_value newValue).mpr newIn)
    let ctx₂ := use.setValue ctx₁ newValue useIn₁ newIn₁
    have useIn₂ : use.InBounds ctx₂ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.setValue_inBounds ctx₁ use (.fromOpOperand use) newValue
        useIn₁ newIn₁).mpr ((Sim.GenericPtr.iff_opOperand use).mpr useIn₁)
    have hRemoved := Sim.BlockPtr.opChain_OpOperandPtr_removeFromCurrent
      (ctx := ctx) (use := use) (useInBounds := useIn) (ctxInBounds := ctxIn) hWF
    have blockIn₁ : block.InBounds ctx₁.spec := hRemoved.blockInBounds
    have hSet : block.OpChain ctx₂.spec array := by
      apply BlockPtr.OpChain_unchanged (ctx := ctx₁.spec) hRemoved
      · exact (Sim.OpOperandPtr.setValue_veir_inBounds ctx₁ use (.block block) newValue
          useIn₁ newIn₁).mpr blockIn₁
      · dsimp only [ctx₂]
        rw [Sim.OpOperandPtr.setValue_spec]
        rw [BlockPtr.get!_OpOperandPtr_setValue]
      · dsimp only [ctx₂]
        rw [Sim.OpOperandPtr.setValue_spec]
        rw [BlockPtr.get!_OpOperandPtr_setValue]
      · intro opPtr opPtrInBounds hParent
        have opPtrInBounds' := (Sim.OpOperandPtr.setValue_veir_inBounds
          ctx₁ use (.operation opPtr) newValue useIn₁ newIn₁).mpr opPtrInBounds
        refine ⟨opPtrInBounds', ?_, ?_, ?_⟩
        all_goals
          dsimp only [ctx₂]
          rw [Sim.OpOperandPtr.setValue_spec]
        · exact OperationPtr.parent!_OpOperandPtr_setValue
        · exact OperationPtr.prev!_OpOperandPtr_setValue
        · exact OperationPtr.next!_OpOperandPtr_setValue
      · intro opPtr opPtrInBounds hParent
        have opPtrInBounds' := (Sim.OpOperandPtr.setValue_veir_inBounds
          ctx₁ use (.operation opPtr) newValue useIn₁ newIn₁).mp opPtrInBounds
        refine ⟨opPtrInBounds', ?_⟩
        dsimp only [ctx₂]
        rw [Sim.OpOperandPtr.setValue_spec]
        exact OperationPtr.parent!_OpOperandPtr_setValue.symm
    have hInserted := Sim.BlockPtr.opChain_OpOperandPtr_insertIntoCurrent
      (ctx := ctx₂) (use := use) (useInBounds := useIn₂)
      (ctxInBounds := ctx₂.fieldsInBounds) hSet
    have hspec : (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec =
        (use.insertIntoCurrent ctx₂ useIn₂ ctx₂.fieldsInBounds).spec := by
      simp only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte, ctx₂, ctx₁]
    rw [hspec]
    exact hInserted

theorem Rewriter.replaceUse_BlockChain
    {region : Veir.RegionPtr}
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hWF : region.BlockChain ctx.spec array) :
    region.BlockChain (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec array := by
  by_cases hImpl : (use.getValue ctx useIn).impl = newValue.impl
  · simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte] using hWF
  · let ctx₁ := use.removeFromCurrent ctx useIn ctxIn
    have useIn₁ : use.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromOpOperand use)).mpr
        ((Sim.GenericPtr.iff_opOperand use).mpr useIn)
    have newIn₁ : newValue.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_value newValue).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromValue newValue)).mpr
        ((Sim.GenericPtr.iff_value newValue).mpr newIn)
    let ctx₂ := use.setValue ctx₁ newValue useIn₁ newIn₁
    have useIn₂ : use.InBounds ctx₂ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.setValue_inBounds ctx₁ use (.fromOpOperand use) newValue
        useIn₁ newIn₁).mpr ((Sim.GenericPtr.iff_opOperand use).mpr useIn₁)
    have hRemoved := Sim.RegionPtr.blockChain_OpOperandPtr_removeFromCurrent
      (ctx := ctx) (use := use) (useInBounds := useIn) (ctxInBounds := ctxIn) hWF
    have regionIn₁ : region.InBounds ctx₁.spec := hRemoved.inBounds
    have hSet : region.BlockChain ctx₂.spec array := by
      apply RegionPtr.blockChain_unchanged (ctx := ctx₁.spec) hRemoved
      · exact (Sim.OpOperandPtr.setValue_veir_inBounds ctx₁ use (.region region) newValue
          useIn₁ newIn₁).mpr regionIn₁
      · dsimp only [ctx₂]
        rw [Sim.OpOperandPtr.setValue_spec]
        rw [RegionPtr.get!_OpOperandPtr_setValue]
      · dsimp only [ctx₂]
        rw [Sim.OpOperandPtr.setValue_spec]
        rw [RegionPtr.get!_OpOperandPtr_setValue]
      · intro blockPtr blockPtrInBounds hParent
        have blockPtrInBounds' := (Sim.OpOperandPtr.setValue_veir_inBounds
          ctx₁ use (.block blockPtr) newValue useIn₁ newIn₁).mpr blockPtrInBounds
        refine ⟨blockPtrInBounds', ?_, ?_, ?_⟩
        all_goals
          dsimp only [ctx₂]
          rw [Sim.OpOperandPtr.setValue_spec]
          rw [BlockPtr.get!_OpOperandPtr_setValue]
      · intro blockPtr blockPtrInBounds hParent
        have blockPtrInBounds' := (Sim.OpOperandPtr.setValue_veir_inBounds
          ctx₁ use (.block blockPtr) newValue useIn₁ newIn₁).mp blockPtrInBounds
        refine ⟨blockPtrInBounds', ?_⟩
        dsimp only [ctx₂]
        rw [Sim.OpOperandPtr.setValue_spec]
        rw [BlockPtr.get!_OpOperandPtr_setValue]
    have hInserted := Sim.RegionPtr.blockChain_OpOperandPtr_insertIntoCurrent
      (ctx := ctx₂) (use := use) (useInBounds := useIn₂)
      (ctxInBounds := ctx₂.fieldsInBounds) hSet
    have hspec : (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec =
        (use.insertIntoCurrent ctx₂ useIn₂ ctx₂.fieldsInBounds).spec := by
      simp only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte, ctx₂, ctx₁]
    rw [hspec]
    exact hInserted

theorem Sim.Operation.wellFormed_OpOperandPtr_setValue
    {opPtr : Veir.OperationPtr} {opInBounds} {use : Sim.OpOperandPtr}
    {useInBounds} {newValue : Sim.ValuePtr} {newValueInBounds}
    (hWF : opPtr.WellFormed ctx.spec opInBounds) :
    opPtr.WellFormed (use.setValue ctx newValue useInBounds newValueInBounds).spec (by grind) := by
  change opPtr.WellFormed (use.spec.setValue ctx.spec newValue.spec (by grind)) _
  apply OperationPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Block.wellFormed_OpOperandPtr_setValue
    {blockPtr : Veir.BlockPtr} {blockInBounds} {use : Sim.OpOperandPtr}
    {useInBounds} {newValue : Sim.ValuePtr} {newValueInBounds}
    (hWF : blockPtr.WellFormed ctx.spec blockInBounds) :
    blockPtr.WellFormed (use.setValue ctx newValue useInBounds newValueInBounds).spec (by grind) := by
  change blockPtr.WellFormed (use.spec.setValue ctx.spec newValue.spec (by grind)) _
  apply BlockPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Region.wellFormed_OpOperandPtr_setValue
    {regionPtr : Veir.RegionPtr} (regionInBounds : regionPtr.InBounds ctx.spec)
    {use : Sim.OpOperandPtr} {useInBounds} {newValue : Sim.ValuePtr} {newValueInBounds}
    (hWF : regionPtr.WellFormed ctx.spec) :
    regionPtr.WellFormed (use.setValue ctx newValue useInBounds newValueInBounds).spec := by
  rw [Sim.OpOperandPtr.setValue_spec]
  apply RegionPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Rewriter.replaceUse_OperationWellFormed
    {opPtr : Veir.OperationPtr} (opIn : opPtr.InBounds ctx.spec)
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hWF : opPtr.WellFormed ctx.spec opIn) :
    opPtr.WellFormed (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec (by grind) := by
  by_cases hImpl : (use.getValue ctx useIn).impl = newValue.impl
  · simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte] using hWF
  · let ctx₁ := use.removeFromCurrent ctx useIn ctxIn
    have useIn₁ : use.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromOpOperand use)).mpr
        ((Sim.GenericPtr.iff_opOperand use).mpr useIn)
    have newIn₁ : newValue.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_value newValue).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromValue newValue)).mpr
        ((Sim.GenericPtr.iff_value newValue).mpr newIn)
    let ctx₂ := use.setValue ctx₁ newValue useIn₁ newIn₁
    have useIn₂ : use.InBounds ctx₂ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.setValue_inBounds ctx₁ use (.fromOpOperand use) newValue
        useIn₁ newIn₁).mpr ((Sim.GenericPtr.iff_opOperand use).mpr useIn₁)
    have hRemoved := Sim.Operation.wellFormed_OpOperandPtr_removeFromCurrent
      (ctx := ctx) (use := use) (useInBounds := useIn) (ctxInBounds := ctxIn) hWF
    have opIn₁ : opPtr.InBounds ctx₁.spec :=
      (Sim.OpOperandPtr.removeFromCurrent_veir_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.operation opPtr)).mpr opIn
    have hSet := Sim.Operation.wellFormed_OpOperandPtr_setValue
      (ctx := ctx₁) (use := use) (useInBounds := useIn₁)
      (newValue := newValue) (newValueInBounds := newIn₁) hRemoved
    have opIn₂ : opPtr.InBounds ctx₂.spec :=
      (Sim.OpOperandPtr.setValue_veir_inBounds ctx₁ use (.operation opPtr) newValue
        useIn₁ newIn₁).mpr opIn₁
    have hInserted := Sim.Operation.wellFormed_OpOperandPtr_insertIntoCurrent
      (ctx := ctx₂) (use := use) (useInBounds := useIn₂)
      (ctxInBounds := ctx₂.fieldsInBounds) opIn₂ hSet
    simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte,
      ctx₂, ctx₁] using hInserted

theorem Rewriter.replaceUse_BlockWellFormed
    {blockPtr : Veir.BlockPtr} (blockIn : blockPtr.InBounds ctx.spec)
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hWF : blockPtr.WellFormed ctx.spec blockIn) :
    blockPtr.WellFormed (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec (by grind) := by
  by_cases hImpl : (use.getValue ctx useIn).impl = newValue.impl
  · simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte] using hWF
  · let ctx₁ := use.removeFromCurrent ctx useIn ctxIn
    have useIn₁ : use.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromOpOperand use)).mpr
        ((Sim.GenericPtr.iff_opOperand use).mpr useIn)
    have newIn₁ : newValue.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_value newValue).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromValue newValue)).mpr
        ((Sim.GenericPtr.iff_value newValue).mpr newIn)
    let ctx₂ := use.setValue ctx₁ newValue useIn₁ newIn₁
    have useIn₂ : use.InBounds ctx₂ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.setValue_inBounds ctx₁ use (.fromOpOperand use) newValue
        useIn₁ newIn₁).mpr ((Sim.GenericPtr.iff_opOperand use).mpr useIn₁)
    have hRemoved := Sim.Block.wellFormed_OpOperandPtr_removeFromCurrent
      (ctx := ctx) (use := use) (useInBounds := useIn) (ctxInBounds := ctxIn) hWF
    have blockIn₁ : blockPtr.InBounds ctx₁.spec :=
      (Sim.OpOperandPtr.removeFromCurrent_veir_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.block blockPtr)).mpr blockIn
    have hSet := Sim.Block.wellFormed_OpOperandPtr_setValue
      (ctx := ctx₁) (use := use) (useInBounds := useIn₁)
      (newValue := newValue) (newValueInBounds := newIn₁) hRemoved
    have blockIn₂ : blockPtr.InBounds ctx₂.spec :=
      (Sim.OpOperandPtr.setValue_veir_inBounds ctx₁ use (.block blockPtr) newValue
        useIn₁ newIn₁).mpr blockIn₁
    have hInserted := Sim.Block.wellFormed_OpOperandPtr_insertIntoCurrent
      (ctx := ctx₂) (use := use) (useInBounds := useIn₂)
      (ctxInBounds := ctx₂.fieldsInBounds) blockIn₂ hSet
    simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte,
      ctx₂, ctx₁] using hInserted

theorem Rewriter.replaceUse_RegionWellFormed
    {regionPtr : Veir.RegionPtr} (regionIn : regionPtr.InBounds ctx.spec)
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hWF : regionPtr.WellFormed ctx.spec) :
    regionPtr.WellFormed (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec := by
  by_cases hImpl : (use.getValue ctx useIn).impl = newValue.impl
  · simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte] using hWF
  · let ctx₁ := use.removeFromCurrent ctx useIn ctxIn
    have useIn₁ : use.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromOpOperand use)).mpr
        ((Sim.GenericPtr.iff_opOperand use).mpr useIn)
    have newIn₁ : newValue.InBounds ctx₁ := by
      apply (Sim.GenericPtr.iff_value newValue).mp
      exact (Sim.OpOperandPtr.removeFromCurrent_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.fromValue newValue)).mpr
        ((Sim.GenericPtr.iff_value newValue).mpr newIn)
    let ctx₂ := use.setValue ctx₁ newValue useIn₁ newIn₁
    have useIn₂ : use.InBounds ctx₂ := by
      apply (Sim.GenericPtr.iff_opOperand use).mp
      exact (Sim.OpOperandPtr.setValue_inBounds ctx₁ use (.fromOpOperand use) newValue
        useIn₁ newIn₁).mpr ((Sim.GenericPtr.iff_opOperand use).mpr useIn₁)
    have hRemoved := Sim.Region.wellFormed_OpOperandPtr_removeFromCurrent
      (ctx := ctx) (use := use) (useInBounds := useIn) (ctxInBounds := ctxIn) regionIn hWF
    have regionIn₁ : regionPtr.InBounds ctx₁.spec :=
      (Sim.OpOperandPtr.removeFromCurrent_veir_inBounds
        (ctx := ctx) (operand := use) (h₁ := useIn) (h₂ := ctxIn) (.region regionPtr)).mpr regionIn
    have hSet := Sim.Region.wellFormed_OpOperandPtr_setValue
      (ctx := ctx₁) (use := use) (useInBounds := useIn₁)
      (newValue := newValue) (newValueInBounds := newIn₁) regionIn₁ hRemoved
    have regionIn₂ : regionPtr.InBounds ctx₂.spec :=
      (Sim.OpOperandPtr.setValue_veir_inBounds ctx₁ use (.region regionPtr) newValue
        useIn₁ newIn₁).mpr regionIn₁
    have hInserted := Sim.Region.wellFormed_OpOperandPtr_insertIntoCurrent
      (ctx := ctx₂) (use := use) (useInBounds := useIn₂)
      (ctxInBounds := ctx₂.fieldsInBounds) regionIn₂ hSet
    simpa only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte,
      ctx₂, ctx₁] using hInserted

theorem Rewriter.replaceUse_ValueDefUseChains
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    ∀ (valuePtr : Veir.ValuePtr), valuePtr.InBounds
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec →
      ∃ array, valuePtr.DefUse
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec array := by
  intro valuePtr valuePtrInBounds
  by_cases hImpl : (use.getValue ctx useIn).impl = newValue.impl
  · have hctx : (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec = ctx.spec := by
      simp only [Rewriter.replaceUse_def, Rewriter.replaceUseSim, hImpl, ↓reduceIte]
    rw [hctx] at valuePtrInBounds ⊢
    simpa only [Std.ExtHashSet.filter_empty] using
      hWf.valueDefUseChains valuePtr valuePtrInBounds
  · have h := Rewriter.replaceUse_spec_ne_of_impl_ne use newValue useIn newIn hImpl
    let oldValue := (use.spec.get! ctx.spec).value
    have ⟨oldArray, hOld⟩ := hWf.valueDefUseChains oldValue (by grind)
    have ⟨newArray, hNew⟩ := hWf.valueDefUseChains newValue.spec (by grind)
    have inputInBounds : valuePtr.InBounds ctx.spec :=
      (Rewriter.replaceUse_veir_inBounds (.value valuePtr) use newValue useIn newIn ctxIn).mp
        valuePtrInBounds
    have ⟨array, hArray⟩ := hWf.valueDefUseChains valuePtr inputInBounds
    simp only [Std.ExtHashSet.filter_empty] at hOld hNew hArray ⊢
    by_cases hv : valuePtr = oldValue
    · subst valuePtr
      exact ⟨_, Rewriter.replaceUse_DefUse_oldValue useIn newIn ctxIn hImpl rfl h hOld hNew⟩
    · by_cases hv' : valuePtr = newValue.spec
      · subst valuePtr
        exact ⟨_, Rewriter.replaceUse_DefUse_newValue useIn newIn ctxIn hImpl rfl
          (by grind) hNew hOld⟩
      · exact ⟨_, Rewriter.replaceUse_DefUse_otherValue useIn newIn ctxIn hImpl rfl hOld hNew
          hArray hv hv' h⟩

theorem Rewriter.replaceUse_BlockDefUseChains
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    ∀ (blockPtr : Veir.BlockPtr), blockPtr.InBounds
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec →
      ∃ array, blockPtr.DefUse
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec array := by
  intro blockPtr blockPtrInBounds
  have inputInBounds : blockPtr.InBounds ctx.spec :=
    (Rewriter.replaceUse_veir_inBounds (.block blockPtr) use newValue useIn newIn ctxIn).mp
      blockPtrInBounds
  have ⟨array, harray⟩ := hWf.blockDefUseChains blockPtr inputInBounds
  simp only [Std.ExtHashSet.filter_empty] at harray
  exact ⟨array, Rewriter.replaceUse_BlockDefUse use newValue useIn newIn ctxIn harray⟩

theorem Rewriter.replaceUse_OpChains
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    ∀ (blockPtr : Veir.BlockPtr), blockPtr.InBounds
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec →
      ∃ array, blockPtr.OpChain
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec array := by
  intro blockPtr blockPtrInBounds
  have inputInBounds : blockPtr.InBounds ctx.spec :=
    (Rewriter.replaceUse_veir_inBounds (.block blockPtr) use newValue useIn newIn ctxIn).mp
      blockPtrInBounds
  have ⟨array, harray⟩ := hWf.opChain blockPtr inputInBounds
  exact ⟨array, Rewriter.replaceUse_OpChain use newValue useIn newIn ctxIn harray⟩

theorem Rewriter.replaceUse_BlockChains
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    ∀ (regionPtr : Veir.RegionPtr), regionPtr.InBounds
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec →
      ∃ array, regionPtr.BlockChain
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec array := by
  intro regionPtr regionPtrInBounds
  have inputInBounds : regionPtr.InBounds ctx.spec :=
    (Rewriter.replaceUse_veir_inBounds (.region regionPtr) use newValue useIn newIn ctxIn).mp
      regionPtrInBounds
  have ⟨array, harray⟩ := hWf.blockChain regionPtr inputInBounds
  exact ⟨array, Rewriter.replaceUse_BlockChain use newValue useIn newIn ctxIn harray⟩

theorem Rewriter.replaceUse_Operations
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    ∀ (opPtr : Veir.OperationPtr)
      (opPtrInBounds : opPtr.InBounds
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec),
      opPtr.WellFormed
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec opPtrInBounds := by
  intro opPtr opPtrInBounds
  have inputInBounds : opPtr.InBounds ctx.spec :=
    (Rewriter.replaceUse_veir_inBounds (.operation opPtr) use newValue useIn newIn ctxIn).mp
      opPtrInBounds
  exact Rewriter.replaceUse_OperationWellFormed inputInBounds use newValue useIn newIn ctxIn
    (hWf.operations opPtr inputInBounds)

theorem Rewriter.replaceUse_Blocks
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    ∀ (blockPtr : Veir.BlockPtr)
      (blockPtrInBounds : blockPtr.InBounds
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec),
      blockPtr.WellFormed
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec blockPtrInBounds := by
  intro blockPtr blockPtrInBounds
  have inputInBounds : blockPtr.InBounds ctx.spec :=
    (Rewriter.replaceUse_veir_inBounds (.block blockPtr) use newValue useIn newIn ctxIn).mp
      blockPtrInBounds
  exact Rewriter.replaceUse_BlockWellFormed inputInBounds use newValue useIn newIn ctxIn
    (hWf.blocks blockPtr inputInBounds)

theorem Rewriter.replaceUse_Regions
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    ∀ (regionPtr : Veir.RegionPtr), regionPtr.InBounds
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec →
      regionPtr.WellFormed
        (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec := by
  intro regionPtr regionPtrInBounds
  have inputInBounds : regionPtr.InBounds ctx.spec :=
    (Rewriter.replaceUse_veir_inBounds (.region regionPtr) use newValue useIn newIn ctxIn).mp
      regionPtrInBounds
  exact Rewriter.replaceUse_RegionWellFormed inputInBounds use newValue useIn newIn ctxIn
    (hWf.regions regionPtr inputInBounds)

@[grind .]
theorem Rewriter.replaceUse_WellFormed
    (use : Sim.OpOperandPtr) (newValue : Sim.ValuePtr)
    (useIn : use.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    (Rewriter.replaceUse ctx use newValue useIn newIn ctxIn).spec.WellFormed := by
  constructor
  case inBounds => exact Rewriter.replaceUse_fieldsInBounds hWf.inBounds
  case valueDefUseChains =>
    simpa only [Std.ExtHashSet.filter_empty] using
      Rewriter.replaceUse_ValueDefUseChains use newValue useIn newIn ctxIn hWf
  case blockDefUseChains =>
    simpa only [Std.ExtHashSet.filter_empty] using
      Rewriter.replaceUse_BlockDefUseChains use newValue useIn newIn ctxIn hWf
  case opChain =>
    exact Rewriter.replaceUse_OpChains use newValue useIn newIn ctxIn hWf
  case blockChain =>
    exact Rewriter.replaceUse_BlockChains use newValue useIn newIn ctxIn hWf
  case operations =>
    exact Rewriter.replaceUse_Operations use newValue useIn newIn ctxIn hWf
  case blocks =>
    exact Rewriter.replaceUse_Blocks use newValue useIn newIn ctxIn hWf
  case regions =>
    exact Rewriter.replaceUse_Regions use newValue useIn newIn ctxIn hWf

@[grind .]
theorem Rewriter.replaceValue?_WellFormed
    (oldValue newValue : Sim.ValuePtr)
    (oldIn : oldValue.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    newCtx.spec.WellFormed := by
  simp only [Rewriter.replaceValue?_def]
  fun_induction Rewriter.replaceValue?Sim
  case case1 => simp
  case case2 =>
    intro heq
    cases heq
    exact hWf
  case case3 =>
    apply_assumption
    apply Rewriter.replaceUse_WellFormed <;> assumption

theorem Rewriter.replaceValue?_oldValue_firstUse_eq_none
    (oldValue newValue : Sim.ValuePtr)
    (oldIn : oldValue.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (heq : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth =
      some newCtx) :
    oldValue.spec.getFirstUse! newCtx.spec = none := by
  simp only [Rewriter.replaceValue?_def] at heq
  fun_induction Rewriter.replaceValue?Sim <;>
    grind [Sim.OptionOpOperandPtr.toOption_none_iff_spec_none,
      Sim.ValuePtr.getFirstUse_spec, Sim.ValuePtr.getFirstUse_sim,
      ValuePtr.getFirstUse!_eq_getFirstUse, Sim.OptionOpOperandPtr.Sim_def]

theorem ValuePtr.hasUses!_replaceValue?_oldValue
    (oldValue newValue : Sim.ValuePtr)
    (oldIn : oldValue.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (heq : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth =
      some newCtx) :
    oldValue.spec.hasUses! newCtx.spec = false := by
  rw [ValuePtr.hasUses!_def,
    Rewriter.replaceValue?_oldValue_firstUse_eq_none oldValue newValue oldIn newIn ctxIn heq]
  rfl

@[grind .]
theorem Rewriter.replaceValue?_preserves_numRegions
    (op : Sim.OperationPtr) (opIn : op.InBounds ctx)
    (heq : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth =
      some newCtx) :
    op.spec.getNumRegions! newCtx.spec = op.spec.getNumRegions! ctx.spec := by
  simp only [Rewriter.replaceValue?_def] at heq
  fun_induction Rewriter.replaceValue?Sim <;>
    grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim, generic_ptr_grind]

theorem Rewriter.replaceValue?_DefUse_otherValue
    (oldValue newValue value : Sim.ValuePtr)
    (oldIn : oldValue.InBounds ctx) (newIn : newValue.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds)
    (hValue : value.spec.DefUse ctx.spec array)
    (hOld : oldValue.spec.DefUse ctx.spec oldArray)
    (hNew : newValue.spec.DefUse ctx.spec newArray)
    (valueNeOld : value.spec ≠ oldValue.spec)
    (valueNeNew : value.spec ≠ newValue.spec)
    (oldNeNew : oldValue.spec ≠ newValue.spec)
    (oldImplNeNew : oldValue.impl ≠ newValue.impl)
    (heq : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth =
      some newCtx) :
    value.spec.DefUse newCtx.spec array := by
  simp only [Rewriter.replaceValue?_def] at heq
  fun_induction Rewriter.replaceValue?Sim generalizing array oldArray newArray
  case case1 => simp at heq
  case case2 =>
    cases heq
    exact hValue
  case case3 ctxCur oldInCur newInCur ctxInCur currentDepth hDepth depth' firstUse hFirst ctx' ih =>
    have hFirstIn : firstUse.InBounds ctxCur := by grind [generic_ptr_grind]
    have hFirstSpec : oldValue.spec.getFirstUse! ctxCur.spec = some firstUse.spec := by
      have hFirstOptionIn :
          (oldValue.getFirstUse ctxCur oldInCur).InBounds ctxCur := by grind
      have hspec := Sim.OptionOpOperandPtr.toOption_some hFirstOptionIn hFirst
      rw [Sim.ValuePtr.getFirstUse_spec] at hspec
      rw [ValuePtr.getFirstUse!_eq_getFirstUse]
      exact hspec
    have hUseValue : (firstUse.spec.get! ctxCur.spec).value = oldValue.spec := by
      grind [ValuePtr.DefUse]
    have hOldImpl : (firstUse.getValue ctxCur hFirstIn).impl = oldValue.impl := by
      have hGetIn : (firstUse.getValue ctxCur hFirstIn).InBounds ctxCur := by grind
      have hGetSpec : (firstUse.getValue ctxCur hFirstIn).spec = oldValue.spec := by grind
      have hGetSim := hGetIn.sim
      have hOldSim := oldInCur.sim
      grind [Sim.ValuePtr.Sim_def]
    have hImpl : (firstUse.getValue ctxCur hFirstIn).impl ≠ newValue.impl := by
      grind
    apply ih
    · exact Rewriter.replaceUse_DefUse_otherValue hFirstIn newInCur ctxInCur hImpl
        hUseValue hOld hNew hValue valueNeOld valueNeNew oldNeNew
    · exact Rewriter.replaceUse_DefUse_oldValue hFirstIn newInCur ctxInCur hImpl
        hUseValue oldNeNew hOld hNew
    · exact Rewriter.replaceUse_DefUse_newValue hFirstIn newInCur ctxInCur hImpl
        hUseValue (Ne.symm oldNeNew) hNew hOld
    · exact heq

theorem ValuePtr.hasUses!_replaceValue?_otherValue
    (oldValue newValue value : Sim.ValuePtr)
    (oldIn : oldValue.InBounds ctx) (newIn : newValue.InBounds ctx)
    (valueIn : value.InBounds ctx)
    (ctxIn : ctx.spec.FieldsInBounds) (wf : ctx.spec.WellFormed)
    (oldNeNew : oldValue.spec ≠ newValue.spec)
    (valueNeOld : value.spec ≠ oldValue.spec)
    (valueNeNew : value.spec ≠ newValue.spec)
    (oldImplNeNew : oldValue.impl ≠ newValue.impl)
    (heq : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth =
      some newCtx) :
    value.spec.hasUses! newCtx.spec = value.spec.hasUses! ctx.spec := by
  have ⟨array, hValue⟩ := wf.valueDefUseChains value.spec valueIn.ib
  have ⟨oldArray, hOld⟩ := wf.valueDefUseChains oldValue.spec oldIn.ib
  have ⟨newArray, hNew⟩ := wf.valueDefUseChains newValue.spec newIn.ib
  simp only [Std.ExtHashSet.filter_empty] at hValue hOld hNew
  have hPreserved := Rewriter.replaceValue?_DefUse_otherValue oldValue newValue value
    oldIn newIn ctxIn hValue hOld hNew valueNeOld valueNeNew oldNeNew oldImplNeNew heq
  have hFirst := hPreserved.firstElem
  have hFirstOld := hValue.firstElem
  grind [ValuePtr.hasUses!_def]

theorem Sim.IRContext.wellFormed_replaceOpResults
    (fromOp toOp : Sim.OperationPtr) (index : UInt64)
    (fromOpIB : fromOp.InBounds ctx) (toOpIB : toOp.InBounds ctx)
    (hNumFrom : index.toNat ≤ fromOp.spec.getNumResults! ctx.spec)
    (hNumTo : index.toNat ≤ toOp.spec.getNumResults! ctx.spec)
    (ctxInBounds : ctx.spec.FieldsInBounds) (hWf : ctx.spec.WellFormed) :
    Rewriter.replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo
      ctxInBounds = some newCtx →
    newCtx.spec.WellFormed := by
  simp only [Rewriter.replaceOpResults_def]
  fun_induction Rewriter.replaceOpResultsSim
  case case1 =>
    intro heq
    cases heq
    exact hWf
  case case2 => simp
  case case3 =>
    apply_assumption
    apply Rewriter.replaceValue?_WellFormed <;> assumption

theorem OpResult.hasUses_replaceOpResults_self_ge
    (ctx : Sim.IRContext OpInfo) (fromOp toOp : Sim.OperationPtr) (index : UInt64)
    (fromOpIB : fromOp.InBounds ctx) (toOpIB : toOp.InBounds ctx)
    (hNumFrom : index.toNat ≤ fromOp.spec.getNumResults! ctx.spec)
    (hNumTo : index.toNat ≤ toOp.spec.getNumResults! ctx.spec)
    (ctxInBounds : ctx.spec.FieldsInBounds) (wf : ctx.spec.WellFormed)
    (neOps : fromOp.spec ≠ toOp.spec)
    (heq : Rewriter.replaceOpResults ctx fromOp toOp index fromOpIB toOpIB
      hNumFrom hNumTo ctxInBounds = some newCtx) :
    ∀ i, index.toNat ≤ i → i < fromOp.spec.getNumResults! ctx.spec →
      i < toOp.spec.getNumResults! ctx.spec →
      (ValuePtr.opResult (fromOp.spec.getResult i)).hasUses! newCtx.spec =
        (ValuePtr.opResult (fromOp.spec.getResult i)).hasUses! ctx.spec := by
  simp only [Rewriter.replaceOpResults_def] at heq
  fun_induction Rewriter.replaceOpResultsSim
  case case1 =>
    cases heq
    intros
    rfl
  case case2 => simp at heq
  case case3 ctxCur indexCur fromInCur toInCur hNumFCur hNumTCur ctxInCur hIndex
      indexPred oldResult newResult nextCtx hReplace ih =>
    have hIndexPos : 0 < indexCur.toNat := by
      have hneNat : indexCur.toNat ≠ 0 := by
        intro hz
        apply hIndex
        apply UInt64.toNat_inj.mp
        simpa using hz
      omega
    have hIndexLt := UInt64.toNat_lt indexCur
    have hPred : indexPred.toNat = indexCur.toNat - 1 := by
      dsimp only [indexPred]
      rw [UInt64.toNat_sub]
      change (2 ^ 64 - 1 + indexCur.toNat) % 2 ^ 64 = indexCur.toNat - 1
      have heqPred : 2 ^ 64 - 1 + indexCur.toNat =
          2 ^ 64 + (indexCur.toNat - 1) := by omega
      rw [heqPred, Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have wfNext : nextCtx.spec.WellFormed :=
      Rewriter.replaceValue?_WellFormed (Sim.ValuePtr.fromOpResultPtr oldResult)
        (Sim.ValuePtr.fromOpResultPtr newResult)
        (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind]) ctxInCur wf hReplace
    intro i hi hFromI hToI
    have hFromINext : i < fromOp.spec.getNumResults! nextCtx.spec := by
      rw [Rewriter.replaceValue?_preserves_results_size fromOp fromInCur hReplace]
      exact hFromI
    have hToINext : i < toOp.spec.getNumResults! nextCtx.spec := by
      rw [Rewriter.replaceValue?_preserves_results_size toOp toInCur hReplace]
      exact hToI
    have hRec := ih wfNext heq i (by rw [hPred]; omega) hFromINext hToINext
    have hNumResultsLt : fromOp.spec.getNumResults! ctxCur.spec < UInt64.size := by
      have hOpWf := wf.operations fromOp.spec fromInCur.ib
      have henc := ctxCur.sim.encoding_op fromOp.spec fromInCur.ib
      rw [← hOpWf.capResults_eq_numResults, henc.numResults]
      exact UInt64.toNat_lt _
    have hISize : i < UInt64.size := Nat.lt_trans hFromI hNumResultsLt
    have hIToNat : i.toUInt64.toNat = i := by
      change (UInt64.ofNat i).toNat = i
      exact UInt64.toNat_ofNat_of_lt hISize
    let valueResult := fromOp.getResultPtr ctxCur i.toUInt64 fromInCur
    let value := Sim.ValuePtr.fromOpResultPtr valueResult
    have hValueIn : value.InBounds ctxCur := by
      dsimp [value, valueResult]
      grind [UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt]
    have hOldIn : (Sim.ValuePtr.fromOpResultPtr oldResult).InBounds ctxCur := by
      grind [generic_ptr_grind]
    have hNewIn : (Sim.ValuePtr.fromOpResultPtr newResult).InBounds ctxCur := by
      grind [generic_ptr_grind]
    have hOldNewSpec : (Sim.ValuePtr.fromOpResultPtr oldResult).spec ≠
        (Sim.ValuePtr.fromOpResultPtr newResult).spec := by
      simp only [Sim.ValuePtr.fromOpResultPtr, oldResult, newResult,
        Sim.OperationPtr.getResultPtr_def, Sim.OperationPtr.getResultPtrSim]
      intro h
      injection h with h
      apply neOps
      exact congrArg OpResultPtr.op h
    have hValueOld : value.spec ≠ (Sim.ValuePtr.fromOpResultPtr oldResult).spec := by
      simp only [value, valueResult, oldResult, Sim.ValuePtr.fromOpResultPtr,
        Sim.OperationPtr.getResultPtr_def, Sim.OperationPtr.getResultPtrSim]
      intro h
      injection h with h
      have hiEq := congrArg OpResultPtr.index h
      simp only [OperationPtr.getResult_index] at hiEq
      rw [hIToNat] at hiEq
      omega
    have hValueNew : value.spec ≠ (Sim.ValuePtr.fromOpResultPtr newResult).spec := by
      simp only [value, valueResult, newResult, Sim.ValuePtr.fromOpResultPtr,
        Sim.OperationPtr.getResultPtr_def, Sim.OperationPtr.getResultPtrSim]
      intro h
      injection h with h
      apply neOps
      exact congrArg OpResultPtr.op h
    have hOldNewImpl : (Sim.ValuePtr.fromOpResultPtr oldResult).impl ≠
        (Sim.ValuePtr.fromOpResultPtr newResult).impl := by
      dsimp [oldResult, newResult, Sim.ValuePtr.fromOpResultPtr]
      exact Sim.OperationPtr.getResultPtr_impl_ne_of_spec_ne fromOp toOp indexPred indexPred
        fromInCur toInCur (by rw [hPred]; omega) (by rw [hPred]; omega) neOps
    have hStep := ValuePtr.hasUses!_replaceValue?_otherValue
      (Sim.ValuePtr.fromOpResultPtr oldResult) (Sim.ValuePtr.fromOpResultPtr newResult)
      value hOldIn hNewIn hValueIn ctxInCur wf
      hOldNewSpec hValueOld hValueNew hOldNewImpl hReplace
    have hValueSpec : value.spec = ValuePtr.opResult (fromOp.spec.getResult i) := by
      simp only [value, valueResult, Sim.ValuePtr.fromOpResultPtr,
        Sim.OperationPtr.getResultPtr_def, Sim.OperationPtr.getResultPtrSim, hIToNat]
    rw [hValueSpec] at hStep
    exact hRec.trans hStep

theorem OpResult.hasUses_replaceOpResults_self
    (ctx : Sim.IRContext OpInfo) (fromOp toOp : Sim.OperationPtr) (index : UInt64)
    (fromOpIB : fromOp.InBounds ctx) (toOpIB : toOp.InBounds ctx)
    (hNumFrom : index.toNat ≤ fromOp.spec.getNumResults! ctx.spec)
    (hNumTo : index.toNat ≤ toOp.spec.getNumResults! ctx.spec)
    (ctxInBounds : ctx.spec.FieldsInBounds) (wf : ctx.spec.WellFormed)
    (neOps : fromOp.spec ≠ toOp.spec)
    (heq : Rewriter.replaceOpResults ctx fromOp toOp index fromOpIB toOpIB
      hNumFrom hNumTo ctxInBounds = some newCtx) :
    ∀ i, i < index.toNat →
      (ValuePtr.opResult (fromOp.spec.getResult i)).hasUses! newCtx.spec = false := by
  simp only [Rewriter.replaceOpResults_def] at heq
  fun_induction Rewriter.replaceOpResultsSim
  case case1 =>
    intros i hi
    simp at hi
  case case2 => simp at heq
  case case3 ctxCur indexCur fromInCur toInCur hNumFCur hNumTCur ctxInCur hIndex
      indexPred oldResult newResult nextCtx hReplace ih =>
    have hIndexPos : 0 < indexCur.toNat := by
      have hneNat : indexCur.toNat ≠ 0 := by
        intro hz
        apply hIndex
        apply UInt64.toNat_inj.mp
        simpa using hz
      omega
    have hIndexLt := UInt64.toNat_lt indexCur
    have hPred : indexPred.toNat = indexCur.toNat - 1 := by
      dsimp only [indexPred]
      rw [UInt64.toNat_sub]
      change (2 ^ 64 - 1 + indexCur.toNat) % 2 ^ 64 = indexCur.toNat - 1
      have heqPred : 2 ^ 64 - 1 + indexCur.toNat =
          2 ^ 64 + (indexCur.toNat - 1) := by omega
      rw [heqPred, Nat.add_mod]
      simp only [Nat.mod_self, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have wfNext : nextCtx.spec.WellFormed :=
      Rewriter.replaceValue?_WellFormed (Sim.ValuePtr.fromOpResultPtr oldResult)
        (Sim.ValuePtr.fromOpResultPtr newResult)
        (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind]) ctxInCur wf hReplace
    intro i hi
    by_cases hlt : i < indexPred.toNat
    · exact ih wfNext heq i hlt
    · have hieq : i = indexPred.toNat := by omega
      subst i
      have hFromNext : fromOp.InBounds nextCtx := by grind [generic_ptr_grind]
      have hToNext : toOp.InBounds nextCtx := by grind [generic_ptr_grind]
      have hFromIndex : indexPred.toNat < fromOp.spec.getNumResults! nextCtx.spec := by
        rw [Rewriter.replaceValue?_preserves_results_size fromOp fromInCur hReplace]
        rw [hPred]
        omega
      have hToIndex : indexPred.toNat < toOp.spec.getNumResults! nextCtx.spec := by
        rw [Rewriter.replaceValue?_preserves_results_size toOp toInCur hReplace]
        rw [hPred]
        omega
      have heq' : Rewriter.replaceOpResults nextCtx fromOp toOp indexPred hFromNext
          hToNext (Nat.le_of_lt hFromIndex) (Nat.le_of_lt hToIndex) wfNext.inBounds =
          some newCtx := by
        simp only [Rewriter.replaceOpResults_def]
        exact heq
      have hKeep := OpResult.hasUses_replaceOpResults_self_ge
        nextCtx fromOp toOp indexPred hFromNext hToNext
        (Nat.le_of_lt hFromIndex) (Nat.le_of_lt hToIndex) wfNext.inBounds wfNext neOps heq'
        indexPred.toNat (by omega) hFromIndex hToIndex
      have hNoUses := ValuePtr.hasUses!_replaceValue?_oldValue
        (Sim.ValuePtr.fromOpResultPtr oldResult) (Sim.ValuePtr.fromOpResultPtr newResult)
        (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind]) ctxInCur hReplace
      have hNoUses' :
          (ValuePtr.opResult (fromOp.spec.getResult indexPred.toNat)).hasUses!
            nextCtx.spec = false := by
        simpa only [oldResult, Sim.ValuePtr.fromOpResultPtr,
          Sim.OperationPtr.getResultPtr_def, Sim.OperationPtr.getResultPtrSim] using hNoUses
      exact hKeep.trans hNoUses'

@[grind .]
theorem OperationPtr.getNumResults!_replaceOpResults
    (op : Sim.OperationPtr) (opIn : op.InBounds ctx)
    (heq : Rewriter.replaceOpResults ctx fromOp toOp index fromOpIB toOpIB
      hNumFrom hNumTo ctxInBounds = some newCtx) :
    op.spec.getNumResults! newCtx.spec = op.spec.getNumResults! ctx.spec := by
  simp only [Rewriter.replaceOpResults_def] at heq
  fun_induction Rewriter.replaceOpResultsSim <;>
    grind [Rewriter.replaceValue?_preserves_results_size, generic_ptr_grind]

@[grind .]
theorem OperationPtr.getNumRegions!_replaceOpResults
    (op : Sim.OperationPtr) (opIn : op.InBounds ctx)
    (heq : Rewriter.replaceOpResults ctx fromOp toOp index fromOpIB toOpIB
      hNumFrom hNumTo ctxInBounds = some newCtx) :
    op.spec.getNumRegions! newCtx.spec = op.spec.getNumRegions! ctx.spec := by
  simp only [Rewriter.replaceOpResults_def] at heq
  fun_induction Rewriter.replaceOpResultsSim <;>
    grind [Rewriter.replaceValue?_preserves_numRegions, generic_ptr_grind]

theorem OperationPtr.hasUses_replaceOpResults
    (ctx : Sim.IRContext OpInfo) (fromOp toOp : Sim.OperationPtr) (index : UInt64)
    (fromOpIB : fromOp.InBounds ctx) (toOpIB : toOp.InBounds ctx)
    (hNumFrom : index.toNat ≤ fromOp.spec.getNumResults! ctx.spec)
    (hNumTo : index.toNat ≤ toOp.spec.getNumResults! ctx.spec)
    (ctxInBounds : ctx.spec.FieldsInBounds) (wf : ctx.spec.WellFormed)
    (neOps : fromOp.spec ≠ toOp.spec)
    (hIndex : index.toNat = fromOp.spec.getNumResults! ctx.spec)
    (heq : Rewriter.replaceOpResults ctx fromOp toOp index fromOpIB toOpIB
      hNumFrom hNumTo ctxInBounds = some newCtx) :
    fromOp.spec.hasUses! newCtx.spec = false := by
  rw [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
  intro i hi
  have hi' : i < fromOp.spec.getNumResults! ctx.spec := by
    rw [← OperationPtr.getNumResults!_replaceOpResults fromOp fromOpIB heq]
    exact hi
  exact OpResult.hasUses_replaceOpResults_self ctx fromOp toOp index fromOpIB toOpIB
    hNumFrom hNumTo ctxInBounds wf neOps heq i (by rw [hIndex]; exact hi')

theorem Sim.IRContext.wellFormed_replaceOp?
    (ctx : Sim.IRContext OpInfo) (oldOp newOp : Sim.OperationPtr)
    (oldIn : oldOp.InBounds ctx) (newIn : newOp.InBounds ctx)
    (ctxIn : ctx.spec.WellFormed)
    (hpar : (oldOp.spec.get! ctx.spec).parent.isSome = true)
    (wf : ctx.spec.WellFormed)
    (neOps : oldOp.spec ≠ newOp.spec)
    (noRegions : oldOp.spec.getNumRegions! ctx.spec = 0)
    (hErase : ∀ (index : UInt64)
      (hNumFrom : index.toNat ≤ oldOp.spec.getNumResults! ctx.spec)
      (hNumTo : index.toNat ≤ newOp.spec.getNumResults! ctx.spec)
      (ctxInBounds : ctx.spec.FieldsInBounds) (replacedCtx : Sim.IRContext OpInfo),
      index.toNat = oldOp.spec.getNumResults! ctx.spec →
      Rewriter.replaceOpResults ctx oldOp newOp index oldIn newIn hNumFrom hNumTo
        ctxInBounds = some replacedCtx →
      Rewriter.EraseOpDeallocFieldsInBounds replacedCtx oldOp := by
        intro index hNumFrom hNumTo ctxInBounds replacedCtx hIndex hReplace
        apply Rewriter.eraseOp_deallocFieldsInBounds
        · exact Sim.IRContext.wellFormed_replaceOpResults oldOp newOp index oldIn newIn
            hNumFrom hNumTo ctxInBounds wf hReplace
        · rw [OperationPtr.getNumRegions!_replaceOpResults oldOp oldIn hReplace]
          exact noRegions
        · exact OperationPtr.hasUses_replaceOpResults ctx oldOp newOp index oldIn newIn
            hNumFrom hNumTo ctxInBounds wf neOps hIndex hReplace)
    (heq : Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar wf hErase =
      some newCtx) :
    newCtx.spec.WellFormed := by
  simp only [Rewriter.replaceOp?_def, Rewriter.replaceOp?Sim] at heq
  split at heq
  · simp at heq
  · split at heq
    · simp at heq
    · rename_i replacedCtx hReplace
      simp only [Option.some.injEq] at heq
      rw [← heq]
      apply Rewriter.eraseOp_WellFormed
      · exact Sim.IRContext.wellFormed_replaceOpResults oldOp newOp
          (oldOp.getNumResults ctx oldIn) oldIn newIn
          (by grind) (by grind) (by grind) wf hReplace
      · grind
      · apply OperationPtr.hasUses_replaceOpResults ctx oldOp newOp
            (oldOp.getNumResults ctx oldIn) oldIn newIn
            (by grind) (by grind) (by grind) wf neOps
        · have hOldWf := wf.operations oldOp.spec oldIn.ib
          have henc := ctx.sim.encoding_op oldOp.spec oldIn.ib
          have hNumResultsLt : oldOp.spec.getNumResults! ctx.spec < UInt64.size := by
            rw [← hOldWf.capResults_eq_numResults, henc.numResults]
            exact UInt64.toNat_lt _
          rw [Sim.OperationPtr.getNumResults_eq_getNumResults! ctx oldOp oldIn,
            Sim.OperationPtr.getNumResults!_spec_of_wf ctx oldOp (ib := oldIn) wf]
          exact UInt64.toNat_ofNat_of_lt hNumResultsLt
        · exact hReplace

theorem Sim.IRContext.fieldsInBounds_replaceOp?
    (ctx : Sim.IRContext OpInfo) (oldOp newOp : Sim.OperationPtr)
    (oldIn : oldOp.InBounds ctx) (newIn : newOp.InBounds ctx)
    (ctxIn : ctx.spec.WellFormed)
    (hpar : (oldOp.spec.get! ctx.spec).parent.isSome = true)
    (wf : ctx.spec.WellFormed)
    (neOps : oldOp.spec ≠ newOp.spec)
    (noRegions : oldOp.spec.getNumRegions! ctx.spec = 0)
    (hErase : ∀ (index : UInt64)
      (hNumFrom : index.toNat ≤ oldOp.spec.getNumResults! ctx.spec)
      (hNumTo : index.toNat ≤ newOp.spec.getNumResults! ctx.spec)
      (ctxInBounds : ctx.spec.FieldsInBounds) (replacedCtx : Sim.IRContext OpInfo),
      index.toNat = oldOp.spec.getNumResults! ctx.spec →
      Rewriter.replaceOpResults ctx oldOp newOp index oldIn newIn hNumFrom hNumTo
        ctxInBounds = some replacedCtx →
      Rewriter.EraseOpDeallocFieldsInBounds replacedCtx oldOp := by grind)
    (heq : Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar wf hErase =
      some newCtx) :
    newCtx.spec.FieldsInBounds :=
  (Sim.IRContext.wellFormed_replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar wf
    neOps noRegions hErase heq).inBounds

end Veir
