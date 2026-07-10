module

public import Veir.IR
public import Veir.Rewriter.InsertPoint
public import Veir.Rewriter.LinkedList.Basic

import Veir.Rewriter.LinkedList.GetSet
import Veir.IR.WellFormed
import Std.Data.HashSet
import Std.Data.ExtHashSet

public section

namespace Veir
variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
variable {ctx ctx' : Sim.IRContext OpInfo}

attribute [local grind ext] OpOperand

/- OpOperandPtr.insertIntoCurrent -/

theorem Sim.OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent_of_value_ne
    (ctxInBounds : ctx.spec.FieldsInBounds) {use : OpOperandPtr} {use' : Veir.OpOperandPtr}
    {useInBounds : use.InBounds ctx}
    (useOfOtherValue : (use.spec.get! ctx.spec).value ≠ (use'.get! ctx.spec).value) array missingUses
    (hWF : (use.spec.get! ctx.spec).value.DefUse ctx.spec array missingUses) :
    use'.get! (insertIntoCurrent ctx use useInBounds ctxInBounds).spec = use'.get! ctx.spec := by
  grind [ValuePtr.DefUse.ValuePtr_getFirstUse_ne_of_value_ne]

theorem Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_self
    {value : Veir.ValuePtr} {use : Sim.OpOperandPtr} {hvalue : use.spec ∈ missingUses} (useIb : use.InBounds ctx)
    (hWF: value.DefUse ctx.spec array missingUses) :
    value.DefUse (use.insertIntoCurrent ctx (by grind) ctxInBounds).spec (#[use.spec] ++ array) (missingUses.erase use.spec) := by
  have : (use.spec.get! ctx.spec).value = value := by grind [ValuePtr.DefUse.missingUsesValue]
  constructor
  case prevNextUse =>
    simp only [gt_iff_lt, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    simp only [OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent]
    intros i
    cases i <;> grind [ValuePtr.DefUse]
  case nextElems =>
    simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    grind [ValuePtr.DefUse]
  all_goals grind [ValuePtr.DefUse]

theorem Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_self_empty
    {value : Veir.ValuePtr} {use : Sim.OpOperandPtr} (useIb : use.InBounds ctx)
    (hWF: value.DefUse ctx.spec array (Std.ExtHashSet.ofList [use.spec])) :
    value.DefUse (use.insertIntoCurrent ctx (by grind) ctxInBounds).spec (#[use.spec] ++ array) := by
  have : ∅ = (Std.ExtHashSet.ofList [use.spec]).erase use.spec := by grind
  grind [ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_self]

theorem Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_other
    {value value' : Veir.ValuePtr} {use : Sim.OpOperandPtr} (useIb : use.InBounds ctx)
    (valueNe : value ≠ value') (hvalue : use.spec ∈ missingUses')
    (hWF : value.DefUse ctx.spec array missingUses)
    (hWF' : value'.DefUse ctx.spec array' missingUses') :
    value.DefUse (use.insertIntoCurrent ctx (by grind) ctxInBounds).spec array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx.spec) <;> grind [ValuePtr.DefUse]

theorem Sim.BlockPtr.defUse_OpOperandPtr_insertIntoCurrent
    {block : Veir.BlockPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : block.DefUse ctx.spec array missingUses) :
    block.DefUse (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx.spec) <;> grind

theorem Sim.BlockPtr.opChain_OpOperandPtr_insertIntoCurrent
    {block : Veir.BlockPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : block.OpChain ctx.spec array) :
    block.OpChain (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.RegionPtr.blockChain_OpOperandPtr_insertIntoCurrent
    {region : Veir.RegionPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : region.BlockChain ctx.spec array) :
    region.BlockChain (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Operation.wellFormed_OpOperandPtr_insertIntoCurrent
    {opPtr : Veir.OperationPtr} (opInBounds : opPtr.InBounds ctx.spec) {use : OpOperandPtr} {useInBounds}
    (hWF : opPtr.WellFormed ctx.spec (by grind)) :
    opPtr.WellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec (by
      have : opPtr.InBounds (OpOperandPtr.insertIntoCurrent ctx use useInBounds ctxInBounds).spec := by grind [generic_ptr_grind]
      grind [generic_ptr_grind]) := by
  apply OperationPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Block.wellFormed_OpOperandPtr_insertIntoCurrent
    {blockPtr : Veir.BlockPtr} (blockInBounds : blockPtr.InBounds ctx.spec) {use : OpOperandPtr} {useInBounds}
    (hWF : blockPtr.WellFormed ctx.spec (by grind)) :
    blockPtr.WellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec (by
      have : blockPtr.InBounds (OpOperandPtr.insertIntoCurrent ctx use useInBounds ctxInBounds).spec := by grind [generic_ptr_grind]
      grind) := by
  apply BlockPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Region.wellFormed_OpOperandPtr_insertIntoCurrent
    {regionPtr : Veir.RegionPtr} (regionInBounds : regionPtr.InBounds ctx.spec) {use : OpOperandPtr} {useInBounds}
    (hWF : regionPtr.WellFormed ctx.spec) :
    regionPtr.WellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec := by
  apply RegionPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.IRContext.wellFormed_OpOperandPtr_insertIntoCurrent
    {ctx : Sim.IRContext OpInfo} {use : OpOperandPtr} (useInBounds : use.InBounds ctx) {ctxInBounds}
    (useMissing : use.spec ∈ missingOperandUses)
    (hWF : ctx.spec.WellFormed missingOperandUses missingSuccessorUses) :
    (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec.WellFormed (missingOperandUses.erase use.spec) missingSuccessorUses := by
  constructor
  · grind
  · intros valuePtr valuePtrInBounds
    have ⟨array, h⟩ := hWF.valueDefUseChains valuePtr (by grind)
    by_cases hvalue: (use.spec.get! ctx.spec).value = valuePtr
    · apply Exists.intro _
      simp only [Std.ExtHashSet.filter_erase_eq]
      apply Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_self
      · grind
      · assumption
      · apply cast (a := h); congr
        grind
    · let valuePtr' := (use.spec.get! ctx.spec).value
      have ⟨array', h'⟩ := hWF.valueDefUseChains valuePtr' (by grind)
      apply Exists.intro _
      simp only [Std.ExtHashSet.filter_erase_eq]
      apply Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_other useInBounds
        (value' := valuePtr') (by grind) (hWF' := h') (hvalue := by grind)
      apply cast (a := h); congr
      ext; grind
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.blockDefUseChains blockPtr (by grind)
    apply Exists.intro array
    apply Sim.BlockPtr.defUse_OpOperandPtr_insertIntoCurrent
    grind
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.opChain blockPtr (by grind)
    apply Exists.intro array
    apply Sim.BlockPtr.opChain_OpOperandPtr_insertIntoCurrent
    apply h
  · intros regionPtr regionPtrInBounds
    have ⟨_, h⟩ := hWF.blockChain regionPtr (by grind)
    apply Exists.intro _
    apply Sim.RegionPtr.blockChain_OpOperandPtr_insertIntoCurrent
    apply h
  · intros opPtr opPtrInBounds
    have := hWF.operations opPtr (by grind)
    grind [Sim.Operation.wellFormed_OpOperandPtr_insertIntoCurrent]
  · intros blockPtr blockPtrInBounds
    have := hWF.blocks blockPtr (by grind)
    grind [Sim.Block.wellFormed_OpOperandPtr_insertIntoCurrent]
  · intros regionPtr regionPtrInBounds
    have := hWF.regions regionPtr (by grind)
    grind [Sim.Region.wellFormed_OpOperandPtr_insertIntoCurrent]

/- OpOperandPtr.removeFromCurrent -/

theorem Sim.OpOperandPtr.back!_array_getElem_removeFromCurrent_eq_of_DefUse
    {use : Sim.OpOperandPtr} {value : Veir.ValuePtr} {array : Array Veir.OpOperandPtr}
    {useInBounds : use.InBounds ctx} {ctxInBounds}
    (hWF : value.DefUse ctx.spec array missingUses) (useInArray: use.spec ∈ array)
    {i} (iPos : i > 0) (iInBounds : i < (array.erase use.spec).size)
    :
    (((array.erase use.spec)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds).spec).back = Veir.OpOperandPtrPtr.operandNextUse (array.erase use.spec)[i - 1] := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  simp [huseIdx.symm]
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
        grind [ValuePtr.DefUse.erase_getElem_array_eq_eraseIdx]
  have hNextUse : (array[useIdx].get! ctx.spec).nextUse = array[useIdx + 1]? := by grind [ValuePtr.DefUse]
  simp only [hNextUse]
  by_cases i = useIdx
  · subst useIdx
    split <;> grind [ValuePtr.DefUse, Array.getElem?_eraseIdx_of_ge]
  · by_cases i < useIdx <;> grind [ValuePtr.DefUse, ValuePtr.DefUse_array_injective]

theorem Sim.OpOperandPtr.nextUse!_array_getElem_removeFromCurrent_eq_of_DefUse
    {use : Sim.OpOperandPtr} {value : Veir.ValuePtr} {array : Array Veir.OpOperandPtr} {ctxInBounds}
    (useInBounds : Sim.OpOperandPtr.InBounds use ctx)
    (hWF : value.DefUse ctx.spec array missingUses) (useInArray: use.spec ∈ array)
    {i} (iInBounds : i < (array.erase use.spec).size)
    :
    (((array.erase use.spec)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds).spec).nextUse = (array.erase use.spec)[i + 1]? := by
  simp only [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
  have useInArray : use.spec ∈ array := by grind [ValuePtr.DefUse]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  simp only [huseIdx.symm]
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by
    grind [ValuePtr.DefUse.erase_getElem_array_eq_eraseIdx]
  have hNextUse : (array[useIdx].get! ctx.spec).nextUse = array[useIdx + 1]? := by
    grind [ValuePtr.DefUse]
  simp only [hNextUse]
  by_cases i < useIdx <;> grind [ValuePtr.DefUse, ValuePtr.DefUse_array_injective]

theorem Sim.OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse
    {valuePtr : Veir.ValuePtr} {operandPtr : Sim.OpOperandPtr}
    {array array' : Array Veir.OpOperandPtr} {operandPtrInBounds ctxInBounds}
    (valuePtrWF : valuePtr.DefUse ctx.spec array missingUses)
    (operandValueWF : (operandPtr.spec.get! ctx.spec).value.DefUse ctx.spec array' missingUses')
    (operandInArray : operandPtr.spec ∈ array') :
    valuePtr.getFirstUse! (OpOperandPtr.removeFromCurrent ctx operandPtr operandPtrInBounds ctxInBounds).spec =
      if valuePtr.getFirstUse! ctx.spec = some operandPtr.spec then
        (operandPtr.spec.get! ctx.spec).nextUse
      else
        valuePtr.getFirstUse! ctx.spec := by
  simp only [ValuePtr.getFirstUse!_OpOperandPtr_removeFromCurrent]
  congr 1
  simp [ValuePtr.DefUse_getFirstUse!_eq_iff_back_eq_valueFirstUse operandValueWF (by grind) valuePtrWF]

theorem Sim.ValuePtr.DefUse.getElem?_zero_erase_array_eq
    {use : Sim.OpOperandPtr} {value : Veir.ValuePtr} {array : Array Veir.OpOperandPtr} {ctxInBounds}
    (useInBounds : Sim.OpOperandPtr.InBounds use ctx)
    (hWF : Veir.ValuePtr.DefUse value ctx.spec array missingUses) (useInArray: use.spec ∈ array)
    {i} (iInBounds : i < (array.erase use.spec).size) :
    (array.erase use.spec)[0]? = value.getFirstUse! (use.removeFromCurrent ctx useInBounds ctxInBounds).spec := by
  grind [Array.getElem_of_mem, ValuePtr.DefUse]

theorem Sim.ValuePtr.defUse_removeFromCurrent_self
    {value : Veir.ValuePtr} {use : Sim.OpOperandPtr} {array : Array Veir.OpOperandPtr} {ctxInBounds}
    (hvalue : use.spec ∈ array) (useIb : use.InBounds ctx)
    (hWF: value.DefUse ctx.spec array missingUses) :
    value.DefUse (use.removeFromCurrent ctx (by grind) ctxInBounds).spec (array.erase use.spec) (missingUses.insert use.spec) := by
  have hUseValue : (use.spec.get! ctx.spec).value = value := by grind [ValuePtr.DefUse.useValue]
  constructor
  case prevNextUse =>
    grind [OpOperandPtr.back!_array_getElem_removeFromCurrent_eq_of_DefUse, Array.mem_of_mem_erase, ValuePtr.DefUse]
  case nextElems =>
    grind [OpOperandPtr.nextUse!_array_getElem_removeFromCurrent_eq_of_DefUse, Array.mem_of_mem_erase, ValuePtr.DefUse]
  case firstElem =>
    grind [ValuePtr.DefUse.getElem?_zero_erase_array_eq, Array.mem_of_mem_erase, ValuePtr.DefUse]
  case firstUseBack =>
    rw [OpOperandPtr.removeFromCurrent_ValuePtr_getFirstUse hWF (by simp [hUseValue]; exact hWF) (by grind)]
    intros firstUse
    split
    · grind [ValuePtr.DefUse]
    · simp [OpOperandPtr.get!_OpOperandPtr_removeFromCurrent]
      intros heq
      simp only [ValuePtr.DefUse.nextUse!_ne_of_getFirstUse!_eq hWF hvalue
            (by simp [hUseValue]; exact hWF) heq,
        ↓reduceIte]
      grind [ValuePtr.DefUse]
  case allUsesInChain =>
    intros use' use'InBounds hvalue'
    by_cases h: use.spec = use' <;> grind [ValuePtr.DefUse]
  all_goals grind [ValuePtr.DefUse]

theorem Sim.ValuePtr.defUse_removeFromCurrent_other
    {value value' : Veir.ValuePtr} {use : Sim.OpOperandPtr}
    {array array' : Array Veir.OpOperandPtr} {ctxInBounds}
    (valueNe : value ≠ value') {hvalue : use.spec ∈ array'}
    (useIb : use.InBounds ctx)
    (hWF : value.DefUse ctx.spec array missingUses)
    (hWF' : value'.DefUse ctx.spec array' missingUses') :
    value.DefUse (use.removeFromCurrent ctx (by grind) ctxInBounds).spec array missingUses := by
  have : value.InBounds ctx.spec := by grind
  apply ValuePtr.DefUse.unchanged (ctx := ctx.spec) <;> try grind [ValuePtr.DefUse.useValue]
  simp [ValuePtr.getFirstUse!_OpOperandPtr_removeFromCurrent]
  intros h
  have : (use.spec.get! ctx.spec).value = value' := by grind [ValuePtr.DefUse]
  grind [ValuePtr.DefUse.value!_eq_of_back!_eq_valueFirstUse]

theorem Sim.BlockPtr.defUse_OpOperandPtr_removeFromCurrent
    {block : Veir.BlockPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : block.DefUse ctx.spec array missingUses) :
    block.DefUse (use.removeFromCurrent ctx useInBounds ctxInBounds).spec array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx.spec) <;> grind

theorem Sim.BlockPtr.opChain_OpOperandPtr_removeFromCurrent
    {block : Veir.BlockPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : block.OpChain ctx.spec array) :
    block.OpChain (use.removeFromCurrent ctx useInBounds ctxInBounds).spec array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.RegionPtr.blockChain_OpOperandPtr_removeFromCurrent
    {region : Veir.RegionPtr} {use : OpOperandPtr} {useInBounds}
    (hWF : region.BlockChain ctx.spec array) :
    region.BlockChain (use.removeFromCurrent ctx useInBounds ctxInBounds).spec array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Operation.wellFormed_OpOperandPtr_removeFromCurrent
    {opPtr : Veir.OperationPtr} {opInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : opPtr.WellFormed ctx.spec opInBounds) :
    opPtr.WellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds).spec (by grind) := by
  apply OperationPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Block.wellFormed_OpOperandPtr_removeFromCurrent
    {blockPtr : Veir.BlockPtr} {blockInBounds} {use : OpOperandPtr} {useInBounds}
    (hWF : blockPtr.WellFormed ctx.spec blockInBounds) :
    blockPtr.WellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds).spec (by grind) := by
  apply BlockPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Region.wellFormed_OpOperandPtr_removeFromCurrent
    {regionPtr : Veir.RegionPtr} (regionInBounds : regionPtr.InBounds ctx.spec) {use : OpOperandPtr} {useInBounds}
    (hWF : regionPtr.WellFormed ctx.spec) :
    regionPtr.WellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds).spec := by
  apply RegionPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.IRContext.wellFormed_OpOperandPtr_removeFromCurrent
    {ctx : Sim.IRContext OpInfo} {use : OpOperandPtr} {useInBounds} {ctxInBounds}
    (useMissing : use.spec ∉ missingOperandUses)
    (hWF : ctx.spec.WellFormed missingOperandUses missingSuccessorUses) :
    (use.removeFromCurrent ctx useInBounds ctxInBounds).spec.WellFormed (missingOperandUses.insert use.spec) missingSuccessorUses := by
  constructor
  · grind
  · intros valuePtr valuePtrInBounds
    have ⟨array, h⟩ := hWF.valueDefUseChains valuePtr (by grind)
    by_cases hvalue: (use.spec.get! ctx.spec).value = valuePtr
    · apply Exists.intro _
      simp (disch := grind) only [Std.ExtHashSet.filter_insert_eq_of_true_eq]
      apply Sim.ValuePtr.defUse_removeFromCurrent_self (array := array) (useIb := by grind)
      · grind [h.allUsesInChain]
      · apply cast (a := h); congr
        grind
    · let valuePtr' := (use.spec.get! ctx.spec).value
      have ⟨array', h'⟩ := hWF.valueDefUseChains valuePtr' (by grind)
      apply Exists.intro _
      simp (disch := grind) only [Std.ExtHashSet.filter_insert_eq_of_false_eq]
      apply Sim.ValuePtr.defUse_removeFromCurrent_other (useIb := by grind)
        (value' := valuePtr') (by grind) (hWF' := h')
      · apply cast (a := h); congr
        grind
      · grind [h'.allUsesInChain]
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.blockDefUseChains blockPtr (by grind)
    apply Exists.intro array
    apply Sim.BlockPtr.defUse_OpOperandPtr_removeFromCurrent
    grind
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.opChain blockPtr (by grind)
    apply Exists.intro array
    apply Sim.BlockPtr.opChain_OpOperandPtr_removeFromCurrent
    apply h
  · intros regionPtr regionPtrInBounds
    have ⟨_, h⟩ := hWF.blockChain regionPtr (by grind)
    apply Exists.intro _
    apply Sim.RegionPtr.blockChain_OpOperandPtr_removeFromCurrent
    apply h
  · intros opPtr opPtrInBounds
    have := hWF.operations opPtr (by grind)
    grind [Sim.Operation.wellFormed_OpOperandPtr_removeFromCurrent]
  · intros blockPtr blockPtrInBounds
    have := hWF.blocks blockPtr (by grind)
    grind [Sim.Block.wellFormed_OpOperandPtr_removeFromCurrent]
  · intros regionPtr regionPtrInBounds
    have := hWF.regions regionPtr (by grind)
    grind [Sim.Region.wellFormed_OpOperandPtr_removeFromCurrent]

section BlockOperandPtr.insertIntoCurrent

theorem Sim.BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne
    (ctxInBounds : ctx.spec.FieldsInBounds) {use use' : Sim.BlockOperandPtr}
    {useInBounds : use.InBounds ctx}
    (useOfOtherValue : (use.spec.get! ctx.spec).value ≠ (use'.spec.get! ctx.spec).value) array missingUses
    (hWF : (use.spec.get! ctx.spec).value.DefUse ctx.spec array missingUses) :
    use'.spec.get! (insertIntoCurrent ctx use useInBounds ctxInBounds).spec = use'.spec.get! ctx.spec := by
  simp only [BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent]
  have := BlockPtr.DefUse.getFirstUse_ne_of_value_ne useOfOtherValue hWF
  simp only [this, ↓reduceIte]
  have : use.spec ≠ use'.spec := by grind
  simp [this]

theorem Sim.BlockPtr.defUse_BlockOperandPtr_insertIntoCurrent_self
    {block : Veir.BlockPtr} {use : Sim.BlockOperandPtr} {hvalue : use.spec ∈ missingUses}
    (useIb : use.InBounds ctx) (hWF: block.DefUse ctx.spec array missingUses) :
    block.DefUse (use.insertIntoCurrent ctx (by grind) ctxInBounds).spec (#[use.spec] ++ array) (missingUses.erase use.spec) := by
  have : (use.spec.get! ctx.spec).value = block := by grind [BlockPtr.DefUse.missingUsesValue]
  constructor
  case backNextUse =>
    simp only [gt_iff_lt, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    simp only [BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent]
    intros i
    cases i <;> grind [BlockPtr.DefUse]
  case nextElems =>
    simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add]
    grind [BlockPtr.DefUse]
  all_goals grind [BlockPtr.DefUse]

theorem Sim.BlockPtr.defUse_BlockOperandPtr_insertIntoCurrent_self_empty
    {block : Veir.BlockPtr} {use : Sim.BlockOperandPtr} (useIb : use.InBounds ctx)
    (hWF: block.DefUse ctx.spec array (Std.ExtHashSet.ofList [use.spec])) :
    block.DefUse (use.insertIntoCurrent ctx (by grind [BlockPtr.DefUse.missingUsesInBounds]) ctxInBounds).spec (#[use.spec] ++ array) := by
  have : ∅ = (Std.ExtHashSet.ofList [use.spec]).erase use.spec := by grind
  grind [Sim.BlockPtr.defUse_BlockOperandPtr_insertIntoCurrent_self]

attribute [grind →] BlockPtr.DefUse.missingUsesInBounds

theorem Sim.BlockPtr.defUse_BlockOperandPtr_insertIntoCurrent_other
    {value value' : Veir.BlockPtr} {use : Sim.BlockOperandPtr} (useIb : use.InBounds ctx)
    (valueNe : value ≠ value') {hvalue : use.spec ∈ missingUses'}
    (hWF : value.DefUse ctx.spec array missingUses)
    (hWF' : value'.DefUse ctx.spec array' missingUses') :
    value.DefUse (use.insertIntoCurrent ctx (by grind) ctxInBounds).spec array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx.spec)
  · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
  · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
  · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
  · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
  · intros
    simp [BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent]
    split
    · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
    · split
      · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
      · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
  · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
  · intros
    simp [BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent]
    split
    · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
    · split
      · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]
      · grind [BlockPtr.DefUse, BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent_of_value_ne]

theorem Sim.ValuePtr.defUse_BlockOperandPtr_insertIntoCurrent
    {block : Veir.ValuePtr} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : block.DefUse ctx.spec array missingUses) :
    block.DefUse (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx.spec) <;> grind

theorem Sim.BlockPtr.opChain_BlockOperandPtr_insertIntoCurrent
    {block : Veir.BlockPtr} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : block.OpChain ctx.spec array) :
    block.OpChain (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.RegionPtr.blockChain_BlockOperandPtr_insertIntoCurrent
    {region : Veir.RegionPtr} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : region.BlockChain ctx.spec array) :
    region.BlockChain (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Operation.wellFormed_BlockOperandPtr_insertIntoCurrent
    {opPtr : Veir.OperationPtr} {opInBounds} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : opPtr.WellFormed ctx.spec opInBounds) :
    opPtr.WellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec (by grind) := by
  apply OperationPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Block.wellFormed_BlockOperandPtr_insertIntoCurrent
    {blockPtr : Veir.BlockPtr} {blockInBounds} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : blockPtr.WellFormed ctx.spec blockInBounds) :
    Veir.BlockPtr.WellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec blockPtr (by grind) := by
  apply BlockPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Region.wellFormed_BlockOperandPtr_insertIntoCurrent
    {regionPtr : Veir.RegionPtr} (regionInBounds : regionPtr.InBounds ctx.spec) {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : regionPtr.WellFormed ctx.spec) :
    regionPtr.WellFormed (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec := by
  apply RegionPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.IRContext.wellFormed_BlockOperandPtr_insertIntoCurrent
    {ctx : Sim.IRContext OpInfo} {use : Sim.BlockOperandPtr} {useInBounds} {ctxInBounds}
    (useMissing : use.spec ∈ missingSuccessorUses)
    (hWF : ctx.spec.WellFormed missingOperandUses missingSuccessorUses) :
    (use.insertIntoCurrent ctx useInBounds ctxInBounds).spec.WellFormed
      missingOperandUses (missingSuccessorUses.erase use.spec) := by
  constructor
  · grind
  · intros valuePtr valueptrInBounds
    have ⟨array, h⟩ := hWF.valueDefUseChains valuePtr (by grind)
    apply Exists.intro array
    apply Sim.ValuePtr.defUse_BlockOperandPtr_insertIntoCurrent
    grind
  · intros blockPtr valuePtrInBounds
    have ⟨array, h⟩ := hWF.blockDefUseChains blockPtr (by grind)
    by_cases hvalue: (use.spec.get! ctx.spec).value = blockPtr
    · apply Exists.intro _
      simp only [Std.ExtHashSet.filter_erase_eq]
      apply Sim.BlockPtr.defUse_BlockOperandPtr_insertIntoCurrent_self (array := array) (useIb := by grind)
      · grind
      · apply cast (a := h); congr
        grind
    · let blockPtr' := (use.spec.get! ctx.spec).value
      have ⟨array', h'⟩ := hWF.blockDefUseChains blockPtr' (by grind)
      apply Exists.intro _
      simp only [Std.ExtHashSet.filter_erase_eq]
      apply Sim.BlockPtr.defUse_BlockOperandPtr_insertIntoCurrent_other
        (value' := blockPtr') (by grind) (by grind) (hWF' := h') (hvalue := by grind)
      apply cast (a := h); congr
      ext; grind
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.opChain blockPtr (by grind)
    apply Exists.intro array
    apply Sim.BlockPtr.opChain_BlockOperandPtr_insertIntoCurrent
    apply h
  · intros regionPtr regionPtrInBounds
    have ⟨_, h⟩ := hWF.blockChain regionPtr (by grind)
    apply Exists.intro _
    apply Sim.RegionPtr.blockChain_BlockOperandPtr_insertIntoCurrent
    apply h
  · intros opPtr opPtrInBounds
    have := hWF.operations opPtr (by grind)
    grind [Sim.Operation.wellFormed_BlockOperandPtr_insertIntoCurrent]
  · intros blockPtr blockPtrInBounds
    have := hWF.blocks blockPtr (by grind)
    grind [Sim.Block.wellFormed_BlockOperandPtr_insertIntoCurrent]
  · intros regionPtr regionPtrInBounds
    have := hWF.regions regionPtr (by grind)
    grind [Sim.Region.wellFormed_BlockOperandPtr_insertIntoCurrent]

end BlockOperandPtr.insertIntoCurrent

section BlockOperandPtr.removeFromCurrent

attribute [local grind ext] BlockOperand

theorem Sim.BlockOperandPtr.back!_array_getElem_BlockOperandPtr_removeFromCurrent_eq_of_DefUse
    {use : Sim.BlockOperandPtr} {block : Veir.BlockPtr} {array : Array Veir.BlockOperandPtr}
    {useInBounds : use.InBounds ctx} {ctxInBounds}
    (hWF : block.DefUse ctx.spec array missingUses) (useInArray: use.spec ∈ array)
    {i} (iPos : i > 0) (iInBounds : i < (array.erase use.spec).size)
    :
    (((array.erase use.spec)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds).spec).back =
    Veir.BlockOperandPtrPtr.blockOperandNextUse (array.erase use.spec)[i - 1] := by
  simp only [BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  simp [← huseIdx]
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by grind
  have hNextUse : (array[useIdx].get! ctx.spec).nextUse = array[useIdx + 1]? := by grind [BlockPtr.DefUse]
  simp only [hNextUse]
  by_cases i = useIdx
  · subst useIdx
    split <;> grind [BlockPtr.DefUse, Array.getElem?_eraseIdx_of_ge]
  · by_cases i < useIdx <;> grind [BlockPtr.DefUse, BlockPtr.DefUse_array_injective]

theorem Sim.BlockOperandPtr.nextUse!_array_getElem_BlockOperandPtr_removeFromCurrent_eq_of_DefUse
    {use : Sim.BlockOperandPtr} {value : Veir.BlockPtr} {array : Array Veir.BlockOperandPtr} {ctxInBounds}
    (useInBounds : Sim.BlockOperandPtr.InBounds use ctx)
    (hWF : value.DefUse ctx.spec array missingUses) (useInArray: use.spec ∈ array)
    {i} (iInBounds : i < (array.erase use.spec).size)
    :
    (((array.erase use.spec)[i]).get! (removeFromCurrent ctx use useInBounds ctxInBounds).spec).nextUse = (array.erase use.spec)[i + 1]? := by
  simp only [BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent]
  have useInArray : use.spec ∈ array := by grind [ValuePtr.DefUse]
  have ⟨useIdx, useIdxInBounds, huseIdx⟩ := Array.getElem_of_mem useInArray
  simp only [← huseIdx]
  have herase : (array.erase (array[useIdx]'(by grind))) = array.eraseIdx useIdx (by grind) := by grind
  have hNextUse : (array[useIdx].get! ctx.spec).nextUse = array[useIdx + 1]? := by grind [BlockPtr.DefUse]
  simp only [hNextUse]
  by_cases i < useIdx <;> grind [BlockPtr.DefUse, BlockPtr.DefUse_array_injective]

theorem Sim.BlockOperandPtr.BlockOperandPtr_removeFromCurrent_BlockPtr_getFirstUse!
    {blockPtr : Veir.BlockPtr} {operandPtr : Sim.BlockOperandPtr}
    {array array' : Array Veir.BlockOperandPtr} {operandPtrInBounds ctxInBounds}
    (valuePtrWF : blockPtr.DefUse ctx.spec array missingUses)
    (operandValueWF : (operandPtr.spec.get! ctx.spec).value.DefUse ctx.spec array' missingUses')
    (operandInArray : operandPtr.spec ∈ array') :
    (blockPtr.get! (BlockOperandPtr.removeFromCurrent ctx operandPtr operandPtrInBounds ctxInBounds).spec).firstUse =
      if (blockPtr.get! ctx.spec).firstUse = some operandPtr.spec then
        (operandPtr.spec.get! ctx.spec).nextUse
      else
        (blockPtr.get! ctx.spec).firstUse := by
  simp only [BlockPtr.firstUse!_BlockOperandPtr_removeFromCurrent]
  congr 1
  simp [BlockPtr.DefUse_getFirstUse!_eq_iff_back_eq_valueFirstUse operandValueWF (by grind) valuePtrWF]

theorem Sim.BlockPtr.DefUse.getElem?_zero_erase_array_eq
    {use : Sim.BlockOperandPtr} {block : Veir.BlockPtr} {array : Array Veir.BlockOperandPtr} {ctxInBounds}
    (useInBounds : Sim.BlockOperandPtr.InBounds use ctx)
    (hWF : Veir.BlockPtr.DefUse block ctx.spec array missingUses) (useInArray: use.spec ∈ array)
    {i} (iInBounds : i < (array.erase use.spec).size) :
    (array.erase use.spec)[0]? = (block.get! (use.removeFromCurrent ctx useInBounds ctxInBounds).spec).firstUse := by
  grind [Array.getElem_of_mem, BlockPtr.DefUse, BlockPtr.DefUse.erase_getElem_array_eq_eraseIdx]

theorem Sim.BlockPtr.defUse_removeFromCurrent_self
    {block : Veir.BlockPtr} {use : Sim.BlockOperandPtr} {array : Array Veir.BlockOperandPtr} {ctxInBounds}
    {hvalue : use.spec ∈ array} (useIb : use.InBounds ctx)
    (hWF: block.DefUse ctx.spec array missingUses) :
    block.DefUse (use.removeFromCurrent ctx (by grind) ctxInBounds).spec (array.erase use.spec) (missingUses.insert use.spec) := by
  have hUseValue : (use.spec.get! ctx.spec).value = block := by grind [BlockPtr.DefUse.useValue]
  constructor
  case backNextUse =>
    grind [BlockOperandPtr.back!_array_getElem_BlockOperandPtr_removeFromCurrent_eq_of_DefUse, Array.mem_of_mem_erase, BlockPtr.DefUse]
  case nextElems =>
    grind [BlockOperandPtr.nextUse!_array_getElem_BlockOperandPtr_removeFromCurrent_eq_of_DefUse, Array.mem_of_mem_erase, BlockPtr.DefUse]
  case firstElem =>
    grind [BlockPtr.DefUse.getElem?_zero_erase_array_eq, Array.mem_of_mem_erase, BlockPtr.DefUse]
  case firstUseBack =>
    rw [BlockOperandPtr.BlockOperandPtr_removeFromCurrent_BlockPtr_getFirstUse! hWF (by simp [hUseValue]; exact hWF) (by grind)]
    intros firstUse
    split
    · grind [BlockPtr.DefUse]
    · simp [BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent]
      intros heq
      simp only [BlockPtr.DefUse.nextUse!_ne_of_getFirstUse!_eq hWF hvalue
            (by simp [hUseValue]; exact hWF) heq,
        ↓reduceIte]
      grind [BlockPtr.DefUse]
  case allUsesInChain =>
    intros use' use'InBounds hvalue'
    by_cases h: use.spec = use' <;> grind [BlockPtr.DefUse]
  all_goals grind [BlockPtr.DefUse]

theorem Sim.BlockPtr.defUse_BlockOperandPtr_removeFromCurrent_other
    {block block' : Veir.BlockPtr} {use : Sim.BlockOperandPtr} (useIb : use.InBounds ctx)
    {array array' : Array Veir.BlockOperandPtr} {ctxInBounds}
    (valueNe : block ≠ block') {hvalue : use.spec ∈ array'}
    (hWF : block.DefUse ctx.spec array missingUses)
    (hWF' : block'.DefUse ctx.spec array' missingUses') :
    block.DefUse (use.removeFromCurrent ctx (by grind) ctxInBounds).spec array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx.spec) <;>
    grind [BlockPtr.DefUse, BlockPtr.DefUse.value!_eq_of_back!_eq_valueFirstUse]

theorem Sim.ValuePtr.defUse_BlockOperandPtr_removeFromCurrent
    {value : Veir.ValuePtr} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : value.DefUse ctx.spec array missingUses) :
    value.DefUse (use.removeFromCurrent ctx useInBounds ctxInBounds).spec array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx.spec) <;> grind

theorem Sim.BlockPtr.opChain_BlockOperandPtr_removeFromCurrent
    {block : Veir.BlockPtr} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : block.OpChain ctx.spec array) :
    block.OpChain (use.removeFromCurrent ctx useInBounds ctxInBounds).spec array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.RegionPtr.blockChain_BlockOperandPtr_removeFromCurrent
    {region : Veir.RegionPtr} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : region.BlockChain ctx.spec array) :
    region.BlockChain (use.removeFromCurrent ctx useInBounds ctxInBounds).spec array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Operation.wellFormed_BlockOperandPtr_removeFromCurrent
    {opPtr : Veir.OperationPtr} {opInBounds} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : opPtr.WellFormed ctx.spec opInBounds) :
    opPtr.WellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds).spec (by grind) := by
  apply OperationPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Block.wellFormed_BlockOperandPtr_removeFromCurrent
    {blockPtr : Veir.BlockPtr} {blockInBounds} {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : blockPtr.WellFormed ctx.spec blockInBounds) :
    blockPtr.WellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds).spec (by grind) := by
  apply BlockPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Region.wellFormed_BlockOperandPtr_removeFromCurrent
    {regionPtr : Veir.RegionPtr} (regionInBounds : regionPtr.InBounds ctx.spec) {use : Sim.BlockOperandPtr} {useInBounds}
    (hWF : regionPtr.WellFormed ctx.spec) :
    regionPtr.WellFormed (use.removeFromCurrent ctx useInBounds ctxInBounds).spec := by
  apply RegionPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.IRContext.wellFormed_BlockOperandPtr_removeFromCurrent
    {ctx : Sim.IRContext OpInfo} {use : Sim.BlockOperandPtr} {useInBounds} {ctxInBounds}
    (useMissing : use.spec ∉ missingSuccessorUses)
    (hWF : ctx.spec.WellFormed missingOperandUses missingSuccessorUses) :
    (use.removeFromCurrent ctx useInBounds ctxInBounds).spec.WellFormed
      missingOperandUses (missingSuccessorUses.insert use.spec) := by
  constructor
  · grind
  · intros valuePtr valuePtrInBounds
    have ⟨array, h⟩ := hWF.valueDefUseChains valuePtr (by grind)
    apply Exists.intro array
    apply Sim.ValuePtr.defUse_BlockOperandPtr_removeFromCurrent
    grind
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.blockDefUseChains blockPtr (by grind)
    by_cases hvalue: (use.spec.get! ctx.spec).value = blockPtr
    · apply Exists.intro _
      simp (disch := grind) only [Std.ExtHashSet.filter_insert_eq_of_true_eq]
      apply Sim.BlockPtr.defUse_removeFromCurrent_self (array := array)
        <;> grind [h.allUsesInChain]
    · let blockPtr' := (use.spec.get! ctx.spec).value
      have ⟨array', h'⟩ := hWF.blockDefUseChains blockPtr' (by grind)
      apply Exists.intro _
      simp (disch := grind) only [Std.ExtHashSet.filter_insert_eq_of_false_eq]
      apply Sim.BlockPtr.defUse_BlockOperandPtr_removeFromCurrent_other
        (block' := blockPtr') (by grind) (by grind) (hWF' := h')
      · apply cast (a := h); congr
        grind
      · grind [h'.allUsesInChain]
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.opChain blockPtr (by grind)
    apply Exists.intro array
    apply Sim.BlockPtr.opChain_BlockOperandPtr_removeFromCurrent
    apply h
  · intros regionPtr regionPtrInBounds
    have ⟨_, h⟩ := hWF.blockChain regionPtr (by grind)
    apply Exists.intro _
    apply Sim.RegionPtr.blockChain_BlockOperandPtr_removeFromCurrent
    apply h
  · intros opPtr opPtrInBounds
    have := hWF.operations opPtr (by grind)
    grind [Sim.Operation.wellFormed_BlockOperandPtr_removeFromCurrent]
  · intros blockPtr blockPtrInBounds
    have := hWF.blocks blockPtr (by grind)
    grind [Sim.Block.wellFormed_BlockOperandPtr_removeFromCurrent]
  · intros regionPtr regionPtrInBounds
    have := hWF.regions regionPtr (by grind)
    grind [Sim.Region.wellFormed_BlockOperandPtr_removeFromCurrent]

end BlockOperandPtr.removeFromCurrent

section OperationPtr.linkBetweenWithParent

variable {op : Sim.OperationPtr}
variable {newCtx : Sim.IRContext OpInfo}
variable {prevOp nextOp : Sim.OptionOperationPtr}
variable {selfIn : op.InBounds ctx} {prevIn : prevOp.InBounds ctx} {nextIn : nextOp.InBounds ctx}

theorem Sim.ValuePtr.defUse_OperationPtr_linkBetweenWithParent
    {value : Veir.ValuePtr}
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    ValuePtr.DefUse value ctx.spec array missingUses →
    ValuePtr.DefUse value newCtx.spec array missingUses := by
  intros
  apply ValuePtr.DefUse.unchanged (ctx := ctx.spec) <;> grind


theorem Sim.BlockPtr.defUse_OperationPtr_linkBetweenWithParent
    {block : Veir.BlockPtr}
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    BlockPtr.DefUse block ctx.spec array missingUses →
    BlockPtr.DefUse block newCtx.spec array missingUses := by
  intros
  apply BlockPtr.DefUse.unchanged (ctx := ctx.spec) <;> grind

set_option maxHeartbeats 400000 in
theorem Sim.BlockPtr.opChain_OperationPtr_linkBetweenWithParent_self
    {block : Sim.BlockPtr} {parentIn : block.InBounds ctx}
    (ctxWf : ctx.spec.WellFormed)
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp block selfIn prevIn nextIn parentIn = some newCtx)
    (ip : InsertPoint)
    (ipRepr : ip.IsRepr)
    (ipInBounds : ip.InBounds ctx.spec)
    (ipBlock : ip.block! ctx.spec = some block.spec)
    (ipNext : ip.next = nextOp)
    (ipPrev : ip.prev! ctx.spec = prevOp.spec)
    (hOpChain : BlockPtr.OpChain block.spec ctx.spec array) :
    BlockPtr.OpChain block.spec newCtx.spec (array.insertIdx (ip.idxIn ctx.spec block.spec (by grind) (by grind) (by grind) ctxWf) op.spec (by
      have := @InsertPoint.idxIn.le_size_array; grind)) := by
  constructor
  case blockInBounds => grind
  case arrayInBounds => grind [Array.mem_insertIdx, BlockPtr.OpChain]
  case missingOpInBounds => grind
  case opParent => grind [Array.mem_insertIdx, BlockPtr.OpChain]
  case missingOpValue => grind
  case allOpsInChain => grind [Array.mem_insertIdx, BlockPtr.OpChain]
  case first =>
    grind [InsertPoint.idxIn_InsertPoint_prev_none, BlockPtr.OpChain]
  case last =>
    simp only [Array.size_insertIdx, Nat.add_one_sub_one, Nat.lt_add_one, getElem?_pos]
    grind [InsertPoint.next_eq_none_iff_idxIn_eq_size_array, BlockPtr.OpChain]
  case prevFirst =>
    grind [BlockPtr.OpChain]
  case prev =>
    intro i hi₁ hi₂
    let idx := ip.idxIn ctx.spec block.spec (by grind) (by grind) (by grind)
    have : nextOp.spec = array[idx]? := by grind
    by_cases h₁ : i < idx
    · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
    · by_cases h₂ : i = idx
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
      · by_cases h₃ : i - 1 = idx
        · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
        · simp only [Array.size_insertIdx] at hi₂
          simp (disch := grind) only [Array.getElem_insertIdx_of_gt]
          grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
  case next =>
    intro i hi
    simp only [Array.size_insertIdx] at hi
    let idx := ip.idxIn ctx.spec block.spec (by grind) (by grind) (by grind)
    have : nextOp.spec = array[idx]? := by grind
    by_cases h₁ : i + 1 < idx
    · grind (instances := 2000) [BlockPtr.OpChain]
    · by_cases h₂ : i + 1 = idx
      · have := @InsertPoint.prev!_eq_GetElem!_idxIn
        grind
      · by_cases h₃ : i = idx
        · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
        · have : i > idx := by grind
          cases hidx : idx <;> grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]


theorem Sim.BlockPtr.opChain_OperationPtr_linkBetweenWithParent_other
    {block : Sim.BlockPtr} {block' : Veir.BlockPtr} {parentIn : block.InBounds ctx}
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp block selfIn prevIn nextIn parentIn = some newCtx)
    (prevParent : prevOp.spec.maybe₁ (fun prev => (prev.get! ctx.spec).parent = some block.spec) )
    (nextParent : nextOp.spec.maybe₁ (fun next => (next.get! ctx.spec).parent = some block.spec) )
    (hNeBlock : block.spec ≠ block') :
    BlockPtr.OpChain block' ctx.spec array →
    BlockPtr.OpChain block' newCtx.spec array := by
  intros opChain
  apply BlockPtr.OpChain_unchanged (ctx := ctx.spec) <;>
     grind [InsertPoint.prev.maybe₁_parent, Option.maybe₁_def]

theorem Sim.RegionPtr.blockChain_OperationPtr_linkBetweenWithParent
    {region : Veir.RegionPtr}
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    RegionPtr.BlockChain region ctx.spec array →
    RegionPtr.BlockChain region newCtx.spec array := by
  intros
  apply RegionPtr.blockChain_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Operation.wellFormed_OperationPtr_linkBetweenWithParent
    {parentBlock : Sim.BlockPtr} {parentIn : parentBlock.InBounds ctx}
    {opPtr : Veir.OperationPtr} {opInBounds : opPtr.InBounds ctx.spec}
    (prevOpParent : prevOp.spec.maybe₁ (fun prev => (prev.get! ctx.spec).parent = some parentBlock.spec))
    (nextOpParent : nextOp.spec.maybe₁ (fun next => (next.get! ctx.spec).parent = some parentBlock.spec))
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    Veir.OperationPtr.WellFormed ctx.spec opPtr opInBounds →
    Veir.OperationPtr.WellFormed newCtx.spec opPtr (by grind) := by
  intro wf
  constructor
  case region_parent =>
    intro region regionInBounds
    apply OperationPtr.WellFormed.region_parent.unchanged (ctx := ctx.spec) <;> grind [IRContext.WellFormed, OperationPtr.WellFormed]
  all_goals grind [Option.maybe₁_def, IRContext.WellFormed, OperationPtr.WellFormed]

theorem Sim.Block.wellFormed_OperationPtr_linkBetweenWithParent
    {parentBlock : Sim.BlockPtr} {parentIn : parentBlock.InBounds ctx}
    {blockPtr : Veir.BlockPtr} {blockInBounds : blockPtr.InBounds ctx.spec}
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    Veir.BlockPtr.WellFormed ctx.spec blockPtr blockInBounds →
    Veir.BlockPtr.WellFormed newCtx.spec blockPtr (by grind) := by
  intros
  apply BlockPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Region.wellFormed_OperationPtr_linkBetweenWithParent
    {parentBlock : Sim.BlockPtr} {parentIn : parentBlock.InBounds ctx}
    {regionPtr : Veir.RegionPtr}
    (regionInBounds : regionPtr.InBounds ctx.spec)
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx) :
    Veir.RegionPtr.WellFormed ctx.spec regionPtr →
    Veir.RegionPtr.WellFormed newCtx.spec regionPtr := by
  intros
  apply RegionPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.IRContext.wellFormed_OperationPtr_linkBetweenWithParent
    {parentBlock : Sim.BlockPtr} {parentIn : parentBlock.InBounds ctx}
    (hWF : ctx.spec.WellFormed)
    (hctx : op.linkBetweenWithParent ctx prevOp nextOp parentBlock selfIn prevIn nextIn parentIn = some newCtx)
    (prevOpParent : prevOp.spec.maybe₁ (fun prev => (prev.get! ctx.spec).parent = some parentBlock.spec))
    (nextOpParent : nextOp.spec.maybe₁ (fun next => (next.get! ctx.spec).parent = some parentBlock.spec))
    {ip : InsertPoint}
    (ipRepr : ip.IsRepr)
    (ipInBounds : ip.InBounds ctx.spec)
    (ipBlock : ip.block! ctx.spec = some parentBlock.spec)
    (ipNext : ip.next = nextOp)
    (ipPrev : ip.prev! ctx.spec = prevOp.spec) :
    newCtx.spec.WellFormed := by
  constructor
  · grind
  · intros valuePtr valuePtrInBounds
    have ⟨array, h⟩ := hWF.valueDefUseChains valuePtr (by grind)
    exists array
    grind [Sim.ValuePtr.defUse_OperationPtr_linkBetweenWithParent]
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.blockDefUseChains blockPtr (by grind)
    exists array
    grind [Sim.BlockPtr.defUse_OperationPtr_linkBetweenWithParent]
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.opChain blockPtr (by grind)
    by_cases hBlock : blockPtr = parentBlock.spec
    · subst hBlock
      exact ⟨_, Sim.BlockPtr.opChain_OperationPtr_linkBetweenWithParent_self
        hWF hctx ip ipRepr ipInBounds ipBlock ipNext ipPrev h⟩
    · exact ⟨_, Sim.BlockPtr.opChain_OperationPtr_linkBetweenWithParent_other
        hctx prevOpParent nextOpParent (Ne.symm hBlock) h⟩
  · intros regionPtr regionPtrInBounds
    have ⟨array, h⟩ := hWF.blockChain regionPtr (by grind)
    exists array
    grind [Sim.RegionPtr.blockChain_OperationPtr_linkBetweenWithParent]
  · intros opPtr opPtrInBounds
    have := hWF.operations opPtr (by grind)
    grind [Sim.Operation.wellFormed_OperationPtr_linkBetweenWithParent]
  · intros blockPtr blockPtrInBounds
    have := hWF.blocks blockPtr (by grind)
    grind [Sim.Block.wellFormed_OperationPtr_linkBetweenWithParent]
  · intros regionPtr regionPtrInBounds
    have := hWF.regions regionPtr (by grind)
    grind [Sim.Region.wellFormed_OperationPtr_linkBetweenWithParent]

end OperationPtr.linkBetweenWithParent

section BlockPtr.linkBetweenWithParent

variable {block : Sim.BlockPtr}
variable {newCtx : Sim.IRContext OpInfo}
variable {prevBlock nextBlock : Sim.OptionBlockPtr}
variable {selfIn : block.InBounds ctx} {prevIn : prevBlock.InBounds ctx} {nextIn : nextBlock.InBounds ctx}

theorem Sim.ValuePtr.defUse_BlockPtr_linkBetweenWithParent
    {value : Veir.ValuePtr} {parent : Sim.RegionPtr} {parentIn : parent.InBounds ctx}
    (hctx : block.linkBetweenWithParent ctx prevBlock nextBlock parent selfIn prevIn nextIn parentIn = some newCtx) :
    ValuePtr.DefUse value ctx.spec array missingUses →
    ValuePtr.DefUse value newCtx.spec array missingUses := by
  intros
  apply ValuePtr.DefUse.unchanged (ctx := ctx.spec) <;> grind

theorem Sim.BlockPtr.defUse_BlockPtr_linkBetweenWithParent
    {block' : Veir.BlockPtr} {parent : Sim.RegionPtr} {parentIn : parent.InBounds ctx}
    (hctx : block.linkBetweenWithParent ctx prevBlock nextBlock parent selfIn prevIn nextIn parentIn = some newCtx) :
    BlockPtr.DefUse block' ctx.spec array missingUses →
    BlockPtr.DefUse block' newCtx.spec array missingUses := by
  intros
  apply BlockPtr.DefUse.unchanged (ctx := ctx.spec) <;> grind

theorem Sim.BlockPtr.opChain_BlockPtr_linkBetweenWithParent
    {block' : Veir.BlockPtr} {parent : Sim.RegionPtr} {parentIn : parent.InBounds ctx}
    (hctx : block.linkBetweenWithParent ctx prevBlock nextBlock parent selfIn prevIn nextIn parentIn = some newCtx)
    (hOpChain : BlockPtr.OpChain block' ctx.spec array) :
    BlockPtr.OpChain block' newCtx.spec array := by
  intros
  apply BlockPtr.OpChain_unchanged (ctx := ctx.spec) <;> grind

set_option maxHeartbeats 1000000 in
theorem Sim.RegionPtr.blockChain_BlockPtr_linkBetweenWithParent_self
    {parent : Sim.RegionPtr} {parentIn : parent.InBounds ctx}
    (ctxWf : ctx.spec.WellFormed)
    (hctx : block.linkBetweenWithParent ctx prevBlock nextBlock parent selfIn prevIn nextIn parentIn = some newCtx)
    (bip : BlockInsertPoint)
    (bipRepr : bip.IsRepr)
    (bipInBounds : bip.InBounds ctx.spec)
    (bipRegion : bip.region! ctx.spec = some parent.spec)
    (bipNext : bip.next = nextBlock)
    (bipPrev : bip.prev! ctx.spec = prevBlock.spec)
    (hBlockChain : RegionPtr.BlockChain parent.spec ctx.spec array) :
    RegionPtr.BlockChain parent.spec newCtx.spec
      (array.insertIdx (bip.idxIn ctx.spec parent.spec (by grind) (by grind) (by grind) ctxWf) block.spec (by
        have := @BlockInsertPoint.idxIn.le_size_array; grind)) := by
  constructor
  case inBounds => grind
  case arrayInBounds => grind [Array.mem_insertIdx, RegionPtr.BlockChain]
  case opParent => grind [Array.mem_insertIdx, RegionPtr.BlockChain]
  case allBlocksInChain => grind [Array.mem_insertIdx, RegionPtr.BlockChain]
  case first => grind [RegionPtr.BlockChain]
  case last =>
    simp only [Array.size_insertIdx, Nat.add_one_sub_one, Nat.lt_add_one, getElem?_pos]
    grind (instances := 2000) (splits := 20) [BlockInsertPoint.next_eq_none_iff_idxIn_eq_size_array, RegionPtr.BlockChain]
  case prevFirst =>
    intro bl
    simp only [RegionPtr.firstBlock!_BlockPtr_linkBetweenWithParent hctx, and_true,
      BlockPtr.prev!_BlockPtr_linkBetweenWithParent hctx]
    split
    · have := @BlockPtr.parent!_of_BlockPtr_linkBetweenWithParent_eq
      have := @BlockInsertPoint.BlockPtr_parent!_of_next_eq_some
      grind
    · rename_i hprev
      split
      · subst nextBlock
        simp only [reduceCtorEq, imp_false]
        have ⟨prevOp, hprevOp⟩ := Option.ne_none_iff_exists.mp hprev
        have := @BlockPtr.parent!_of_BlockPtr_linkBetweenWithParent_eq
        have := @BlockInsertPoint.BlockPtr_parent!_of_next_eq_some
        grind [RegionPtr.BlockChain]
      · grind [RegionPtr.BlockChain]
  case prev =>
    intro i hi₁ hi₂
    let idx := bip.idxIn ctx.spec parent.spec (by grind) (by grind) (by grind) ctxWf
    have : nextBlock.spec = array[idx]? := by grind
    by_cases h₁ : i < idx
    · grind (gen := 10) (instances := 2000) [RegionPtr.BlockChain, RegionPtr.BlockChain_array_injective]
    · by_cases h₂ : i = idx
      · grind [RegionPtr.BlockChain, RegionPtr.BlockChain_array_injective,
          BlockInsertPoint.prev!_eq_getElem!_idxIn]
      · by_cases h₃ : i - 1 = idx
        · grind [RegionPtr.BlockChain, RegionPtr.BlockChain_array_injective]
        · grind (splits := 15) (instances := 2000) [RegionPtr.BlockChain, RegionPtr.BlockChain_array_injective]
  case next =>
    intro i hi
    simp only [Array.size_insertIdx] at hi
    let idx := bip.idxIn ctx.spec parent.spec (by grind) (by grind) (by grind) ctxWf
    have : nextBlock.spec = array[idx]? := by grind
    by_cases h₁ : i + 1 < idx
    · grind (instances := 3000) [RegionPtr.BlockChain, RegionPtr.BlockChain_array_injective,
        BlockInsertPoint.prev!_eq_getElem!_idxIn]
    · by_cases h₂ : i + 1 = idx
      · have := @BlockInsertPoint.prev!_eq_getElem!_idxIn
        grind [RegionPtr.BlockChain, RegionPtr.BlockChain_array_injective]
      · by_cases h₃ : i = idx
        · grind [RegionPtr.BlockChain, RegionPtr.BlockChain_array_injective]
        · have : i > idx := by grind
          cases hidx : idx
          · grind [RegionPtr.BlockChain, RegionPtr.BlockChain_array_injective]
          · have := @BlockPtr.parent!_of_BlockPtr_linkBetweenWithParent_eq
            have := @BlockInsertPoint.BlockPtr_parent!_of_next_eq_some
            grind (instances := 5000) [RegionPtr.BlockChain, RegionPtr.BlockChain_array_injective]

theorem Sim.RegionPtr.blockChain_BlockPtr_linkBetweenWithParent_other
    {parent : Sim.RegionPtr} {parentIn : parent.InBounds ctx} {region : Veir.RegionPtr}
    (hctx : block.linkBetweenWithParent ctx prevBlock nextBlock parent selfIn prevIn nextIn parentIn = some newCtx)
    (prevParent : prevBlock.spec.maybe₁ (fun prev => (prev.get! ctx.spec).parent = some parent.spec) )
    (nextParent : nextBlock.spec.maybe₁ (fun next => (next.get! ctx.spec).parent = some parent.spec) )
    (hNeRegion : parent.spec ≠ region) :
    RegionPtr.BlockChain region ctx.spec array →
    RegionPtr.BlockChain region newCtx.spec array := by
  intros blockChain
  apply RegionPtr.blockChain_unchanged (ctx := ctx.spec) <;> grind [Option.maybe₁_def]

theorem Sim.Operation.wellFormed_BlockPtr_linkBetweenWithParent
    {parentRegion : Sim.RegionPtr} {parentIn : parentRegion.InBounds ctx}
    {opPtr : Veir.OperationPtr} {opInBounds : opPtr.InBounds ctx.spec}
    (hctx : block.linkBetweenWithParent ctx prevBlock nextBlock parentRegion selfIn prevIn nextIn parentIn = some newCtx) :
    Veir.OperationPtr.WellFormed ctx.spec opPtr opInBounds →
    Veir.OperationPtr.WellFormed newCtx.spec opPtr (by grind) := by
  intros
  apply OperationPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind

theorem Sim.Block.wellFormed_BlockPtr_linkBetweenWithParent
    {parentRegion : Sim.RegionPtr} {parentIn : parentRegion.InBounds ctx}
    {block' : Veir.BlockPtr} {blockInBounds : block'.InBounds ctx.spec}
    (ctxWf : Veir.IRContext.WellFormed ctx.spec)
    (prevBlockParent : prevBlock.spec.maybe₁ (fun prev => (prev.get! ctx.spec).parent = some parentRegion.spec))
    (nextBlockParent : nextBlock.spec.maybe₁ (fun next => (next.get! ctx.spec).parent = some parentRegion.spec))
    (hctx : block.linkBetweenWithParent ctx prevBlock nextBlock parentRegion selfIn prevIn nextIn parentIn = some newCtx)
    (hWF : Veir.BlockPtr.WellFormed ctx.spec block' blockInBounds) :
    Veir.BlockPtr.WellFormed newCtx.spec block' (by grind) := by
  by_cases hBlock : block' = block.spec <;> constructor <;> grind [BlockPtr.WellFormed, Option.maybe₁_def]

theorem Sim.Region.wellFormed_BlockPtr_linkBetweenWithParent
    {parentRegion : Sim.RegionPtr} {parentIn : parentRegion.InBounds ctx} {region : Veir.RegionPtr}
    (hctx : block.linkBetweenWithParent ctx prevBlock nextBlock parentRegion selfIn prevIn nextIn parentIn = some newCtx)
    (regionInBounds : region.InBounds ctx.spec)
    (hWF : RegionPtr.WellFormed ctx.spec region) :
    RegionPtr.WellFormed newCtx.spec region := by
  by_cases hregion : region = parentRegion.spec
  · constructor <;> try grind [RegionPtr.WellFormed, Option.maybe₁_def]
    simp only [OperationPtr.getRegion!_BlockPtr_linkBetweenWithParent hctx]
    grind [RegionPtr.WellFormed]
  · apply RegionPtr.WellFormed_unchanged (ctx := ctx.spec) <;> grind [RegionPtr.WellFormed]

theorem Sim.IRContext.wellFormed_BlockPtr_linkBetweenWithParent
    {parentRegion : Sim.RegionPtr} {parentIn : parentRegion.InBounds ctx}
    (hWF : ctx.spec.WellFormed)
    (hctx : block.linkBetweenWithParent ctx prevBlock nextBlock parentRegion selfIn prevIn nextIn parentIn = some newCtx)
    (prevBlockParent : prevBlock.spec.maybe₁ (fun prev => (prev.get! ctx.spec).parent = some parentRegion.spec))
    (nextBlockParent : nextBlock.spec.maybe₁ (fun next => (next.get! ctx.spec).parent = some parentRegion.spec))
    {ip : BlockInsertPoint}
    {ipRepr : ip.IsRepr}
    (ipInBounds : ip.InBounds ctx.spec)
    (ipBlock : ip.region! ctx.spec = some parentRegion.spec)
    (ipNext : ip.next = nextBlock)
    (ipPrev : ip.prev! ctx.spec = prevBlock.spec) :
    newCtx.spec.WellFormed := by
  constructor
  · grind
  · intros valuePtr valuePtrInBounds
    have ⟨array, h⟩ := hWF.valueDefUseChains valuePtr (by grind)
    exists array
    grind [Sim.ValuePtr.defUse_BlockPtr_linkBetweenWithParent]
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.blockDefUseChains blockPtr (by grind)
    exists array
    grind [Sim.BlockPtr.defUse_BlockPtr_linkBetweenWithParent]
  · intros regionPtr regionPtrInBounds
    have ⟨array, h⟩ := hWF.opChain regionPtr (by grind)
    exists array
    grind [Sim.BlockPtr.opChain_BlockPtr_linkBetweenWithParent]
  · intros blockPtr blockPtrInBounds
    have ⟨array, h⟩ := hWF.blockChain blockPtr (by grind)
    by_cases hBlock : blockPtr = parentRegion.spec
    · subst hBlock
      exact ⟨_, Sim.RegionPtr.blockChain_BlockPtr_linkBetweenWithParent_self
        hWF hctx ip ipRepr ipInBounds ipBlock ipNext ipPrev h⟩
    · exact ⟨_, Sim.RegionPtr.blockChain_BlockPtr_linkBetweenWithParent_other
        hctx prevBlockParent nextBlockParent (Ne.symm hBlock) h⟩
  · intros opPtr opPtrInBounds
    have := hWF.operations opPtr (by grind)
    grind [Sim.Operation.wellFormed_BlockPtr_linkBetweenWithParent]
  · intros blockPtr blockPtrInBounds
    have := hWF.blocks blockPtr (by grind)
    grind [Sim.Block.wellFormed_BlockPtr_linkBetweenWithParent]
  · intros regionPtr regionPtrInBounds
    have := hWF.regions regionPtr (by grind)
    grind [Sim.Region.wellFormed_BlockPtr_linkBetweenWithParent]

end BlockPtr.linkBetweenWithParent

end Veir
