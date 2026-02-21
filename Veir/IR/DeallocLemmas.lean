module

public import Veir.IR.Basic
public import Veir.IR.WellFormed

import all Veir.IR.Basic -- TODO: encapsulate
import Veir.ForLean
import Veir.IR.Fields
import Veir.IR.GetSet
import Veir.IR.Grind
import Veir.IR.InBounds

public section

/-!
  This file contains lemmas about deallocation of IR constructs.
  Compared to other methods that modify the IRs, deallocation often
  requires well-formedness lemmas to prove the `FieldsInBounds`
  preservation.

  This file is thus used to collect such lemmas without having
  circular imports.
-/

namespace Veir

def Std.ExtHashSet.fromOperands (ctx : IRContext) (op : OperationPtr)
    : Std.ExtHashSet OpOperandPtr :=
  Std.ExtHashSet.ofList ((0...(op.getNumOperands! ctx)).toList.map (fun i => op.getOpOperand i))

def Std.ExtHashSet.fromSuccessors (ctx : IRContext) (op : OperationPtr)
    : Std.ExtHashSet BlockOperandPtr :=
  Std.ExtHashSet.ofList ((0...(op.getNumSuccessors! ctx)).toList.map (fun i => op.getBlockOperand i))

@[grind .]
theorem Std.ExtHashSet.fromSuccessors.mem_ne :
    operand.op ≠ op →
    operand ∉ (Std.ExtHashSet.fromSuccessors ctx op) := by
  simp only [Std.ExtHashSet.fromSuccessors]
  grind [Std.Rco.mem_toList_iff_mem, Std.Rco.mem_iff]

@[grind =]
theorem Std.ExtHashSet.fromSuccessors.mem_iff
    (inBounds : operand.InBounds ctx) :
    (operand ∈ (Std.ExtHashSet.fromSuccessors ctx op) ↔ operand.op = op) := by
  simp only [Std.ExtHashSet.fromSuccessors]
  simp only [Std.ExtHashSet.mem_ofList, List.contains_eq_mem, List.mem_map,
    Std.Rco.mem_toList_iff_mem, Std.Rco.mem_iff, Nat.zero_le, true_and, decide_eq_true_eq]
  constructor
  · grind
  · intro h
    exists operand.index
    constructor
    · grind [OperationPtr.getNumSuccessors!, BlockOperandPtr.InBounds]
    · cases operand
      grind [OperationPtr.getBlockOperand]

@[grind .]
theorem Std.ExtHashSet.fromOperands.mem_ne :
    operand.op ≠ op →
    operand ∉ (Std.ExtHashSet.fromOperands ctx op) := by
  simp only [Std.ExtHashSet.fromOperands]
  grind [Std.Rco.mem_toList_iff_mem, Std.Rco.mem_iff]

@[grind =]
theorem Std.ExtHashSet.fromOperands.mem_iff
    (inBounds : operand.InBounds ctx) :
    (operand ∈ (Std.ExtHashSet.fromOperands ctx op) ↔ operand.op = op) := by
  simp only [Std.ExtHashSet.fromOperands]
  simp only [Std.ExtHashSet.mem_ofList, List.contains_eq_mem, List.mem_map,
    Std.Rco.mem_toList_iff_mem, Std.Rco.mem_iff, Nat.zero_le, true_and, decide_eq_true_eq]
  constructor
  · grind
  · intro h
    exists operand.index
    constructor
    · grind [OperationPtr.getNumOperands!, OpOperandPtr.InBounds]
    · cases operand
      grind [OperationPtr.getOpOperand]

theorem IRContext.fieldsInBounds_OperationPtr_dealloc {ctx : IRContext} {inBounds : op.InBounds ctx}
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op) (Std.ExtHashSet.fromSuccessors ctx op))
    (huses : ¬ op.hasUses ctx)
    (hparent : (op.get! ctx).parent = none)
    (hregions : op.getNumRegions! ctx = 0) :
    IRContext.FieldsInBounds (OperationPtr.dealloc op ctx inBounds) := by
  have inMissingUses : ∀ operand, operand.InBounds ctx → operand.op = op → operand ∈ (Std.ExtHashSet.fromOperands ctx op) := by
    intro operand operandIn hoperandOp
    simp only [Std.ExtHashSet.fromOperands, Std.ExtHashSet.mem_ofList, List.contains_eq_mem,
      List.mem_map, decide_eq_true_eq]
    exists operand.index
    subst op
    constructor
    · grind [Std.Rco.mem_toList_iff_mem, OpOperandPtr.InBounds, OperationPtr.getNumOperands, OperationPtr.getOpOperand]
    · simp [OperationPtr.getOpOperand]
  have inMissingSuccessorUses : ∀ blockOperand, blockOperand.InBounds ctx → blockOperand.op = op
        → blockOperand ∈ (Std.ExtHashSet.fromSuccessors ctx op) := by
    intro blockOperand blockOperandIn hblockOperandOp
    simp only [Std.ExtHashSet.fromSuccessors, Std.ExtHashSet.mem_ofList, List.contains_eq_mem,
      List.mem_map, decide_eq_true_eq]
    exists blockOperand.index
    subst op
    constructor
    · grind [Std.Rco.mem_toList_iff_mem, BlockOperandPtr.InBounds, OperationPtr.getNumSuccessors, OperationPtr.getBlockOperand]
    · simp [OperationPtr.getBlockOperand]
  constructor
  · intro op' op'In
    constructor
    · intro res resInBounds resOp
      constructor
      · simp only [← OpResultPtr.get!_eq_get]
        simp (disch := grind) only [OpResultPtr.get!_OperationPtr_dealloc]
        simp only [Option.maybe_def]
        intro firstUse
        intro hFirstUse
        simp only [← GenericPtr.iff_opOperand]
        apply OpOperandPtr.dealloc.inBounds_dealloc_genericPtr
        · grind
        · simp only
          have := wf.valueDefUseChains res (by grind)
          grind [ValuePtr.DefUse, Std.ExtHashSet.fromOperands]
      · simp only [← OpResultPtr.get!_eq_get]
        simp (disch := grind) only [OpResultPtr.get!_OperationPtr_dealloc]
        simp only [← GenericPtr.iff_operation]
        apply OpOperandPtr.dealloc.inBounds_dealloc_genericPtr; grind
        simp only
        have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := wf.operations op' (by grind)
        have := OpResultPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc resInBounds
        have := OperationPtr.eq_getResult_of_OpResultPtr_op_eq resOp
        grind
    · grind [Option.maybe_def, IRContext.WellFormed.OperationPtr_parent!_ne_none_of_next!_ne_none,
        IRContext.WellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some]
    · grind [Option.maybe_def, IRContext.WellFormed.OperationPtr_parent!_ne_none_of_prev!_ne_none,
        IRContext.WellFormed.OperationPtr_prev!_eq_some_of_next!_eq_some]
    · grind [Option.maybe_def]
    · intro operand operandIn hop
      have hoperandOp := BlockOperandPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc operandIn
      have operandIn' := operandIn
      simp only [← GenericPtr.iff_blockOperand] at operandIn'
      have operandIn' := OpResultPtr.dealloc.inBounds_genericPtr_of_inBounds_dealloc operandIn'
      simp only [GenericPtr.iff_blockOperand] at operandIn'
      have opNe : op ≠ op' := by grind
      constructor
      · simp only [Option.maybe_def]
        have ⟨array, harray⟩ := wf.blockDefUseChains (operand.get! ctx).value (by grind)
        grind [BlockPtr.DefUse, Array.getElem_of_mem]
      · simp only [← BlockOperandPtr.get!_eq_get]
        simp (disch := grind) only [BlockOperandPtr.get!_OperationPtr_dealloc]
        simp only [← GenericPtr.iff_blockOperandPtr]
        apply OpOperandPtr.dealloc.inBounds_dealloc_genericPtr; grind
        cases hback : (operand.get! ctx).back; rotate_right 1; simp only
        have ⟨array, harray⟩ := wf.blockDefUseChains (operand.get! ctx).value (by grind)
        grind [BlockPtr.DefUse, Array.getElem_of_mem]
      · simp only [← BlockOperandPtr.get!_eq_get]
        simp (disch := grind) only [BlockOperandPtr.get!_OperationPtr_dealloc]
        simp only [← GenericPtr.iff_operation]
        apply OpOperandPtr.dealloc.inBounds_dealloc_genericPtr; grind
        simp only
        intro howner
        apply hoperandOp
        have := (wf.operations operand.op (by grind)).blockOperand_owner operand.index (by grind [BlockOperandPtr.inBounds_def])
        simp only [OperationPtr.getBlockOperand] at this
        cases operand
        grind
      · grind [Option.maybe_def]
    · grind
    · intro operand operandIn hop
      have hoperandOp := OpOperandPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc operandIn
      have operandIn' := operandIn
      simp only [← GenericPtr.iff_opOperand] at operandIn'
      have operandIn' := OpResultPtr.dealloc.inBounds_genericPtr_of_inBounds_dealloc operandIn'
      simp only [GenericPtr.iff_opOperand] at operandIn'
      have opNe : op ≠ op' := by grind
      have ⟨array, harray⟩ := wf.valueDefUseChains (operand.get! ctx).value (by grind)
      constructor
      · simp only [Option.maybe_def]
        grind [ValuePtr.DefUse, Array.getElem_of_mem]
      · simp only [← OpOperandPtr.get!_eq_get]
        simp (disch := grind) only [OpOperandPtr.get!_OperationPtr_dealloc]
        simp only [← GenericPtr.iff_opOperandPtr]
        apply OpOperandPtr.dealloc.inBounds_dealloc_genericPtr; grind
        cases hback : (operand.get! ctx).back
        case operandNextUse nextUse =>
          simp only
          grind [ValuePtr.DefUse, Array.getElem_of_mem]
        case valueFirstUse firstUse =>
          cases firstUse
          case blockArgument blockArg => simp
          case opResult opRes =>
            simp only
            have : operand ∈ array := by grind [ValuePtr.DefUse]
            intro hopResOp
            simp only [← OperationPtr.hasUses!_eq_hasUses, Bool.not_eq_true] at huses
            simp only [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false] at huses
            have hopResUses := huses opRes.index (by grind)
            have : op.getResult opRes.index = opRes := by cases opRes; grind [OperationPtr.getResult]
            simp only [this] at hopResUses
            simp only [ValuePtr.hasUses!_def,
              Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hopResUses
            grind [ValuePtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse]
      · simp only [← OpOperandPtr.get!_eq_get]
        simp (disch := grind) only [OpOperandPtr.get!_OperationPtr_dealloc]
        simp only [← GenericPtr.iff_operation]
        apply OpOperandPtr.dealloc.inBounds_dealloc_genericPtr; grind
        simp only
        intro howner
        apply hoperandOp
        have := (wf.operations operand.op (by grind)).operand_owner operand.index (by grind [OpOperandPtr.inBounds_def])
        simp only [OperationPtr.getOpOperand] at this
        cases operand
        grind
      · simp only [← OpOperandPtr.get!_eq_get]
        simp (disch := grind) only [OpOperandPtr.get!_OperationPtr_dealloc]
        simp only [← GenericPtr.iff_value]
        apply OpOperandPtr.dealloc.inBounds_dealloc_genericPtr; grind
        cases hvalue : (operand.get! ctx).value; rotate_left 1; grind
        rename_i opRes
        simp only
        intro howner
        have : operand ∈ array := by grind [ValuePtr.DefUse]
        simp only [← OperationPtr.hasUses!_eq_hasUses, Bool.not_eq_true] at huses
        simp only [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false] at huses
        have hopResUses := huses opRes.index (by grind)
        have : op.getResult opRes.index = opRes := by cases opRes; grind [OperationPtr.getResult]
        grind [ValuePtr.DefUse.getFirstUse!_eq_of_back_eq_valueFirstUse, ValuePtr.DefUse.hasUses_iff]
  · intro block blockIn
    constructor
    · have ⟨array, harray⟩ := wf.blockDefUseChains block (by grind)
      grind [BlockPtr.DefUse, Array.getElem_of_mem]
    · grind [Option.maybe_def]
    · grind [Option.maybe_def]
    · grind [Option.maybe_def]
    · grind [Option.maybe_def, IRContext.WellFormed, Operation.WellFormed]
    · grind [Option.maybe_def, IRContext.WellFormed, Operation.WellFormed]
    · intro arg harg hblock
      have ⟨array, harray⟩ := wf.valueDefUseChains arg (by grind)
      constructor <;> grind [ValuePtr.DefUse]
  · intro region regionIn
    constructor
    · grind
    · grind
    · grind [IRContext.WellFormed, Operation.WellFormed]

theorem Operation.wellFormed_OperationPtr_dealloc
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op) (Std.ExtHashSet.fromSuccessors ctx op))
    (inBounds' : OperationPtr.InBounds opPtr' ctx)
    (huses : ¬ op.hasUses ctx)
    (hparent : (op.get! ctx).parent = none)
    (hregions : op.getNumRegions! ctx = 0)
    (inBoundsAfter' : opPtr'.InBounds (OperationPtr.dealloc op ctx inBounds)) :
    Operation.WellFormed op' (OperationPtr.dealloc op ctx inBounds) opPtr' inBoundsAfter' := by
  have := wf.operations opPtr' inBounds'
  constructor
  · grind [IRContext.fieldsInBounds_OperationPtr_dealloc]
  · grind [IRContext.WellFormed, Operation.WellFormed]
  · grind [IRContext.WellFormed, Operation.WellFormed]
  · grind [IRContext.WellFormed, Operation.WellFormed]
  · grind [IRContext.WellFormed, Operation.WellFormed]
  · grind [IRContext.WellFormed, Operation.WellFormed]
  · simp (disch := grind) only [OperationPtr.getRegion!_OperationPtr_dealloc]
    grind [IRContext.WellFormed, Operation.WellFormed]
  · grind [IRContext.WellFormed, Operation.WellFormed]

theorem Block.wellFormed_OperationPtr_dealloc
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op) (Std.ExtHashSet.fromSuccessors ctx op))
    (inBounds' : BlockPtr.InBounds blockPtr ctx)
    (huses : ¬ op.hasUses ctx)
    (hparent : (op.get! ctx).parent = none)
    (hregions : op.getNumRegions! ctx = 0)
    (inBoundsAfter : blockPtr.InBounds (OperationPtr.dealloc op ctx inBounds)) :
    Block.WellFormed block (OperationPtr.dealloc op ctx inBounds) blockPtr inBoundsAfter := by
  constructor
  · grind [IRContext.fieldsInBounds_OperationPtr_dealloc]
  · grind [IRContext.WellFormed, Block.WellFormed]
  · grind [IRContext.WellFormed, Block.WellFormed]

theorem Region.wellFormed_OperationPtr_dealloc
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op) (Std.ExtHashSet.fromSuccessors ctx op))
    (inBounds' : RegionPtr.InBounds regionPtr ctx)
    (huses : ¬ op.hasUses ctx)
    (hparent : (op.get! ctx).parent = none)
    (hregions : op.getNumRegions! ctx = 0)
    (inBoundsAfter : regionPtr.InBounds (OperationPtr.dealloc op ctx inBounds)) :
    Region.WellFormed (regionPtr.get! (OperationPtr.dealloc op ctx inBounds)) (OperationPtr.dealloc op ctx inBounds) regionPtr := by
  constructor
  · have := wf.regions regionPtr inBounds'
    have := this.inBounds
    grind [IRContext.fieldsInBounds_OperationPtr_dealloc, IRContext.WellFormed, Region.WellFormed]
  · have := wf.regions regionPtr inBounds'
    have := this.inBounds
    grind [IRContext.fieldsInBounds_OperationPtr_dealloc, IRContext.WellFormed, Region.WellFormed]

theorem ValuePtr.defUse_OperationPtr_dealloc
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op) (Std.ExtHashSet.fromSuccessors ctx op))
    (defUse : ValuePtr.DefUse valuePtr ctx array
      ((Std.ExtHashSet.fromOperands ctx op).filter (fun use => (use.get! ctx).value = valuePtr)))
    (inBoundsAfter : valuePtr.InBounds (OperationPtr.dealloc op ctx inBounds)) :
    ValuePtr.DefUse valuePtr (OperationPtr.dealloc op ctx inBounds) array := by
  constructor
  · grind
  · intro use useIn
    have : (use.get! ctx).value = valuePtr := by grind [ValuePtr.DefUse]
    have := defUse.allUsesInChain use (by grind) (by grind)
    grind [ValuePtr.DefUse, Array.getElem_of_mem]
  · grind [ValuePtr.DefUse, Array.getElem_of_mem]
  · grind [ValuePtr.DefUse, Array.getElem_of_mem]
  · intro use useIn useValue
    simp only [Std.ExtHashSet.not_mem_empty, not_false_eq_true, iff_true]
    have : (use.get! ctx).value = valuePtr := by grind [ValuePtr.DefUse]
    have := defUse.allUsesInChain use (by grind) (by grind)
    grind [OpOperandPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc]
  · grind [ValuePtr.DefUse, Array.getElem_of_mem]
  · grind [ValuePtr.DefUse, Array.getElem_of_mem]
  · grind [ValuePtr.DefUse, Array.getElem_of_mem]
  · grind
  · grind

theorem BlockPtr.defUse_OperationPtr_dealloc
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op) (Std.ExtHashSet.fromSuccessors ctx op))
    (defUse : BlockPtr.DefUse blockPtr ctx array
      ((Std.ExtHashSet.fromSuccessors ctx op).filter (fun use => (use.get! ctx).value = blockPtr)))
    (inBoundsAfter : blockPtr.InBounds (OperationPtr.dealloc op ctx inBounds)) :
    BlockPtr.DefUse blockPtr (OperationPtr.dealloc op ctx inBounds) array := by
  constructor
  · grind
  · intro use useIn
    have : (use.get! ctx).value = blockPtr := by grind [BlockPtr.DefUse]
    have := defUse.allUsesInChain use (by grind) (by grind)
    grind [BlockPtr.DefUse, Array.getElem_of_mem]
  · grind [BlockPtr.DefUse, Array.getElem_of_mem]
  · grind [BlockPtr.DefUse, Array.getElem_of_mem]
  · grind [BlockPtr.DefUse, Array.getElem_of_mem]
  · grind [BlockPtr.DefUse, Array.getElem_of_mem]
  · grind [BlockPtr.DefUse, Array.getElem_of_mem]
  · intro use useIn useValue
    simp only [Std.ExtHashSet.not_mem_empty, not_false_eq_true, iff_true]
    have : (use.get! ctx).value = blockPtr := by grind [BlockPtr.DefUse]
    have := defUse.allUsesInChain use (by grind) (by grind)
    grind [BlockOperandPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc]
  · grind
  · grind

theorem BlockPtr.opChain_OperationPtr_dealloc
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op) (Std.ExtHashSet.fromSuccessors ctx op))
    (opChain : BlockPtr.OpChain blockPtr ctx array)
    (hparent : (op.get! ctx).parent = none)
    (inBoundsAfter : blockPtr.InBounds (OperationPtr.dealloc op ctx inBounds)) :
    BlockPtr.OpChain blockPtr (OperationPtr.dealloc op ctx inBounds) array := by
  constructor <;> grind [BlockPtr.OpChain]

theorem RegionPtr.blockChain_OperationPtr_dealloc
    (opChain : RegionPtr.BlockChain regionPtr ctx array)
    (inBoundsAfter : regionPtr.InBounds (OperationPtr.dealloc op ctx inBounds)) :
    RegionPtr.BlockChain regionPtr (OperationPtr.dealloc op ctx inBounds) array := by
  constructor <;> grind [RegionPtr.BlockChain]

theorem IRContext.wellFormed_OperationPtr_dealloc {ctx : IRContext} {inBounds : op.InBounds ctx}
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op) (Std.ExtHashSet.fromSuccessors ctx op))
    (huses : ¬ op.hasUses ctx)
    (hparent : (op.get! ctx).parent = none)
    (hregions : op.getNumRegions! ctx = 0) :
    IRContext.WellFormed (OperationPtr.dealloc op ctx inBounds) := by
  constructor
  · grind [IRContext.fieldsInBounds_OperationPtr_dealloc]
  · intro value valueInBounds
    have ⟨array, harray⟩ := wf.valueDefUseChains value (by grind)
    exists array
    simp only [Std.ExtHashSet.filter_empty]
    apply ValuePtr.defUse_OperationPtr_dealloc <;> grind
  · intro block blockInBounds
    have ⟨array, harray⟩ := wf.blockDefUseChains block (by grind)
    exists array
    simp only [Std.ExtHashSet.filter_empty]
    apply BlockPtr.defUse_OperationPtr_dealloc <;> grind
  · intro block blockInBounds
    have ⟨array, harray⟩ := wf.opChain block (by grind)
    exists array
    apply BlockPtr.opChain_OperationPtr_dealloc <;> grind
  · intro region regionInBounds
    have ⟨array, harray⟩ := wf.blockChain region (by grind)
    exists array
    apply RegionPtr.blockChain_OperationPtr_dealloc <;> grind
  · grind [Operation.wellFormed_OperationPtr_dealloc]
  · grind [Block.wellFormed_OperationPtr_dealloc]
  · grind [Region.wellFormed_OperationPtr_dealloc]

end Veir
