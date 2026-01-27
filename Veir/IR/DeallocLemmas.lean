import Veir.IR.WellFormed

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
    (inBounds: operand.InBounds ctx) :
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
    (inBounds: operand.InBounds ctx) :
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
    (hregions : op.getNumRegions! ctx = 0)
    (htoplevelOp : ctx.topLevelOp ≠ op) :
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
  · grind
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
        cases hvalue: (operand.get! ctx).value; rotate_left 1; grind
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

end Veir
