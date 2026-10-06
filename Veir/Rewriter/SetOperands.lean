module

public import Veir.Rewriter.WfRewriter.Basic

import all Veir.IR.Basic
import all Veir.Rewriter.Basic
import Veir.Rewriter.GetSet
import Veir.Rewriter.WellFormed.Operation
import Veir.Rewriter.WellFormed.OpOperands
import Veir.IR.DeallocLemmas

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo} {op : OperationPtr} {hop : op.InBounds ctx}

section
setup_grind_with_get_set_definitions
attribute [local grind] GenericPtr.InBounds OperationPtr.InBounds RegionPtr.InBounds
  BlockPtr.InBounds OpResultPtr.InBounds BlockArgumentPtr.InBounds OpOperandPtr.InBounds
  BlockOperandPtr.InBounds ValuePtr.InBounds OpOperandPtrPtr.InBounds BlockOperandPtrPtr.InBounds
attribute [local grind cases] GenericPtr OpOperandPtrPtr BlockOperandPtrPtr ValuePtr

private theorem inBounds_clear (ptr : GenericPtr) :
    ptr.InBounds (op.setOperands ctx #[] hop) ↔
      match ptr with
      | .opOperand use | .opOperandPtr (.operandNextUse use) =>
          ptr.InBounds ctx ∧ use.op ≠ op
      | _ => ptr.InBounds ctx := by
  cases ptr <;> grind
end

attribute [local grind =] inBounds_clear

private theorem defUse_clear
    (h : ValuePtr.DefUse value ctx array
      ((Std.ExtHashSet.fromOperands ctx op).filter (fun use => (use.get! ctx).value = value))) :
    ValuePtr.DefUse value (op.setOperands ctx #[] hop) array := by
  have hne : ∀ use ∈ array, use.op ≠ op := by
    grind [ValuePtr.DefUse]
  constructor <;> grind [ValuePtr.DefUse, Array.getElem_of_mem]

private theorem fieldsInBounds_clear
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op)) :
    (op.setOperands ctx #[] hop).FieldsInBounds := by
  have uses : ∀ value, value.InBounds ctx →
      ∃ array, ValuePtr.DefUse value (op.setOperands ctx #[] hop) array := by
    intro value hv
    obtain ⟨array, harray⟩ := wf.valueDefUseChains value hv
    exact ⟨array, defUse_clear harray⟩
  constructor
  · intro other hother
    have old := wf.inBounds.operations_inBounds other (by grind)
    constructor
    case results_inBounds =>
      intro result hr _
      obtain ⟨array, harray⟩ := uses result (by grind)
      constructor <;> grind [Option.maybe_def, ValuePtr.DefUse]
    case operands_inBounds =>
      intro use hu _
      have hu' : use.InBounds ctx := by grind
      obtain ⟨array, harray⟩ := uses (use.get! ctx).value (by grind)
      have hm : use ∈ array := by grind [ValuePtr.DefUse]
      obtain ⟨i, hi, heq⟩ := Array.getElem_of_mem hm
      constructor <;> grind [Option.maybe_def, ValuePtr.DefUse]
    case blockOperands_inBounds => intros; constructor <;> grind [Option.maybe_def]
    all_goals grind [Option.maybe_def]
  · intro block hb
    have old := wf.inBounds.blocks_inBounds block (by grind)
    constructor
    case arguments_inBounds =>
      intro arg ha _
      obtain ⟨array, harray⟩ := uses arg (by grind)
      constructor <;> grind [Option.maybe_def, ValuePtr.DefUse]
    all_goals grind [Option.maybe_def]
  · intros; constructor <;> grind [Option.maybe_def]

private theorem wellFormed_clear
    (wf : ctx.WellFormed (Std.ExtHashSet.fromOperands ctx op)) :
    (op.setOperands ctx #[] hop).WellFormed := by
  have fib := fieldsInBounds_clear wf (hop := hop)
  constructor
  case inBounds => exact fib
  case valueDefUseChains =>
    intro value hv
    obtain ⟨array, harray⟩ := wf.valueDefUseChains value (by grind)
    simpa only [Std.ExtHashSet.filter_empty] using ⟨array, defUse_clear harray (hop := hop)⟩
  case blockDefUseChains =>
    intro block hb
    obtain ⟨array, harray⟩ := wf.blockDefUseChains block (by grind)
    refine ⟨array, ?_⟩
    simp only [Std.ExtHashSet.filter_empty] at harray ⊢
    apply BlockPtr.DefUse.unchanged harray <;> grind
  case opChain =>
    intro block hb
    obtain ⟨array, harray⟩ := wf.opChain block (by grind)
    refine ⟨array, ?_⟩
    apply BlockPtr.OpChain_unchanged harray <;> grind
  case blockChain =>
    intro region hr
    obtain ⟨array, harray⟩ := wf.blockChain region (by grind)
    refine ⟨array, ?_⟩
    apply RegionPtr.blockChain_unchanged harray <;> grind
  case operations =>
    intro other ho
    have old := wf.operations other (by grind)
    constructor
    case region_parent =>
      intro region hr
      simpa only [OperationPtr.getNumRegions!_OperationPtr_setOperands,
        OperationPtr.getRegion!_OperationPtr_setOperands, RegionPtr.get!_OperationPtr_setOperands]
        using old.region_parent region (by grind)
    all_goals grind [OperationPtr.WellFormed]
  case blocks =>
    intro block hb
    apply BlockPtr.WellFormed_unchanged (wf.blocks block (by grind)) <;> grind
  case regions =>
    intro region hr
    apply RegionPtr.WellFormed_unchanged (wf.regions region (by grind)) <;> grind

/-- Replace an operation's operands, detaching old uses before reusing their indices. -/
def WfRewriter.setOperands (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    (values : Array ValuePtr)
    (hop : op.InBounds wfCtx.raw := by grind)
    (hvalues : ∀ value ∈ values, value.InBounds wfCtx.raw := by grind) :
    WfIRContext OpInfo :=
  let detached := Rewriter.detachOperands wfCtx.raw op (by grind) hop
  have detachedWf : detached.WellFormed (Std.ExtHashSet.fromOperands detached op) := by
    have h := Rewriter.detachOperands_wellFormed wfCtx.wellFormed
      (op := op) (hOp := hop) (hCtx := by grind) (by grind)
    simpa [detached, Std.ExtHashSet.fromOperands, Std.ExtHashSet.insertMany_empty_eq_ofList,
      OperationPtr.getOpOperand_def] using h
  let cleared := op.setOperands detached #[] (by grind)
  have clearedWf : cleared.WellFormed := wellFormed_clear detachedWf
  ⟨Rewriter.initOpOperands cleared op (by grind) values (by grind) (by grind),
    by apply Rewriter.initOpOperands_WellFormed; exact clearedWf⟩

/--
Replace a slice of an operation's operands, allowing the replacement to grow or
shrink the slice. This maintains use-def chains but does not update dialect
properties such as operand segment sizes.
-/
def WfRewriter.setOperandRange (ctx : WfIRContext OpInfo) (op : OperationPtr)
    (start length : Nat) (values : Array ValuePtr) : Except String (WfIRContext OpInfo) := do
  if hop : op.InBounds ctx.raw then
    let old := op.getOperands! ctx.raw
    unless start + length ≤ old.size do
      throw "operand range is out of bounds"
    let operands := old.extract 0 start ++ values ++ old.extract (start + length) old.size
    if hvalues : ∀ value ∈ values, value.InBounds ctx.raw then
      return WfRewriter.setOperands ctx op operands hop (by
        grind [Array.mem_extract_iff])
    else
      throw "replacement operand is out of bounds"
  else
    throw "operation is out of bounds"

end Veir
