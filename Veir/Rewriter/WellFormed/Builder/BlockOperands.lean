import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSetInBounds
import Veir.Rewriter.LinkedList.GetSet

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable (ctx : IRContext OpInfo)
variable (ctxInBounds : ctx.FieldsInBounds)
variable (opPtr opPtr' : OperationPtr)
variable (opPtrInBounds : opPtr.InBounds ctx := by grind)

include ctxInBounds in
@[simp, local grind →]
theorem Rewriter.pushBlockOperand_DefUse_getElem?
    array (arrayWf : BlockPtr.DefUse blockPtr ctx array) (i : Nat) (hISize : i < array.size) :
    (array[i].get (Rewriter.pushBlockOperand ctx opPtr
        blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) (by grind [BlockPtr.DefUse])) =
      {
        (BlockOperandPtr.get array[i] ctx (by grind [BlockPtr.DefUse])) with
        back := (if i = 0
          then
            .blockOperandNextUse (opPtr.nextBlockOperand ctx)
          else
            (BlockOperandPtr.get array[i] ctx (by grind [BlockPtr.DefUse])).back) }
    := by
  apply BlockOperand.ext <;> grind [BlockPtr.DefUse]

set_option maxHeartbeats 4000000 in -- TODO
theorem Rewriter.pushBlockOperand_DefUse (hOpWf : ctx.WellFormed) (blockPtr'InBounds : blockPtr'.InBounds ctx) :
    ∃ array, BlockPtr.DefUse blockPtr' (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) array := by
  have ⟨array', arrayWf'⟩ := hOpWf.blockDefUseChains blockPtr' blockPtr'InBounds
  have ⟨array, arrayWf⟩ := hOpWf.blockDefUseChains blockPtr blockPtrInBounds
  by_cases blockPtr' = blockPtr
  -- Case where we are adding a new use
  case pos =>
    subst blockPtr'
    exists (#[opPtr.nextBlockOperand ctx] ++ array)
    constructor
    case arrayInBounds =>
      grind [ValuePtr.DefUse]
    case firstElem => grind
    case nextElems =>
      intros i hi
      simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
        Nat.zero_add] at hi
      rw [Array.getElem?_append_right (by grind)]
      simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.add_one_sub_one]
      by_cases hi0 : i = 0 <;> grind [BlockOperandPtr.get!_pushBlockOperand', BlockPtr.DefUse]
    case useValue =>
      intro use hUse
      have ⟨i, hI, hUseI⟩ := Array.mem_iff_getElem.mp hUse
      grind [BlockOperandPtr.get!_pushBlockOperand', BlockPtr.DefUse]
    case backNextUse =>
      simp only [gt_iff_lt, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
        Nat.zero_add]
      intros i hi₁ hi₂
      have iNeZero : i ≠ 0 := by grind
      simp only [Array.getElem_append, List.size_toArray, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.lt_one_iff, iNeZero, ↓reduceDIte, List.getElem_toArray,
        List.getElem_singleton]
      grind [BlockOperandPtr.get!_pushBlockOperand', BlockPtr.DefUse]
    case allUsesInChain =>
      grind [BlockOperandPtr.get!_pushBlockOperand', BlockPtr.DefUse]
    all_goals grind [BlockOperandPtr.get!_pushBlockOperand', BlockPtr.DefUse]
  -- Case where the use def chains are preserved
  case neg =>
    exists array'
    apply BlockPtr.DefUse.unchanged (ctx := ctx) <;>
      grind [BlockOperandPtr.get!_pushBlockOperand']

/--
info: 'Veir.Rewriter.pushBlockOperand_DefUse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.pushBlockOperand_DefUse

theorem Rewriter.pushBlockOperand_WellFormed (hOpWf : ctx.WellFormed) :
    (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds valuePtrInBounds ctxInBounds).WellFormed := by
  constructor
  case valueDefUseChains =>
    intros valuePtr valuePtrInBounds
    have ⟨array, arrayWf⟩ := hOpWf.valueDefUseChains valuePtr (by grind)
    exists array
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind
  case blockDefUseChains =>
    grind [Rewriter.pushBlockOperand_DefUse]
  case inBounds => grind
  case opChain =>
    intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := hOpWf.opChain blockPtr (by grind)
    exists array
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind
  case blockChain =>
    intros reg hreg
    have ⟨array, arrayWf⟩ := hOpWf.blockChain reg (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged (ctx := ctx) <;>
      grind
  case operations =>
    intros opPtr' opPtrInBounds
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hOpWf.operations opPtr' (by grind)
    constructor
    case region_parent =>
      simp only [OperationPtr.getRegion!_pushBlockOperand]
      grind
    all_goals grind [Rewriter.pushBlockOperand, Operation.WellFormed, OperationPtr.getBlockOperand]
  case blocks =>
    intros bl hbl
    have ⟨h₁, h₂, h₃, h₄, h₅⟩ := hOpWf.blocks bl (by grind)
    constructor <;> grind
  case regions =>
    intros reg hreg
    have ⟨h₁, h₂⟩ := hOpWf.regions reg (by grind)
    constructor
    · grind [Rewriter.pushBlockOperand]
    · simp only [OperationPtr.getRegion!_pushBlockOperand]
      grind

/--
info: 'Veir.Rewriter.pushBlockOperand_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.pushBlockOperand_WellFormed

theorem Rewriter.initBlockOperands_WellFormed (hOpWf : ctx.WellFormed) :
    (Rewriter.initBlockOperands ctx opPtr operands n h₁ h₂ h₃ h₄).WellFormed := by
  induction n generalizing ctx
  case zero =>
    grind [initBlockOperands]
  case succ n ih =>
    simp only [initBlockOperands]
    grind [Rewriter.pushBlockOperand_WellFormed]
