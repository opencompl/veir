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
theorem Rewriter.pushOperand_DefUse_getElem?
    (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx)
    array (arrayWf : valuePtr.DefUse ctx array) (i : Nat) (hISize : i < array.size) :
    (array[i].get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) (by grind [ValuePtr.DefUse])) =
      { (OpOperandPtr.get array[i] ctx (by grind [ValuePtr.DefUse])) with
        back := (if i = 0 then .operandNextUse (opPtr.nextOperand ctx) else (OpOperandPtr.get array[i] ctx (by grind [ValuePtr.DefUse])).back) }
    := by
  grind [ValuePtr.DefUse]

set_option maxHeartbeats 10000000 in -- TODO
theorem Rewriter.pushOperand_DefUse
    (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) (hOpWf : ctx.WellFormed)
    (valuePtr' : ValuePtr) (valuePtr'InBounds : valuePtr'.InBounds ctx) :
    ∃ array, valuePtr'.DefUse (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) array := by
  have ⟨array', arrayWf'⟩ := hOpWf.valueDefUseChains valuePtr' valuePtr'InBounds
  have ⟨array, arrayWf⟩ := hOpWf.valueDefUseChains valuePtr valuePtrInBounds
  by_cases valuePtr' = valuePtr
  -- Case where we are adding a new use
  case pos =>
    subst valuePtr'
    exists (#[opPtr.nextOperand ctx] ++ array)
    constructor
    case arrayInBounds =>
      grind [ValuePtr.DefUse]
    case firstElem => grind
    case nextElems =>
      intros i hi
      simp at hi
      rw [Array.getElem?_append_right (by grind)]
      simp
      by_cases hi0 : i = 0 <;> grind [ValuePtr.DefUse]
    case useValue =>
      intro use hUse
      have ⟨i, hI, hUseI⟩ := Array.mem_iff_getElem.mp hUse
      grind [ValuePtr.DefUse]
    case firstUseBack =>
      grind [IRContext.WellFormed]
    case prevNextUse =>
      simp only [gt_iff_lt, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
        Nat.zero_add]
      intros i hi₁ hi₂
      have iNeZero : i ≠ 0 := by grind
      simp [Array.getElem_append, iNeZero]
      grind [ValuePtr.DefUse, Option.maybe_def]
    case allUsesInChain =>
      grind [ValuePtr.DefUse, IRContext.WellFormed]
    all_goals grind
  -- Case where the use def chains are preserved
  case neg =>
    exists array'
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;>
      grind [ValuePtr.DefUse, OpOperandPtr.get!_pushOperand']

/--
info: 'Veir.Rewriter.pushOperand_DefUse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.pushOperand_DefUse

theorem Rewriter.pushOperand_WellFormed  (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) (hOpWf : ctx.WellFormed) :
    (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds).WellFormed := by
  constructor
  case valueDefUseChains =>
    grind [Rewriter.pushOperand_DefUse]
  case blockDefUseChains =>
    intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := hOpWf.blockDefUseChains blockPtr (by grind)
    exists array
    apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind
  case inBounds => grind
  case opChain =>
    intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := hOpWf.opChain blockPtr (by grind)
    exists array
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;>
      grind
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
      intros region regionInBounds
      simp only [OperationPtr.getRegion!_pushOperand]
      grind
    all_goals grind [Rewriter.pushOperand, Operation.WellFormed, OperationPtr.getOpOperand]
  case blocks =>
    intros bl blInBounds
    have ⟨h₁, h₂, h₃, h₄, h₅⟩ := hOpWf.blocks bl (by grind)
    constructor <;> grind
  case regions =>
    intros reg hreg
    have ⟨h₁, h₂⟩ := hOpWf.regions reg (by grind)
    constructor
    · grind [Rewriter.pushOperand]
    · intro op heq
      simp only [OperationPtr.getRegion!_pushOperand]
      grind

/--
info: 'Veir.Rewriter.pushOperand_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rewriter.pushOperand_WellFormed

theorem Rewriter.initOpOperands_WellFormed (ctx: IRContext OpInfo) (opPtr: OperationPtr) (opPtrInBounds : opPtr.InBounds ctx)
    (operands : Array ValuePtr) (hoperands : ∀ oper, oper ∈ operands → oper.InBounds ctx) (hctx : ctx.FieldsInBounds)
    (n : Nat := operands.size) (hn : 0 ≤ n ∧ n ≤ operands.size := by grind)
    (hOpWf : ctx.WellFormed) :
    (Rewriter.initOpOperands ctx opPtr opPtrInBounds operands hoperands hctx n hn).WellFormed := by
  induction n generalizing ctx
  case zero =>
    grind [initOpOperands]
  case succ n ih =>
    simp only [initOpOperands]
    grind [Rewriter.pushOperand_WellFormed]
