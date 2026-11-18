module

public import Veir.Interpreter.CTreePrimitiveRefinement
public import Veir.Interpreter.ResultsConform
public import Veir.Interpreter.Lemmas

import all Veir.Interpreter.CTreeInterpreter
import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Monotonicity of opcodes in CTrees

`OpCode.interpretCTree_monotone` is the obligation of an opcode: running a verified operation of
it on refined operands and refined memory has only behaviors that it has on the original ones, up
to refinement of the results and of the memory, with the results of the target of their types.
A dialect meets it from a simulation of the CTree semantics of the opcode (`of_sim`), where the
types of the results come from `ResultsConform`, or, for an opcode whose CTree semantics is the
lift of its `Interp` semantics, from its monotonicity in `Interp` (`of_lift`).
-/

open CTree

namespace Veir

/-- No dialect with CTree semantics calls a region, so `CTree.interpretOp'` ignores the regions. -/
theorem CTree.interpretOp'_regions {opType : OpCode} (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (regions : Array RegionPtr) :
    CTree.interpretOp' opType properties resultTypes operands blockOperands mem regions =
      CTree.interpretOp' opType properties resultTypes operands blockOperands mem := by
  cases opType <;> rfl

/-- The lift of a refinement in `Interp` is a simulation. -/
theorem CTree.sim_monadLift_of_isRefinedBy {R : α → β → Prop} {source : Interp α}
    {target : Interp β} (h : Interp.isRefinedBy R source target) :
    Sim (fun t s => R s t) (monadLift target : Tree β) (monadLift source : Tree α) := by
  cases source with
  | ub _ => exact sim_ub _ _
  | fail _ => exact sim_fail _ _
  | ok a =>
    cases target with
    | ok b => simpa [monadLift, MonadLift.monadLift, Interp.isRefinedBy] using h
    | ub _ => simp [Interp.isRefinedBy] at h
    | fail _ => simp [Interp.isRefinedBy] at h

/--
An opcode meets its obligation if its CTree semantics on refined operands and refined memory
simulates, with the results of the target of the given types whenever every result it may return
is. `ResultsConform` says the latter of a verified operation.
-/
theorem OpCode.interpretCTree_monotone.of_sim {opType : OpCode} [Veir.ResultsConform opType]
    (h : ∀ (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
      (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr)
      (mem mem' : MemoryState) (regions : Array RegionPtr),
      operands ⊒ operands' → mem ⊒ mem' →
      (∀ vals m a, CTree.MayReturn
        (CTree.interpretOp' opType properties resultTypes operands' blockOperands mem' regions)
        (vals, m, a) → RuntimeValue.ArrayConforms vals resultTypes) →
      Sim (fun t s =>
          OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 resultTypes)
        (CTree.interpretOp' opType properties resultTypes operands' blockOperands mem' regions)
        (CTree.interpretOp' opType properties resultTypes operands blockOperands mem regions)) :
    opType.interpretCTree_monotone := by
  intro ctx op opIn hType hVerified sv tv sm tm hConf hRef hMem
  have hT : ∀ vals m a, CTree.MayReturn (op.interpretCTree opIn tv tm) (vals, m, a) →
      RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) :=
    fun vals m a hr => interpretCTree_results_conform (hType ▸ Veir.ResultsConform.conform)
      hVerified (hConf.of_isRefinedBy hRef) hr
  rw [OperationPtr.getResultTypes!_eq_getResultTypes opIn] at hT ⊢
  simp only [OperationPtr.interpretCTree] at hT ⊢
  subst hType
  exact h _ _ _ _ _ _ _ _ hRef hMem hT

/--
An opcode whose CTree semantics is the lift of its `Interp` semantics, as `hLift` says, simulates
on refined operands and refined memory if it is monotone in `Interp`, with the results of the
target of the given types whenever every result it may return is.
-/
theorem CTree.sim_of_lift {opType : OpCode} [inst : InterpretOp'Monotone opType]
    {properties : propertiesOf opType} {resultTypes : Array TypeAttr}
    {operands operands' : Array RuntimeValue} {blockOperands : Array BlockPtr}
    {mem mem' : MemoryState} {regions : Array RegionPtr}
    (hLift : ∀ operands mem,
      CTree.interpretOp' opType properties resultTypes operands blockOperands mem regions =
        monadLift (Veir.interpretOp' opType properties resultTypes operands blockOperands mem))
    (h : operands ⊒ operands') (hMem : mem ⊒ mem')
    (hT : ∀ vals m a, CTree.MayReturn
      (CTree.interpretOp' opType properties resultTypes operands' blockOperands mem' regions)
      (vals, m, a) → RuntimeValue.ArrayConforms vals resultTypes) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 resultTypes)
      (CTree.interpretOp' opType properties resultTypes operands' blockOperands mem' regions)
      (CTree.interpretOp' opType properties resultTypes operands blockOperands mem regions) := by
  rw [hLift] at hT
  rw [hLift, hLift]
  exact CTree.sim_monadLift_of_isRefinedBy (Interp.isRefinedBy_and
    (inst.monotone properties resultTypes operands operands' blockOperands mem mem' h hMem)
    fun ⟨vals, m, a⟩ hok => hT vals m a ((CTree.MayReturn.monadLift_iff _ _).mpr hok))

/--
An opcode whose CTree semantics is the lift of its `Interp` semantics, as `hLift` says, meets its
obligation if it is monotone in `Interp`.
-/
theorem OpCode.interpretCTree_monotone.of_lift {opType : OpCode} [Veir.ResultsConform opType]
    [InterpretOp'Monotone opType]
    (hLift : ∀ properties resultTypes operands blockOperands mem regions,
      CTree.interpretOp' opType properties resultTypes operands blockOperands mem regions =
        monadLift (Veir.interpretOp' opType properties resultTypes operands blockOperands mem)) :
    opType.interpretCTree_monotone :=
  .of_sim fun properties resultTypes _ _ blockOperands _ _ regions h hMem hT =>
    CTree.sim_of_lift (fun operands mem => hLift properties resultTypes operands blockOperands mem
      regions) h hMem hT

end Veir

end
