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

theorem CTree.tree_bind_eq (t : Tree α) (k : α → Tree β) : t >>= k = CTree.bind t k := by
  simp only [Bind.bind]

/-! ## Choices on either side of a simulation -/

theorem CTree.choose_freeze (i : FreezeCIn) :
    (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i : Tree (FreezeC i)) =
      CTree.tauG (.inr i) (fun x => pure x) := by
  rw [CTree.choose_def, CTree.tau_def]
  rfl

/-- The target chooses: every choice must be simulated. -/
theorem CTree.sim_choose_left {RR : α → β → Prop} (i : FreezeCIn) {k : FreezeC i → Tree α}
    {s : Tree β} (h : ∀ x, Sim RR (k x) s) :
    Sim RR (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i >>= k) s := by
  rw [CTree.choose_freeze, bind_tau]
  exact (Sim.tau_l _ _ _ _).mpr fun x => by simpa using h x

/-- The source chooses: one choice suffices. -/
theorem CTree.sim_choose_right {RR : α → β → Prop} (i : FreezeCIn) {k : FreezeC i → Tree β}
    {t : Tree α} (x : FreezeC i) (h : Sim RR t (k x)) :
    Sim RR t (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i >>= k) := by
  rw [CTree.choose_freeze, bind_tau]
  exact Sim.tau_r _ _ _ _ x (by simpa using h)

/-- A tree that chooses `x` and goes on may return what it then returns. -/
theorem CTree.mayReturn_choose_bind {i : FreezeCIn} {k : FreezeC i → Tree α} (x : FreezeC i)
    {r : α} (h : CTree.MayReturn (k x) r) :
    CTree.MayReturn (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i >>= k) r := by
  rw [CTree.tree_bind_eq]
  exact (CTree.MayReturn.bind_iff _ _ _).mpr ⟨x, (CTree.MayReturn.choose_iff _ _).mpr trivial, h⟩

/-! ## Operands and results -/

/-- The operands that refine a single operand are a single operand. -/
theorem CTree.toList_eq_singleton_of_isRefinedBy {operands operands' : Array RuntimeValue}
    (h : operands ⊒ operands') {v : RuntimeValue} (hv : operands.toList = [v]) :
    ∃ v', operands'.toList = [v'] ∧ v ⊒ v' := by
  obtain rfl : operands = #[v] := by
    rcases operands with ⟨l⟩; simp only [List.toArray] at hv ⊢; simp [hv]
  obtain ⟨v', rfl, hv'⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
  exact ⟨v', rfl, hv'⟩

/-- A single refined result of the given types, with refined memory, simulates. -/
theorem CTree.sim_result {v v' : RuntimeValue} (h : v ⊒ v') {mem mem' : MemoryState}
    (hMem : mem ⊒ mem') {types : Array TypeAttr} (hT : RuntimeValue.ArrayConforms #[v'] types) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 types)
      (pure (#[v'], mem', none) :
        Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
      (pure (#[v], mem, none) :
        Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :=
  (Sim.pure _ _ _).mpr ⟨OperationResult.isRefinedBy_def.mpr
    ⟨by simp [h], hMem, ControlFlowAction.optionIsRefinedBy_refl _⟩, hT⟩

/-! ## Monotonicity -/

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
