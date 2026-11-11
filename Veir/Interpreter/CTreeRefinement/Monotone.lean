module

public import Veir.Interpreter.CTreeInterpreter
public import Veir.Interpreter.Lemmas

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTree

public section

/-!
# Monotonicity of opcodes in CTrees

An opcode is monotone in CTrees when running it on refined operands and refined memory has only
behaviors that it has on the original ones, up to refinement of the results and of the memory.
An opcode whose CTree semantics is the lift of its `Interp` semantics is monotone in CTrees if
it is monotone in `Interp`.
-/

open CTree

namespace Veir.CTree

theorem tree_bind_eq (t : Tree α) (k : α → Tree β) : t >>= k = CTree.bind t k := by
  simp only [Bind.bind]

@[simp]
theorem fail_bind (k : α → Tree β) : (fail : Tree α) >>= k = fail := by
  rw [tree_bind_eq, bind_fail]

/-- A simulation with a stronger relation. -/
theorem sim_mono {RR RR' : α → β → Prop} {t : Tree α} {s : Tree β} (h : Sim RR t s)
    (hRR : ∀ a b, RR a b → RR' a b) : Sim RR' t s := by
  have := Sim.bind (RR' := RR') t s pure pure h (fun a b hab => (Sim.pure _ _ _).mpr (hRR a b hab))
  rwa [← tree_bind_eq, ← tree_bind_eq, _root_.bind_pure, _root_.bind_pure] at this

/-- Checked results preserve opcode simulation and establish target conformance. -/
theorem sim_checkResultTypes {source target : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)}
    (h : Sim (fun t s => OperationResult.isRefinedBy s t) target source) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 types)
      (checkResultTypes types target) (checkResultTypes types source) := by
  unfold checkResultTypes
  apply Sim.bind _ _ _ _ h
  intro t s related
  by_cases hc : RuntimeValue.ArrayConforms s.1 types
  · have ht := hc.of_isRefinedBy related.1
    simp only [hc, ht, ↓reduceIte, Sim.pure]
    exact ⟨related, trivial⟩
  · simp only [hc, ↓reduceIte]
    exact Veir.sim_ub _ _

/-- Checking a lifted deterministic result agrees with lifting its checked result. -/
theorem checkResultTypes_lift (types : Array TypeAttr)
    (outcome : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
    checkResultTypes types (monadLift outcome) = monadLift (Veir.checkResultTypes types outcome) := by
  cases outcome with
  | fail => simp [checkResultTypes, Veir.checkResultTypes, monadLift, MonadLift.monadLift, Bind.bind]
  | ub => simp [checkResultTypes, Veir.checkResultTypes, monadLift, MonadLift.monadLift, Bind.bind]
  | ok result =>
    simp only [checkResultTypes, Veir.checkResultTypes, Interp.bind_ok, CTree.monadLift_interp_ok,
      ← CTree.ret_pure, CTree.CTree.bind_ret]
    split <;> rfl


/-- No dialect with CTree semantics calls a region, so `interpretOp'` ignores the regions. -/
theorem interpretOp'_regions {opType : OpCode} (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (regions : Array RegionPtr) :
    interpretOp' opType properties resultTypes operands blockOperands mem regions =
      interpretOp' opType properties resultTypes operands blockOperands mem := by
  cases opType <;> rfl

/-! ## Choices on either side of a simulation -/

theorem choose_freeze (i : FreezeCIn) :
    (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i : Tree (FreezeC i)) =
      CTree.tauG (.inr i) (fun x => pure x) := by
  rw [CTree.choose_def, CTree.tau_def]
  rfl

/-- The target chooses: every choice must be simulated. -/
theorem sim_choose_left {RR : α → β → Prop} (i : FreezeCIn) {k : FreezeC i → Tree α}
    {s : Tree β} (h : ∀ x, Sim RR (k x) s) :
    Sim RR (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i >>= k) s := by
  rw [choose_freeze, bind_tau]
  exact (Sim.tau_l _ _ _ _).mpr fun x => by simpa using h x

/-- The source chooses: one choice suffices. -/
theorem sim_choose_right {RR : α → β → Prop} (i : FreezeCIn) {k : FreezeC i → Tree β}
    {t : Tree α} (x : FreezeC i) (h : Sim RR t (k x)) :
    Sim RR t (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i >>= k) := by
  rw [choose_freeze, bind_tau]
  exact Sim.tau_r _ _ _ _ x (by simpa using h)

/-! ## Operands and results -/

/-- The operands that refine a single operand are a single operand. -/
theorem toList_eq_singleton_of_isRefinedBy {operands operands' : Array RuntimeValue}
    (h : operands ⊒ operands') {v : RuntimeValue} (hv : operands.toList = [v]) :
    ∃ v', operands'.toList = [v'] ∧ v ⊒ v' := by
  obtain rfl : operands = #[v] := by
    rcases operands with ⟨l⟩; simp only [List.toArray] at hv ⊢; simp [hv]
  obtain ⟨v', rfl, hv'⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
  exact ⟨v', rfl, hv'⟩

/-- A single refined result, with refined memory and no control flow, simulates. -/
theorem sim_result {v v' : RuntimeValue} (h : v ⊒ v') {mem mem' : MemoryState}
    (hMem : mem ⊒ mem') :
    Sim (fun t s => OperationResult.isRefinedBy s t)
      (pure (#[v'], mem', none) :
        Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
      (pure (#[v], mem, none) :
        Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :=
  (Sim.pure _ _ _).mpr (OperationResult.isRefinedBy_def.mpr
    ⟨by simp [h], hMem, ControlFlowAction.optionIsRefinedBy_refl _⟩)

/-! ## Monotonicity -/

/-- The lift of a refinement in `Interp` is a simulation. -/
theorem sim_monadLift_of_isRefinedBy {R : α → β → Prop} {source : Interp α} {target : Interp β}
    (h : Interp.isRefinedBy R source target) :
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
Monotonicity of the CTree semantics of an opcode in its operands and its memory: running it on
refined operands and refined memory has only behaviors that it has on the original ones, up to
refinement of the results and of the memory.
-/
class InterpretOpTreeMonotone (opType : OpCode) : Prop where
  monotone (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem mem' : MemoryState) (regions : Array RegionPtr) :
    operands ⊒ operands' → mem ⊒ mem' →
    Sim (fun t s => OperationResult.isRefinedBy s t)
      (interpretOp' opType properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' opType properties resultTypes operands blockOperands mem regions)

/--
An opcode whose CTree semantics is the lift of its `Interp` semantics, as `hLift` says, is
monotone in CTrees if it is monotone in `Interp`.
-/
theorem InterpretOpTreeMonotone.of_lift {opType : OpCode}
    [inst : InterpretOp'ContextuallyMonotone opType]
    (hLift : ∀ properties resultTypes operands blockOperands mem regions,
      interpretOp' opType properties resultTypes operands blockOperands mem regions =
        monadLift (Veir.interpretOp' opType properties resultTypes operands blockOperands mem)) :
    InterpretOpTreeMonotone opType where
  monotone properties resultTypes operands operands' blockOperands mem mem' regions h hMem := by
    rw [hLift, hLift]
    exact sim_monadLift_of_isRefinedBy
      (inst.monotone properties resultTypes operands operands' blockOperands mem mem' h hMem)

end Veir.CTree

end
