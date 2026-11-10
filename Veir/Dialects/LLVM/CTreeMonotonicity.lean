module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.LLVM.Monotonicity
public import Veir.Interpreter.CTreePrimitiveRefinement

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.LLVM.Interpreter
import Veir.Data.Casting

public section

/-!
# Monotonicity of the LLVM opcodes in CTrees

Every LLVM opcode but `llvm.freeze` runs its `Interp` semantics in CTrees, which is monotone in
its operands and its memory. `llvm.freeze` chooses what poison becomes, and so does any
refinement of its operand.
-/

open CTree

namespace Veir.CTree

/-- An LLVM opcode but `freeze` runs its `Interp` semantics. -/
theorem interpretOp'_llvm_of_ne_freeze {op : Llvm} (h : op ≠ .freeze)
    (properties : propertiesOf (OpCode.llvm op)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr) :
    interpretOp' (.llvm op) properties resultTypes operands blockOperands mem regions =
      monadLift
        (Veir.interpretOp' (.llvm op) properties resultTypes operands blockOperands mem) := by
  cases op <;> simp_all [interpretOp', Veir.interpretOp', Llvm.interpretOpCTree]

/-! ## `llvm.freeze` -/

instance llvm_treeMonotone_freeze : InterpretOpTreeMonotone (.llvm .freeze) where
  monotone properties resultTypes operands operands' blockOperands mem mem' regions h hMem := by
    rw [interpretOp'_regions, interpretOp'_regions]
    simp only [interpretOp', Llvm.interpretOpCTree]
    rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
    · simp
    rotate_left
    · simp
    obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
    simp only [hs']
    cases v with
    | int w x =>
      obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy hv
      cases x with
      | val a =>
        obtain rfl : x' = .val a := by
          have := RuntimeValue.int_val_isRefinedBy_iff.mp hv; simpa using this
        exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
      | poison =>
        cases x' with
        | val a =>
          simp only
          exact sim_choose_right _ a (sim_result (by simp [RuntimeValue.isRefinedBy]) hMem)
        | poison =>
          refine sim_choose_left _ fun bits => sim_choose_right _ bits ?_
          exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
    | byte w b =>
      obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
      refine sim_choose_left _ fun bits => sim_choose_right _ (b'.val ||| (b'.poison &&& bits)) ?_
      rw [LLVM.Byte.resolve_of_isRefinedBy hb]
      exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
    | addr p =>
      cases v' <;> simp only [RuntimeValue.isRefinedBy] at hv
      rename_i p'
      cases p with
      | poison =>
        cases p' with
        | val q =>
          -- The source chooses the address of the target's pointer.
          refine sim_choose_right _ q.address.toBitVec (sim_result ?_ hMem)
          simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]
        | poison =>
          refine sim_choose_left _ fun q => sim_choose_right _ q ?_
          exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
      | val q =>
        cases p' <;> simp only [Data.LLVM.Ptr.isRefinedBy] at hv
        exact sim_result (by simpa [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy] using hv)
          hMem
    | _ => simp

/-- Every LLVM opcode is monotone in CTrees, `freeze` by its CTree semantics. -/
theorem llvm_interpretOpTreeMonotone (op : Llvm) : InterpretOpTreeMonotone (.llvm op) := by
  by_cases h : op = .freeze
  · subst h; infer_instance
  · have := llvm_interpretOp'ContextuallyMonotone h
    exact .of_lift (interpretOp'_llvm_of_ne_freeze h)


/-! ## With the types of the results -/

/-- A refinement in `Interp` together with what holds of every result of the target. -/
private theorem Interp.isRefinedBy_and {R : α → β → Prop} {P : β → Prop} {s : Interp α}
    {t : Interp β} (h : Interp.isRefinedBy R s t) (hP : ∀ b, t = .ok b → P b) :
    Interp.isRefinedBy (fun a b => R a b ∧ P b) s t := by
  cases s <;> cases t <;> simp_all [Interp.isRefinedBy]

/-- A single result conforms as another single result of the same kind does. -/
private theorem arrayConforms_singleton {v v' : RuntimeValue} {types : Array TypeAttr}
    (h : RuntimeValue.ArrayConforms #[v] types) (hk : ∀ ty, v.Conforms ty → v'.Conforms ty) :
    RuntimeValue.ArrayConforms #[v'] types := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨by simpa using hs, fun i hi => ?_⟩
  obtain rfl : i = 0 := by simp at hi; omega
  simpa using hk _ (by simpa using hc 0 (by simp))

/-- A single refined result of the given types, with refined memory, simulates. -/
private theorem sim_result_typed {v v' : RuntimeValue} (h : v ⊒ v') {mem mem' : MemoryState}
    (hMem : mem ⊒ mem') {types : Array TypeAttr} (hT : RuntimeValue.ArrayConforms #[v'] types) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 types)
      (pure (#[v'], mem', none) :
        Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
      (pure (#[v], mem, none) :
        Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :=
  (Sim.pure _ _ _).mpr ⟨OperationResult.isRefinedBy_def.mpr
    ⟨by simp [h], hMem, ControlFlowAction.optionIsRefinedBy_refl _⟩, hT⟩

/--
An LLVM opcode is monotone in CTrees, with the results of the target of the types that its
`Interp` results have.
-/
theorem llvm_sim_typed {op : Llvm} {opType : OpCode} (hType : opType = .llvm op)
    (properties : propertiesOf opType) (resultTypes types : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    {mem mem' : MemoryState} (regions : Array RegionPtr) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem')
    (hTyped : ∀ vals m a, Veir.interpretOp' opType properties resultTypes operands' blockOperands
      mem' = .ok (vals, m, a) → RuntimeValue.ArrayConforms vals types) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 types)
      (interpretOp' opType properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' opType properties resultTypes operands blockOperands mem regions) := by
  subst hType
  by_cases hFreeze : op = .freeze
  · subst hFreeze
    rw [interpretOp'_regions, interpretOp'_regions]
    simp only [interpretOp', Llvm.interpretOpCTree]
    rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
    · simp
    rotate_left
    · simp
    obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
    have hTyped' := fun vals m a hok => hTyped vals m a hok
    simp only [Veir.interpretOp', Llvm.interpretOp', hs'] at hTyped'
    simp only [hs']
    cases v with
    | int w x =>
      obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy hv
      have hT := fun y => arrayConforms_singleton (v' := .int w y) (hTyped' _ _ _ rfl)
        fun ty hc => by obtain ⟨a, _⟩ := ty; cases a <;> exact hc
      cases x with
      | val a =>
        obtain rfl : x' = .val a := by
          have := RuntimeValue.int_val_isRefinedBy_iff.mp hv; simpa using this
        exact sim_result_typed (RuntimeValue.isRefinedBy_refl _) hMem (hT _)
      | poison =>
        cases x' with
        | val a =>
          simp only
          exact sim_choose_right _ a
            (sim_result_typed (by simp [RuntimeValue.isRefinedBy]) hMem (hT _))
        | poison =>
          refine sim_choose_left _ fun bits => sim_choose_right _ bits ?_
          exact sim_result_typed (RuntimeValue.isRefinedBy_refl _) hMem (hT _)
    | byte w b =>
      obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
      have hT := fun y => arrayConforms_singleton (v' := .byte w y) (hTyped' _ _ _ rfl)
        fun ty hc => by obtain ⟨a, _⟩ := ty; cases a <;> exact hc
      refine sim_choose_left _ fun bits => sim_choose_right _ (b'.val ||| (b'.poison &&& bits)) ?_
      rw [LLVM.Byte.resolve_of_isRefinedBy hb]
      exact sim_result_typed (RuntimeValue.isRefinedBy_refl _) hMem (hT _)
    | addr p =>
      cases v' <;> simp only [RuntimeValue.isRefinedBy] at hv
      rename_i p'
      have hk : ∀ (x y : Data.LLVM.Ptr) ty, (RuntimeValue.addr x).Conforms ty →
          (RuntimeValue.addr y).Conforms ty := fun _ _ ty hc => by
        obtain ⟨a, _⟩ := ty; cases a <;> exact hc
      cases p with
      | poison =>
        cases p' with
        | val q =>
          -- The source chooses the address of the target's pointer.
          refine sim_choose_right _ q.address.toBitVec (sim_result_typed ?_ hMem
            (arrayConforms_singleton (hTyped' _ _ _ rfl) (hk _ _)))
          simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]
        | poison =>
          refine sim_choose_left _ fun q => sim_choose_right _ q ?_
          exact sim_result_typed (RuntimeValue.isRefinedBy_refl _) hMem
            (arrayConforms_singleton (hTyped' _ _ _ rfl) (hk _ _))
      | val q =>
        cases p' <;> simp only [Data.LLVM.Ptr.isRefinedBy] at hv
        exact sim_result_typed
          (by simpa [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy] using hv) hMem
          (arrayConforms_singleton (hTyped' _ _ _ rfl) (hk _ _))
    | _ => simp
  · have := llvm_interpretOp'ContextuallyMonotone hFreeze
    rw [interpretOp'_llvm_of_ne_freeze hFreeze, interpretOp'_llvm_of_ne_freeze hFreeze]
    exact sim_monadLift_of_isRefinedBy (Interp.isRefinedBy_and
      (this.monotone properties resultTypes operands operands' blockOperands mem mem' h hMem)
      fun ⟨vals, m, a⟩ hok => hTyped vals m a hok)

end Veir.CTree

namespace Veir

/--
Every LLVM opcode is monotone in CTrees, with the results of the target typed: the obligation of
`OpCode.interpretCTree_monotone` holds for LLVM. The types of the results come from
`interpretOp'_results_conform`.
-/
theorem OpCode.interpretCTree_monotone_llvm (op : Llvm) :
    OpCode.interpretCTree_monotone (.llvm op) := by
  intro ctx o oIn hType hVerified sv tv sm tm hConf hRef hMem
  simp only [OperationPtr.interpretCTree]
  refine CTree.llvm_sim_typed hType _ _ _ _ _ hRef hMem fun vals m a hok =>
    interpretOp'_results_conform (mem := tm) (mem' := m) (act := a) hVerified
      (hConf.of_isRefinedBy hRef) ?_
  simp only [OperationPtr.interpret]
  rw [OperationPtr.getOpType!_eq_getOpType oIn, OperationPtr.getProperties!_eq_getProperties oIn
    (by grind), OperationPtr.getResultTypes!_eq_getResultTypes oIn,
    OperationPtr.getSuccessors!_eq_getSuccessors oIn]
  exact hok

/--
info: 'Veir.OpCode.interpretCTree_monotone_llvm' depends on axioms: [propext,
 Sim,
 Classical.choice,
 Quot.sound,
 interpretOp'_results_conform,
 Sim.ret,
 Sim.tau_l,
 Sim.tau_r,
 Sim.ub]
-/
#guard_msgs in
#print axioms OpCode.interpretCTree_monotone_llvm

instance (op : Llvm) : InterpretCTreeMonotone (.llvm op) :=
  ⟨OpCode.interpretCTree_monotone_llvm op⟩

end Veir

end
