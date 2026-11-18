module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.LLVM.Monotonicity
public import Veir.Interpreter.CTreePrimitiveRefinement
public import Veir.Dialects.LLVM.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.LLVM.Interpreter
import Veir.Data.LLVM.Byte.Lemmas

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

/--
What holds of the values of the target, `Q`, and is the same for all values of a kind and width:
the types of the values, or nothing.
-/
private def KindAlike (Q : Array RuntimeValue → Prop) : Prop :=
  (∀ w (x y : Data.LLVM.Int w), Q #[.int w x] → Q #[.int w y]) ∧
  (∀ w (b b' : Data.LLVM.Byte w), Q #[.byte w b] → Q #[.byte w b']) ∧
  (∀ (p q : Data.LLVM.Ptr), Q #[.addr p] → Q #[.addr q])

/--
`llvm.freeze` is monotone in CTrees: a refinement of its operand chooses what poison becomes as
it does. What holds of the `Interp` results of the target, `Q`, holds of its CTree results.
-/
private theorem llvm_freeze_sim {Q : Array RuntimeValue → Prop} (hQ : KindAlike Q)
    (properties : propertiesOf (OpCode.llvm .freeze)) (resultTypes : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    {mem mem' : MemoryState} (regions : Array RegionPtr) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem')
    (hTyped : ∀ vals m a, Veir.interpretOp' (.llvm .freeze) properties resultTypes operands'
      blockOperands mem' = .ok (vals, m, a) → Q vals) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ Q t.1)
      (interpretOp' (.llvm .freeze) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.llvm .freeze) properties resultTypes operands blockOperands mem regions) := by
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
    have hT := fun y => hQ.1 w _ y (hTyped' _ _ _ rfl)
    cases x with
    | val a =>
      obtain rfl : x' = .val a := by
        have := RuntimeValue.int_val_isRefinedBy_iff.mp hv; simpa using this
      exact sim_result_of (RuntimeValue.isRefinedBy_refl _) hMem (hT _)
    | poison =>
      cases x' with
      | val a =>
        simp only
        exact sim_choose_right _ a
          (sim_result_of (by simp [RuntimeValue.isRefinedBy]) hMem (hT _))
      | poison =>
        refine sim_choose_left _ fun bits => sim_choose_right _ bits ?_
        exact sim_result_of (RuntimeValue.isRefinedBy_refl _) hMem (hT _)
  | byte w b =>
    obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
    have hT := fun y => hQ.2.1 w _ y (hTyped' _ _ _ rfl)
    refine sim_choose_left _ fun bits => sim_choose_right _ (b'.fillPoison bits) ?_
    rw [Data.LLVM.Byte.fillPoison_of_isRefinedBy hb]
    exact sim_result_of (RuntimeValue.isRefinedBy_refl _) hMem (hT _)
  | addr p =>
    cases v' <;> simp only [RuntimeValue.isRefinedBy] at hv
    rename_i p'
    cases p with
    | poison =>
      cases p' with
      | val q =>
        -- The source chooses the address of the target's pointer.
        refine sim_choose_right _ q.address.toBitVec
          (sim_result_of ?_ hMem (hQ.2.2 _ _ (hTyped' _ _ _ rfl)))
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]
      | poison =>
        refine sim_choose_left _ fun q => sim_choose_right _ q ?_
        exact sim_result_of (RuntimeValue.isRefinedBy_refl _) hMem
          (hQ.2.2 _ _ (hTyped' _ _ _ rfl))
    | val q =>
      cases p' <;> simp only [Data.LLVM.Ptr.isRefinedBy] at hv
      exact sim_result_of
        (by simpa [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy] using hv) hMem
        (hQ.2.2 _ _ (hTyped' _ _ _ rfl))
  | _ => simp

/-! ## Every opcode -/

/--
An LLVM opcode is monotone in CTrees, with what holds of the `Interp` results of the target, `Q`,
holding of its CTree results.
-/
private theorem llvm_sim {op : Llvm} {Q : Array RuntimeValue → Prop} (hQ : KindAlike Q)
    (properties : propertiesOf (OpCode.llvm op)) (resultTypes : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    {mem mem' : MemoryState} (regions : Array RegionPtr) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem')
    (hTyped : ∀ vals m a, Veir.interpretOp' (.llvm op) properties resultTypes operands'
      blockOperands mem' = .ok (vals, m, a) → Q vals) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ Q t.1)
      (interpretOp' (.llvm op) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.llvm op) properties resultTypes operands blockOperands mem regions) := by
  by_cases hFreeze : op = .freeze
  · subst hFreeze
    exact llvm_freeze_sim hQ properties resultTypes blockOperands regions h hMem hTyped
  · have := llvm_interpretOp'ContextuallyMonotone hFreeze
    exact sim_of_lift (fun _ _ => interpretOp'_llvm_of_ne_freeze hFreeze _ _ _ _ _ _) h hMem hTyped

/-- Every LLVM opcode is monotone in CTrees. -/
theorem llvm_interpretOpTreeMonotone (op : Llvm) : InterpretOpTreeMonotone (.llvm op) where
  monotone properties resultTypes operands operands' blockOperands mem mem' regions h hMem := by
    simpa using llvm_sim (Q := fun _ => True)
      ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial⟩
      properties resultTypes blockOperands regions h hMem fun _ _ _ _ => trivial

/-! ## With the types of the results -/

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
  refine llvm_sim ⟨fun _ _ _ hc => ?_, fun _ _ _ hc => ?_, fun _ _ hc => ?_⟩ properties
    resultTypes blockOperands regions h hMem hTyped
  all_goals
    exact arrayConforms_singleton hc fun ty hc => by obtain ⟨a, _⟩ := ty; cases a <;> exact hc

end Veir.CTree

namespace Veir

/--
Every LLVM opcode is monotone in CTrees, with the results of the target typed: the obligation of
`OpCode.interpretCTree_monotone` holds for LLVM. The types of the results come from
`Llvm.interpretOp'_results_conform`.
-/
theorem OpCode.interpretCTree_monotone_llvm (op : Llvm) :
    OpCode.interpretCTree_monotone (.llvm op) := by
  intro ctx o oIn hType hVerified sv tv sm tm hConf hRef hMem
  have hType! : o.getOpType! ctx.raw = .llvm op := by
    rw [OperationPtr.getOpType!_eq_getOpType oIn]; exact hType
  simp only [OperationPtr.interpretCTree]
  refine CTree.llvm_sim_typed hType _ _ _ _ _ hRef hMem fun vals m a hok => ?_
  /- Put the hypothesis back in terms of `OperationPtr.interpret`, which is the form
  `Llvm.interpretOp'_results_conform` takes once the opcode is known. -/
  have hok' : o.interpret ctx.raw tv tm = .ok (vals, m, a) := by
    simp only [OperationPtr.interpret]
    rw [OperationPtr.getOpType!_eq_getOpType oIn,
      OperationPtr.getProperties!_eq_getProperties oIn (by grind),
      OperationPtr.getResultTypes!_eq_getResultTypes oIn,
      OperationPtr.getSuccessors!_eq_getSuccessors oIn]
    exact hok
  simp only [OperationPtr.interpret] at hok'
  rw [hType!] at hok'
  exact Llvm.interpretOp'_results_conform op hType! hVerified (hConf.of_isRefinedBy hRef) hok'

instance (op : Llvm) : InterpretCTreeMonotone (.llvm op) :=
  ⟨OpCode.interpretCTree_monotone_llvm op⟩

end Veir

end
