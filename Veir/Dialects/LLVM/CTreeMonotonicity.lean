module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.LLVM.Monotonicity

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.LLVM.Interpreter
import Veir.Data.LLVM.Byte.Lemmas

public section

/-!
# Monotonicity of the LLVM opcodes in CTrees

Every LLVM opcode but `llvm.freeze` runs its `Interp` semantics in CTrees, which is monotone in
its operands and its memory. `llvm.freeze` chooses what poison becomes, and so does any
refinement of its operand. The types of the results come from `ResultsConform`.
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

/-- A tree that returns a result may return it. -/
private theorem mayReturn_pure {α : Type} (r : α) : MayReturn (pure r : Tree α) r :=
  (MayReturn.pure_iff _ _).mpr rfl

/-! ## `llvm.freeze` -/

/--
`llvm.freeze` is monotone in CTrees: a refinement of its operand chooses what poison becomes as
it does, and the result is of the types every result it may return has.
-/
private theorem llvm_freeze_sim (properties : propertiesOf (OpCode.llvm .freeze))
    (resultTypes : Array TypeAttr) {operands operands' : Array RuntimeValue}
    (blockOperands : Array BlockPtr) {mem mem' : MemoryState} (regions : Array RegionPtr)
    (h : operands ⊒ operands') (hMem : mem ⊒ mem')
    (hT : ∀ vals m a, MayReturn
      (interpretOp' (.llvm .freeze) properties resultTypes operands' blockOperands mem' regions)
      (vals, m, a) → RuntimeValue.ArrayConforms vals resultTypes) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 resultTypes)
      (interpretOp' (.llvm .freeze) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.llvm .freeze) properties resultTypes operands blockOperands mem regions) := by
  rw [interpretOp'_regions, interpretOp'_regions] at hT ⊢
  simp only [interpretOp', Llvm.interpretOpCTree] at hT ⊢
  rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
  · simp
  rotate_left
  · simp
  obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
  simp only [hs'] at hT ⊢
  cases v with
  | int w x =>
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy hv
    cases x with
    | val a =>
      obtain rfl : x' = .val a := by
        have := RuntimeValue.int_val_isRefinedBy_iff.mp hv; simpa using this
      exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem (hT _ _ _ (mayReturn_pure _))
    | poison =>
      cases x' with
      | val a =>
        simp only
        exact sim_choose_right _ a (sim_result (by simp [RuntimeValue.isRefinedBy]) hMem
          (hT _ _ _ (mayReturn_pure _)))
      | poison =>
        refine sim_choose_left _ fun bits => sim_choose_right _ bits ?_
        exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
          (hT _ _ _ (mayReturn_choose_bind bits (mayReturn_pure _)))
  | byte w b =>
    obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
    refine sim_choose_left _ fun bits => sim_choose_right _ (b'.fillPoison bits) ?_
    rw [Data.LLVM.Byte.fillPoison_of_isRefinedBy hb]
    exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
      (hT _ _ _ (mayReturn_choose_bind bits (mayReturn_pure _)))
  | addr p =>
    cases v' <;> simp only [RuntimeValue.isRefinedBy] at hv
    rename_i p'
    cases p with
    | poison =>
      cases p' with
      | val q =>
        -- The source chooses the address of the target's pointer.
        refine sim_choose_right _ q.address.toBitVec
          (sim_result ?_ hMem (hT _ _ _ (mayReturn_pure _)))
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]
      | poison =>
        refine sim_choose_left _ fun q => sim_choose_right _ q ?_
        exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
          (hT _ _ _ (mayReturn_choose_bind q (mayReturn_pure _)))
    | val q =>
      cases p' <;> simp only [Data.LLVM.Ptr.isRefinedBy] at hv
      exact sim_result
        (by simpa [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy] using hv) hMem
        (hT _ _ _ (mayReturn_pure _))
  | _ => simp

end Veir.CTree

namespace Veir

/--
Every LLVM opcode whose results conform meets its CTree monotonicity obligation, `freeze` by its
own semantics.
-/
theorem OpCode.interpretCTree_monotone_llvm (op : Llvm) [Veir.ResultsConform (.llvm op)] :
    OpCode.interpretCTree_monotone (.llvm op) :=
  .of_sim fun properties resultTypes operands operands' blockOperands mem mem' regions h hMem
      hT => by
    by_cases hFreeze : op = .freeze
    · subst hFreeze
      exact CTree.llvm_freeze_sim properties resultTypes blockOperands regions h hMem hT
    · have := llvm_interpretOp'Monotone hFreeze
      exact CTree.sim_of_lift
        (fun _ _ => CTree.interpretOp'_llvm_of_ne_freeze hFreeze _ _ _ _ _ _) h hMem hT

instance (op : Llvm) [ResultsConform (.llvm op)] : InterpretCTreeMonotone (.llvm op) :=
  ⟨OpCode.interpretCTree_monotone_llvm op⟩

end Veir

end
