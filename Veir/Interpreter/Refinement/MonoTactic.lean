module

public import Veir.Interpreter.Lemmas

public section

/-!
# A tactic for monotonicity in the operands

Most opcodes match their operands as a list of integers or a pointer, compute a result from
them, and return the memory they are given. `op_mono` proves such an opcode monotone in its
operands: the target operands have the same shape, each is poison in the source or the same
value in both, and unfolding the operations on the values reduces the source to poison or to
the target.
-/

namespace Veir

theorem Interp.isRefinedBy_ok_ok {R : α → β → Prop} {a : α} {b : β} :
    Interp.isRefinedBy R (.ok a) (.ok b) ↔ R a b := Iff.rfl

theorem Interp.liftM_none_eq {α : Type} :
    (liftM (none : Option α) : Interp α) = .fail none := rfl

/--
Closes the goals that `op_mono` leaves: both sides are the same computation, on operands where
the source has poison and the target a value. Unfolding the operations `ls` reduces the source to
poison or to the target.
-/
macro "op_mono_finish" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (repeat' split) <;> (try simp_all [Interp.pure_eq, Interp.isRefinedBy_ok_ok,
    Interp.liftM_none_eq, OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy,
    RuntimeValue.isRefinedBy, _root_.isRefinedBy, Id.run, $ls,*])
  all_goals ((repeat' split) <;> (try simp_all [Interp.isRefinedBy_ok_ok,
    Interp.liftM_none_eq]))))

/--
Proves an opcode monotone that matches its operands as a list of one to three integers or one
pointer. `us` unfolds the interpreter of its dialect, and `ls` the operations on the values.
-/
macro "op_mono" "[" us:Lean.Parser.Tactic.simpLemma,* "]"
    "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [interpretOp', $us,*]
  split
  · rename_i heq
    first
      | (obtain ⟨_, hT, h1⟩ := RuntimeValue.toList_int1_of_isRefinedBy (by assumption) heq
         simp only [hT]
         rcases h1 with rfl | ⟨_, rfl, rfl⟩)
      | (obtain ⟨_, _, hT, h1, h2⟩ := RuntimeValue.toList_int2_of_isRefinedBy (by assumption) heq
         simp only [hT]
         rcases h1 with rfl | ⟨_, rfl, rfl⟩ <;> rcases h2 with rfl | ⟨_, rfl, rfl⟩)
      | (obtain ⟨_, _, _, hT, h1, h2, h3⟩ :=
           RuntimeValue.toList_int3_of_isRefinedBy (by assumption) heq
         simp only [hT]
         rcases h1 with rfl | ⟨_, rfl, rfl⟩ <;> rcases h2 with rfl | ⟨_, rfl, rfl⟩ <;>
           rcases h3 with rfl | ⟨_, rfl, rfl⟩)
      | (obtain ⟨_, hT, h1⟩ := RuntimeValue.toList_addr1_of_isRefinedBy (by assumption) heq
         simp only [hT]
         rcases h1 with rfl | ⟨_, rfl, rfl | rfl⟩)
    all_goals first
      | exact Interp.isRefinedBy_refl_operationResult_sameMemory _
      | op_mono_finish [$ls,*]
  · simp [Interp.isRefinedBy_ok_ok, Interp.liftM_none_eq]))

end Veir

end
