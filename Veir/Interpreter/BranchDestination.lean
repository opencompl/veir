module

public import Veir.Interpreter.Basic

import all Veir.Interpreter.Basic
import all Veir.Interpreter.Interp
import all Veir.Dialects.Arith.OpInfo
import all Veir.Dialects.ModArith.OpInfo
import all Veir.Dialects.LLZK.Felt.OpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.RISCV_Stack.OpInfo
import all Veir.Dialects.RV64.OpInfo
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.Comb.OpInfo
import all Veir.Dialects.HW.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.OpInfo

public section

/-!
# The destination of a branch is a successor

An operation that branches, in any dialect, branches to one of its successors. The branches
read their destination from the successors, `llvm.switch` in a loop over its cases; no other
operation branches.
-/

namespace Veir

/-- Unfolds a dialect interpreter and checks every outcome that branches. -/
local macro "dest_tac" ls:Lean.Parser.Tactic.simpLemma,* : tactic => `(tactic| (
  simp only [interpretOp', $ls,*] at * <;> (repeat' split at *) <;>
    simp_all [Interp.pure_eq, liftM, monadLift, MonadLift.monadLift, Bind.bind, Array.mem_def,
      -Array.mem_toList_iff] <;> grind [List.eq_toArray_iff]))

/-- A property of the state of a `for` loop that every step keeps holds at its end. -/
private theorem list_forIn_preserves {α β : Type} (xs : List α)
    (body : α → β → Interp (ForInStep β)) (P : β → Prop) (initial final : β)
    (hinit : P initial)
    (hstep : ∀ x state, P state → ∀ result, body x state = .ok result → P result.value)
    (h : forIn xs initial body = .ok final) : P final := by
  induction xs generalizing initial with
  | nil => cases h; exact hinit
  | cons x xs ih =>
    simp only [List.forIn_cons] at h
    cases hb : body x initial with
    | fail => simp [hb, Bind.bind] at h
    | ub => simp [hb, Bind.bind] at h
    | ok step =>
      have hp := hstep x initial hinit step hb
      cases step with
      | done final' => simp [hb, Bind.bind] at h; cases h; exact hp
      | yield next =>
        simp only [hb, Bind.bind] at h
        exact ih next hp h

private theorem range_forIn_preserves {β : Type} (r : Std.Legacy.Range)
    (body : Nat → β → Interp (ForInStep β)) (P : β → Prop) (initial final : β)
    (hinit : P initial)
    (hstep : ∀ x state, P state → ∀ result, body x state = .ok result → P result.value)
    (h : forIn r initial body = .ok final) : P final := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_preserves _ body P initial final hinit hstep h

set_option maxHeartbeats 2000000 in
/-- `llvm.switch` branches to its default successor or to the successor of a case. -/
private theorem Llvm.interpretOp'_switch_dest_mem
    {properties : propertiesOf Llvm.switch} {resultTypes : Array TypeAttr}
    {operands : Array RuntimeValue} {blockOperands : Array BlockPtr} {mem mem' : MemoryState}
    {vals res : Array RuntimeValue} {dest : BlockPtr} {layout : DataLayout}
    (h : Llvm.interpretOp' .switch properties resultTypes operands blockOperands mem layout
      = .ok (vals, mem', some (.branch res dest))) : dest ∈ blockOperands := by
  simp only [Llvm.interpretOp'] at h
  repeat first
    | contradiction
    | split at h
    | simp only [Bind.bind, Pure.pure, liftM, monadLift, MonadLift.monadLift] at h
  all_goals try (cases h; done)
  · rename_i loopState hloop _ outcome houtcome
    have hinv : ∀ o, loopState.1 = some o →
        ∃ r d, o.2.2 = some (ControlFlowAction.branch r d) ∧ d ∈ blockOperands := by
      apply range_forIn_preserves _ _ _ _ _ ?_ ?_ hloop
      · simp
      · intro i state _ result hresult
        repeat first
          | cases hresult; simp
          | contradiction
          | split at hresult
        all_goals first
          | (injection hresult with hresult; subst hresult; simp; done)
          | (injection hresult with hresult; subst hresult; simp
             exact Array.mem_of_getElem? ‹_›)
          | grind
    obtain ⟨r, d, hd, hmem⟩ := hinv outcome houtcome
    cases h
    simp_all
  · cases h
    exact Array.mem_of_getElem? ‹_›
set_option maxHeartbeats 4000000 in
/--
A branch control-flow action returned by interpreting an operation always targets one of the
provided successor blocks.
-/
theorem interpretOp'_branch_dest_mem {opType : OpCode} {properties : propertiesOf opType}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue}
    {blockOperands : Array BlockPtr} {mem mem' : MemoryState} {vals res : Array RuntimeValue}
    {dest : BlockPtr}
    (h : interpretOp' opType properties resultTypes operands blockOperands mem
      = .ok (vals, mem', some (.branch res dest))) :
    dest ∈ blockOperands := by
  cases opType
  case llvm op =>
    by_cases hSwitch : op = .switch
    · subst hSwitch
      simp only [interpretOp'] at h
      exact Llvm.interpretOp'_switch_dest_mem h
    cases op <;> first | exact absurd rfl hSwitch | dest_tac Llvm.interpretOp'
  case arith op => cases op <;> dest_tac Arith.interpretOp'
  case mod_arith op => cases op <;> dest_tac ModArith.interpretOp'
  case felt op => cases op <;> dest_tac Felt.interpretOp'
  case riscv op => cases op <;> dest_tac Riscv.interpretOp'
  case riscv_cf op => cases op <;> dest_tac Riscv_Cf.interpretOp'
  case riscv_stack op => cases op <;> dest_tac Riscv_Stack.interpretOp'
  case rv64 op => cases op <;> dest_tac Rv64.interpretOp'
  case cf op => cases op <;> dest_tac Cf.interpretOp'
  case comb op => cases op <;> dest_tac Comb.interpretOp'
  case hw op => cases op <;> dest_tac HW.interpretOp'
  case gmir op => cases op <;> dest_tac GMIR.interpretOp'
  case gmir_riscv op => cases op <;> dest_tac GMIR_RISCV.interpretOp'
  all_goals (try (rename_i op; cases op)) <;> dest_tac

end Veir

end
