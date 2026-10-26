module
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Dialects.RISCV_Stack.OpInfo
import all Veir.Dialects.Cir.OpInfo
import all Veir.Dialects.Func.OpInfo
import all Veir.Dialects.Arith.OpInfo
import all Veir.Dialects.ModArith.OpInfo
import all Veir.Dialects.LLZK.Felt.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.RV64.OpInfo
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.Comb.OpInfo
import all Veir.Dialects.HW.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Interpreter.Basic
import all Veir.GlobalOpInfo
import all Veir.Dialects.RISCV.OpInfo

public import Veir.Interpreter.CTreeInterpreter

import all Veir.Interpreter.CTree
import all CTree.Defs
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Interpreter.Interp
import all Veir.IR.OpInfo
import Veir.DataLayout.RISCV64
public section

/-!
# Memory and control-flow preservation from opcode metadata

These theorems prove concrete properties of interpreter outcomes. No semantic
axiom connecting the memory-effect metadata to the interpreter is assumed.
-/

namespace Veir

open _root_.CTree

private theorem forIn_list_invariant {α β : Type} (P : β → Prop)
    (xs : List α) (body : α → β → Interp (ForInStep β))
    (hbody : ∀ x state step, P state → body x state = .ok step →
      match step with | .done state' | .yield state' => P state')
    (state result : β) (hstate : P state)
    (hrun : forIn xs state body = .ok result) : P result := by
  induction xs generalizing state with
  | nil =>
    simp only [List.forIn_nil, Interp.pure_eq, Interp.ok.injEq] at hrun
    subst result
    exact hstate
  | cons x xs ih =>
    rw [List.forIn_cons] at hrun
    cases hstep : body x state with
    | fail _ => simp [hstep] at hrun
    | ub _ => simp [hstep] at hrun
    | ok step =>
      have hnext := hbody x state step hstate hstep
      cases step with
      | done next =>
        simp only [hstep, Interp.bind_ok, Interp.pure_eq, Interp.ok.injEq] at hrun
        subst result
        exact hnext
      | yield next =>
        apply ih next hnext
        simpa [hstep] using hrun

private theorem forIn_array_invariant {α β : Type} (P : β → Prop)
    (xs : Array α) (body : α → β → Interp (ForInStep β))
    (hbody : ∀ x state step, P state → body x state = .ok step →
      match step with | .done state' | .yield state' => P state')
    (state result : β) (hstate : P state)
    (hrun : forIn xs state body = .ok result) : P result := by
  apply forIn_list_invariant P xs.toList body hbody state result hstate
  simpa only [Array.forIn_toList] using hrun

private theorem gep_loop_preserves_memory
    (dynamic : Array (RuntimeValue × Nat)) (base : Int) (mem : MemoryState)
    (result : Option (Array RuntimeValue × MemoryState × Option ControlFlowAction) × Int)
    (hrun : (forIn (m := Interp) dynamic (none, base) fun (x : RuntimeValue × Nat)
      (state : Option (Array RuntimeValue × MemoryState × Option ControlFlowAction) × Int) =>
      match x.fst with
      | .int _ idx =>
        match idx with
        | .val idx => pure (.yield (none, state.snd + idx.toInt * x.snd))
        | _ => pure (.done (some (#[.addr .poison], mem, none), state.snd))
      | _ => .fail none) = .ok result) :
    ∀ out, result.fst = some out → out.2.1 = mem ∧ out.2.2 = none := by
  apply forIn_array_invariant
    (fun state => ∀ out, state.fst = some out → out.2.1 = mem ∧ out.2.2 = none)
    dynamic _ _ (none, base) result (by simp) hrun
  intro x state step hstate hstep
  repeat' first | simp_all | split at hstep
  all_goals subst step <;> simp

/-- A successful LLVM opcode that is not a block terminator with no writes or allocations preserves
memory and produces no control-flow action. -/
theorem Llvm.interpretOp'_preserves_memory_and_control (op : Llvm) (props : Llvm.propertiesOf op) (tys : Array TypeAttr)
  (args : Array RuntimeValue) (succs : Array BlockPtr) (mem mem' : MemoryState)
  (vals : Array RuntimeValue) (act : Option ControlFlowAction) (layout : DataLayout)
  (hw : (Llvm.getEffects op props).writes = false)
  (ha : (Llvm.getEffects op props).allocates = false)
  (ht : Llvm.isTerminator op = false)
  (hrun : Llvm.interpretOp' op props tys args succs mem layout = .ok (vals,mem',act)) : mem'=mem ∧ act=none := by
  cases op <;> try simp_all [Llvm.getEffects, Llvm.isTerminator, MemoryEffects.none,
    MemoryEffects.unknown, MemoryEffects.allocate, MemoryEffects.read,
    MemoryEffects.write, MemoryEffects.readWrite]
  all_goals try (split at hw <;> simp_all)
  all_goals simp only [Llvm.interpretOp', Interp.bind_def] at hrun
  all_goals repeat' first | simp_all | split at hrun
  have hs := gep_loop_preserves_memory _ _ mem _ (by assumption)
  exact hs _ (by assumption)

/-- Lifting an interpreter outcome creates exactly its successful return, if any. -/
@[simp]
theorem PureOrErr.CanInterpretTo.monadLift_ok_iff (outcome : Interp α) (value : α) :
    CanInterpretTo (monadLift outcome : Tree α) (.ok value) ↔ outcome = .ok value := by
  cases outcome <;>
    simp [monadLift, MonadLift.monadLift, Veir.fail, Veir.ub, _root_.CTree.CTree.trigger, Bind.bind, eq_comm]

/-- An ordinary interpreter outcome lifts to a finite tree with only UB/error events. -/
@[simp]
theorem PureOrErr.monadLift (outcome : Interp α) : PureOrErr (monadLift outcome : Tree α) := by
  cases outcome with
  | ok value => exact .ret value
  | fail _ =>
    change PureOrErr (Veir.fail : Tree α)
    simp only [Veir.fail, _root_.CTree.CTree.trigger, Bind.bind, _root_.CTree.CTree.bind_vis]
    exact .fail
  | ub _ =>
    change PureOrErr (Veir.ub : Tree α)
    simp only [Veir.ub, _root_.CTree.CTree.trigger, Bind.bind, _root_.CTree.CTree.bind_vis]
    exact .ub

/-- Failure has no successful returned value. -/
@[simp]
theorem PureOrErr.CanInterpretTo.fail_ok (value : α) :
    ¬CanInterpretTo (Veir.fail : Tree α) (.ok value) := by
  intro h
  have hbad := (monadLift_ok_iff (Interp.fail (α := α) none) value).mp h
  cases hbad

/-- UB has no successful returned value. -/
@[simp]
theorem PureOrErr.CanInterpretTo.ub_ok (value : α) :
    ¬CanInterpretTo (Veir.ub : Tree α) (.ok value) := by
  intro h
  have hbad := (monadLift_ok_iff (Interp.ub (α := α) none) value).mp h
  cases hbad

/-- Choices have finite depth and introduce no visible effects. -/
@[simp]
theorem PureOrErr.choose (choice : FreezeCIn) :
    PureOrErr (_root_.CTree.CTree.choose choice : Tree (FreezeC choice)) := by
  rw [_root_.CTree.CTree.choose_def, _root_.CTree.CTree.tau_def]
  exact .tau _ _ (fun _ => .ret _)

/-- The CTree LLVM interpreter respects the same memory and control-flow metadata,
including every possible freeze choice. -/
theorem Llvm.interpretOpCTree_preserves_memory_and_control
    (op : Llvm) (props : Llvm.propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem mem' : MemoryState)
    (vals : Array RuntimeValue) (act : Option ControlFlowAction) (layout : DataLayout)
    (hw : (Llvm.getEffects op props).writes = false)
    (ha : (Llvm.getEffects op props).allocates = false)
    (ht : Llvm.isTerminator op = false)
    (hrun : PureOrErr.CanInterpretTo
      (Llvm.interpretOpCTree op props tys args succs mem layout) (.ok (vals, mem', act))) :
    mem' = mem ∧ act = none := by
  by_cases hfreeze : op = .freeze
  · subst op
    simp only [Llvm.interpretOpCTree] at hrun
    repeat' first
    | simp_all [PureOrErr.CanInterpretTo.bind_iff, Bind.bind]
    | split at hrun
  · have heq : Llvm.interpretOpCTree op props tys args succs mem layout =
        monadLift (Llvm.interpretOp' op props tys args succs mem layout) := by
      cases op <;> simp_all [Llvm.interpretOpCTree]
    rw [heq, PureOrErr.CanInterpretTo.monadLift_ok_iff] at hrun
    exact Llvm.interpretOp'_preserves_memory_and_control
      op props tys args succs mem mem' vals act layout hw ha ht hrun

private theorem riscvLoad_preserves_memory (mem mem' : MemoryState) (address : BitVec 64)
    (bytes : Nat) (extension : LoadExtension) (value : BitVec 64)
    (hrun : riscvLoad mem address bytes extension = .ok (value, mem')) : mem' = mem := by
  simp only [riscvLoad, Interp.bind_def] at hrun
  repeat' first | simp_all | split at hrun

set_option maxHeartbeats 800000 in
/-- Concrete effect metadata soundness for the outcome-monad opcode interpreter.
No memory-effect or control-flow axiom is used. -/
theorem interpretOp'_preserves_memory_and_control
    (op : OpCode) (props : propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem mem' : MemoryState)
    (vals : Array RuntimeValue) (act : Option ControlFlowAction) (layout : DataLayout)
    (hw : (OpCode.getEffects op props).writes = false)
    (ha : (OpCode.getEffects op props).allocates = false)
    (ht : OpCode.isTerminator op = false)
    (hrun : Veir.interpretOp' op props tys args succs mem layout = .ok (vals, mem', act)) :
    mem' = mem ∧ act = none := by
  cases op
  case llvm op =>
    exact Llvm.interpretOp'_preserves_memory_and_control op props tys args succs
      mem mem' vals act layout (by simpa [get_effects] using hw)
      (by simpa [get_effects] using ha) (by simpa [is_terminator] using ht) hrun
  all_goals rename_i op
  all_goals cases op
  all_goals try simp_all [get_effects, is_terminator, Cir.isTerminator, Cir.getEffects, Riscv_Stack.getEffects, MemoryEffects.none,
    MemoryEffects.unknown, MemoryEffects.allocate, MemoryEffects.read,
    MemoryEffects.write, MemoryEffects.readWrite]
  all_goals try (split at hw <;> simp_all)
  all_goals simp only [Veir.interpretOp', Arith.interpretOp', ModArith.interpretOp',
    Felt.interpretOp', Riscv.interpretOp', Riscv_Cf.interpretOp', Rv64.interpretOp',
    Comb.interpretOp', HW.interpretOp', GMIR.interpretOp', Interp.bind_def] at hrun
  all_goals repeat' first | simp_all | split at *
  all_goals try grind
  all_goals have hs := riscvLoad_preserves_memory _ _ _ _ _ _ (by assumption)
  all_goals grind

/-- Successful binding reaches a successful left result and then a successful continuation. -/
@[simp]
theorem PureOrErr.CanInterpretTo.bind_ok_iff (tree : Tree α) (next : α → Tree β) (value : β) :
    CanInterpretTo (_root_.CTree.bind tree next) (.ok value) ↔
      ∃ result, CanInterpretTo tree (.ok result) ∧ CanInterpretTo (next result) (.ok value) := by
  simp [PureOrErr.CanInterpretTo.bind_iff]

private theorem riscvLoadCTree_preserves_memory (mem : MemoryState) (address : BitVec 64)
    (bytes : Nat) (extension : LoadExtension) (result : BitVec 64 × MemoryState)
    (hrun : PureOrErr.CanInterpretTo (riscvLoadCTree mem address bytes extension) (.ok result)) :
    result.2 = mem := by
  simp only [riscvLoadCTree, Bind.bind, PureOrErr.CanInterpretTo.bind_ok_iff] at hrun
  grind

private theorem interpretRiscvLoad_preserves_memory_and_control
    (props : RISCVMemProperties) (args : Array RuntimeValue) (mem mem' : MemoryState)
    (bytes : Nat) (extension : LoadExtension) (vals : Array RuntimeValue) (act : Option ControlFlowAction)
    (hrun : PureOrErr.CanInterpretTo
      (interpretRiscvLoad props args mem bytes extension) (.ok (vals, mem', act))) :
    mem' = mem ∧ act = none := by
  simp only [interpretRiscvLoad] at hrun
  repeat' first
  | simp_all [PureOrErr.CanInterpretTo.bind_ok_iff, Bind.bind]
  | split at hrun
  all_goals rcases hrun with ⟨value, memOut, hload, hresult⟩
  all_goals have hmem := riscvLoadCTree_preserves_memory _ _ _ _ (value, memOut) hload
  all_goals grind

private theorem builtin_deterministic_preserves_memory_and_control
    (op : Builtin) (props : Builtin.propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem mem' : MemoryState)
    (vals : Array RuntimeValue) (act : Option ControlFlowAction) (layout : DataLayout)
    (hrun : Veir.interpretOp' (.builtin op) props tys args succs mem layout = .ok (vals, mem', act)) :
    mem' = mem ∧ act = none := by
  cases op <;> simp only [Veir.interpretOp', Interp.bind_def] at hrun
  all_goals repeat' first | simp_all | split at hrun

/-- Builtin CTree choices preserve the memory and do not change control flow. -/
theorem Builtin.interpretOpCTree_preserves_memory_and_control
    (op : Builtin) (props : Builtin.propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem mem' : MemoryState)
    (vals : Array RuntimeValue) (act : Option ControlFlowAction) (layout : DataLayout)
    (hrun : PureOrErr.CanInterpretTo
      (Builtin.interpretOpCTree op props tys args succs mem layout) (.ok (vals, mem', act))) :
    mem' = mem ∧ act = none := by
  cases op <;> simp only [Builtin.interpretOpCTree] at hrun
  all_goals repeat' first
  | simp_all [PureOrErr.CanInterpretTo.bind_ok_iff, Bind.bind]
  | split at hrun
  all_goals exact builtin_deterministic_preserves_memory_and_control _ _ _ _ _ _ _ _ _ _ (by assumption)

private theorem lifted_interpretOp'_preserves_memory_and_control
    (op : OpCode) (props : propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem mem' : MemoryState)
    (vals : Array RuntimeValue) (act : Option ControlFlowAction) (layout : DataLayout)
    (hw : (OpCode.getEffects op props).writes = false)
    (ha : (OpCode.getEffects op props).allocates = false)
    (ht : OpCode.isTerminator op = false)
    (hrun : PureOrErr.CanInterpretTo
      (monadLift (Veir.interpretOp' op props tys args succs mem layout) : Tree _)
      (.ok (vals, mem', act))) : mem' = mem ∧ act = none := by
  rw [PureOrErr.CanInterpretTo.monadLift_ok_iff] at hrun
  exact interpretOp'_preserves_memory_and_control op props tys args succs
    mem mem' vals act layout hw ha ht hrun

/-- A successful leaf of an opcode with no writes, allocations, or control-flow
termination preserves memory exactly and produces no control-flow action. -/
theorem CTree.interpretOpTree_preserves_memory_and_control
    (op : OpCode) (props : propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem mem' : MemoryState)
    (vals : Array RuntimeValue) (act : Option ControlFlowAction)
    (hw : (OpCode.getEffects op props).writes = false)
    (ha : (OpCode.getEffects op props).allocates = false)
    (ht : OpCode.isTerminator op = false)
    (hrun : PureOrErr.CanInterpretTo
      (CTree.interpretOpTree op props tys args succs mem) (.ok (vals, mem', act))) :
    mem' = mem ∧ act = none := by
  cases op
  case llvm op =>
    simp only [CTree.interpretOpTree] at hrun
    exact Llvm.interpretOpCTree_preserves_memory_and_control op props tys args succs
      mem mem' vals act .riscv64 (by simpa [get_effects] using hw)
      (by simpa [get_effects] using ha) (by simpa [is_terminator] using ht) hrun
  case builtin op =>
    simp only [CTree.interpretOpTree] at hrun
    exact Builtin.interpretOpCTree_preserves_memory_and_control
      op props tys args succs mem mem' vals act .riscv64 hrun
  case riscv op =>
    simp only [CTree.interpretOpTree] at hrun
    cases op <;> simp only [Riscv.interpretOpCTree] at hrun
    all_goals first
    | exact interpretRiscvLoad_preserves_memory_and_control _ _ _ _ _ _ _ _ hrun
    | exact lifted_interpretOp'_preserves_memory_and_control (.riscv _) props tys args succs mem mem' vals act .riscv64 hw ha ht hrun
  case arith op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.arith op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case mod_arith op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.mod_arith op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case felt op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.felt op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case riscv_cf op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.riscv_cf op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case riscv_stack op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.riscv_stack op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case rv64 op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.rv64 op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case cf op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.cf op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case comb op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.comb op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case hw op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.hw op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case func op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.func op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case cir op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.cir op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case gmir op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.gmir op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case verif op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.verif op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case datapath op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.datapath op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case pdl op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.pdl op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case io op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.io op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case test op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.test op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case «include» op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.include op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case function op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.function op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun
  case seq op =>
    exact lifted_interpretOp'_preserves_memory_and_control (.seq op) props tys args succs
      mem mem' vals act .riscv64 hw ha ht hrun

@[simp]
theorem PureOrErr.pure_tree (value : α) : PureOrErr (pure value : Tree α) := .ret value

@[simp]
theorem PureOrErr.fail_tree : PureOrErr (Veir.fail : Tree α) := by
  exact PureOrErr.monadLift (Interp.fail none)

@[simp]
theorem PureOrErr.ub_tree : PureOrErr (Veir.ub : Tree α) := by
  exact PureOrErr.monadLift (Interp.ub none)

/-- LLVM operation trees have finite depth, including every freeze choice. -/
theorem Llvm.interpretOpCTree_pureOrErr
    (op : Llvm) (props : Llvm.propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem : MemoryState) (layout : DataLayout) :
    PureOrErr (Llvm.interpretOpCTree op props tys args succs mem layout) := by
  cases op <;> simp only [Llvm.interpretOpCTree]
  all_goals repeat' first
  | exact PureOrErr.monadLift _
  | exact PureOrErr.pure_tree _
  | exact PureOrErr.fail_tree
  | exact PureOrErr.ub_tree
  | exact PureOrErr.choose _
  | apply PureOrErr.bind
  | (intro)
  | split

/-- Builtin operation trees have finite depth. -/
theorem Builtin.interpretOpCTree_pureOrErr
    (op : Builtin) (props : Builtin.propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem : MemoryState) (layout : DataLayout) :
    PureOrErr (Builtin.interpretOpCTree op props tys args succs mem layout) := by
  cases op <;> simp only [Builtin.interpretOpCTree]
  all_goals repeat' first
  | exact PureOrErr.monadLift _
  | exact PureOrErr.pure_tree _
  | exact PureOrErr.fail_tree
  | exact PureOrErr.ub_tree
  | exact PureOrErr.choose _
  | apply PureOrErr.bind
  | (intro)
  | split

private theorem riscvLoadCTree_pureOrErr
    (mem : MemoryState) (address : BitVec 64) (bytes : Nat) (extension : LoadExtension) :
    PureOrErr (riscvLoadCTree mem address bytes extension) := by
  simp only [riscvLoadCTree]
  repeat' first
  | exact PureOrErr.monadLift _
  | exact PureOrErr.pure_tree _
  | exact PureOrErr.fail_tree
  | exact PureOrErr.ub_tree
  | exact PureOrErr.choose _
  | apply PureOrErr.bind
  | (intro)
  | split

private theorem interpretRiscvLoad_pureOrErr
    (props : RISCVMemProperties) (args : Array RuntimeValue) (mem : MemoryState)
    (bytes : Nat) (extension : LoadExtension) :
    PureOrErr (interpretRiscvLoad props args mem bytes extension) := by
  simp only [interpretRiscvLoad]
  repeat' first
  | exact riscvLoadCTree_pureOrErr _ _ _ _
  | exact PureOrErr.pure_tree _
  | exact PureOrErr.fail_tree
  | apply PureOrErr.bind
  | (intro)
  | split

/-- RISC-V operation trees have finite depth, including loads from poisoned memory. -/
theorem Riscv.interpretOpCTree_pureOrErr
    (op : Riscv) (props : Riscv.propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem : MemoryState) :
    PureOrErr (Riscv.interpretOpCTree op props tys args succs mem) := by
  cases op <;> simp only [Riscv.interpretOpCTree]
  all_goals first
  | exact PureOrErr.monadLift _
  | exact interpretRiscvLoad_pureOrErr _ _ _ _ _

/-- A single opcode executes a finite tree; unbounded control flow belongs to the CFG interpreter. -/
theorem CTree.interpretOpTree_pureOrErr
    (op : OpCode) (props : propertiesOf op) (tys : Array TypeAttr)
    (args : Array RuntimeValue) (succs : Array BlockPtr) (mem : MemoryState) :
    PureOrErr (CTree.interpretOpTree op props tys args succs mem) := by
  cases op <;> simp only [CTree.interpretOpTree]
  all_goals first
  | exact Llvm.interpretOpCTree_pureOrErr _ _ _ _ _ _ _
  | exact Builtin.interpretOpCTree_pureOrErr _ _ _ _ _ _ _
  | exact Riscv.interpretOpCTree_pureOrErr _ _ _ _ _ _
  | exact PureOrErr.monadLift _

end Veir
