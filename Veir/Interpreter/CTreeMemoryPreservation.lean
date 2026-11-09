module

public import Veir.Interpreter.CTreeOpcodeLemmas
public import Veir.Interpreter.Lemmas
import all Veir.Interpreter.CTree
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Interp
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
import all Veir.IR.OpInfo
import all Veir.Dialects.RISCV_Stack.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.OpInfo

import all Veir.Dialects.Arith.OpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Dialects.Func.OpInfo
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.RV64.OpInfo
import all Veir.Dialects.ModArith.OpInfo
import all Veir.Dialects.Datapath.OpInfo
import all Veir.Dialects.Comb.OpInfo
import all Veir.Dialects.HW.OpInfo
import all Veir.Dialects.Verif.OpInfo
import all Veir.Dialects.PDL.OpInfo
import all Veir.Dialects.IO.OpInfo
import all Veir.Dialects.Test.OpInfo
import all Veir.Dialects.LLZK.Felt.OpInfo
import all Veir.Dialects.LLZK.Include.OpInfo
import all Veir.Dialects.LLZK.Function.OpInfo
import all Veir.Dialects.Cir.OpInfo
import all Veir.Dialects.Seq.OpInfo
import all Veir.Dialects.Tensor.OpInfo
import all Veir.Dialects.SMT.OpInfo

namespace Veir

public section

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

private theorem array_forIn_preserves {α β : Type} (xs : Array α)
    (body : α → β → Interp (ForInStep β)) (P : β → Prop) (initial final : β)
    (hinit : P initial)
    (hstep : ∀ x state, P state → ∀ result, body x state = .ok result → P result.value)
    (h : forIn xs initial body = .ok final) : P final := by
  apply list_forIn_preserves xs.toList body P initial final hinit hstep
  simpa only [Array.forIn_toList] using h

set_option maxHeartbeats 2000000 in
/-- GEP returns only the original memory. -/
theorem Llvm.interpretOp'_gep_memory
    (properties : propertiesOf Llvm.getelementptr) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (layout : DataLayout)
    (h : Llvm.interpretOp' .getelementptr properties types operands successors before layout =
      .ok (results, after, action)) : after = before := by
  simp only [Llvm.interpretOp'] at h
  repeat first
    | cases h; rfl
    | contradiction
    | split at h
    | simp only [Bind.bind, Pure.pure, liftM, monadLift, MonadLift.monadLift] at h
  all_goals try grind

set_option maxHeartbeats 2000000 in
/-- A successful effect-free deterministic LLVM operation leaves memory unchanged. -/
theorem Llvm.interpretOp'_memory_of_noEffects
    (code : Llvm) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (layout : DataLayout)
    (effects : Llvm.getEffects code properties = .none)
    (hterm : Llvm.isTerminator code = false)
    (h : Llvm.interpretOp' code properties types operands successors before layout = .ok (results, after, action)) :
    after = before := by
  by_cases hgep : code = .getelementptr
  · subst code
    exact Llvm.interpretOp'_gep_memory properties types operands successors before after results action layout h
  cases code <;> simp [Llvm.isTerminator] at hterm <;> try contradiction
  all_goals simp [Llvm.getEffects, MemoryEffects.none, MemoryEffects.unknown, MemoryEffects.allocate,
    MemoryEffects.read, MemoryEffects.write, MemoryEffects.readWrite] at effects
  all_goals try { contradiction }
  all_goals
    try simp only [Llvm.interpretOp'] at h
    repeat first
      | cases h; rfl
      | contradiction
      | split at h
      | simp only [Bind.bind, Pure.pure] at h

  all_goals try grind

set_option maxHeartbeats 2000000 in
/-- A successful effect-free Riscv operation preserves memory. -/
theorem Riscv.interpretOp'_memory_of_noEffects
    (code : Riscv) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (effects : Riscv.getEffects code properties = .none)
    (h : Riscv.interpretOp' code properties types operands successors before = .ok (results, after, action)) :
    after = before := by
  cases code <;> simp [Riscv.getEffects, MemoryEffects.none, MemoryEffects.unknown, MemoryEffects.allocate,
    MemoryEffects.read, MemoryEffects.write, MemoryEffects.readWrite] at effects
  all_goals try { contradiction }
  all_goals
    try simp only [Riscv.interpretOp'] at h
    repeat first
      | cases h; rfl
      | contradiction
      | split at h
      | simp only [Bind.bind, Pure.pure] at h
  all_goals try grind

set_option maxHeartbeats 2000000 in
/-- A successful effect-free GMIR operation preserves memory. -/
theorem GMIR.interpretOp'_memory_of_noEffects
    (code : GMIR) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (effects : GMIR.getEffects code properties = .none)
    (h : GMIR.interpretOp' code properties types operands successors before = .ok (results, after, action)) :
    after = before := by
  cases code <;> simp [GMIR.getEffects, MemoryEffects.none, MemoryEffects.unknown, MemoryEffects.allocate,
    MemoryEffects.read, MemoryEffects.write, MemoryEffects.readWrite] at effects
  all_goals try { contradiction }
  all_goals
    try simp only [GMIR.interpretOp'] at h
    repeat first
      | cases h; rfl
      | contradiction
      | split at h
      | simp only [Bind.bind, Pure.pure] at h
  all_goals try grind

set_option maxHeartbeats 2000000 in
/-- A successful effect-free GMIR_RISCV operation preserves memory. -/
theorem GMIR_RISCV.interpretOp'_memory_of_noEffects
    (code : GMIR_RISCV) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (effects : GMIR_RISCV.getEffects code properties = .none)
    (h : GMIR_RISCV.interpretOp' code properties types operands successors before = .ok (results, after, action)) :
    after = before := by
  cases code <;> simp [GMIR_RISCV.getEffects, MemoryEffects.none, MemoryEffects.unknown, MemoryEffects.allocate,
    MemoryEffects.read, MemoryEffects.write, MemoryEffects.readWrite] at effects
  all_goals try { contradiction }
  all_goals
    try simp only [GMIR_RISCV.interpretOp'] at h
    repeat first
      | cases h; rfl
      | contradiction
      | split at h
      | simp only [Bind.bind, Pure.pure] at h
  all_goals
    simp only [GMIR_RISCV.base, GMIR.interpretOp'] at *
    repeat first
      | cases h; rfl
      | contradiction
      | split at *
      | simp only [Bind.bind, Pure.pure] at *
  all_goals try grind

set_option maxHeartbeats 2000000 in
/-- Successful deterministic nonterminators whose effect summary is empty preserve memory. -/
theorem interpretOp'_memory_of_noEffects
    (code : OpCode) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (effects : code.getEffects properties = .none) (nonterm : code.isTerminator = false)
    (h : Veir.interpretOp' code properties types operands successors before = .ok (results, after, action)) :
    after = before := by
  cases code with
  | llvm code =>
      exact Llvm.interpretOp'_memory_of_noEffects code properties types operands successors
        before after results action .riscv64 effects nonterm h
  | riscv code =>
      exact Riscv.interpretOp'_memory_of_noEffects code properties types operands successors
        before after results action effects h
  | gmir code =>
      exact GMIR.interpretOp'_memory_of_noEffects code properties types operands successors
        before after results action effects h
  | gmir_riscv code =>
      exact GMIR_RISCV.interpretOp'_memory_of_noEffects code properties types operands successors
        before after results action effects h
  | builtin code =>
      cases code <;> simp only [Veir.interpretOp'] at h
      all_goals
        repeat first
          | cases h; rfl
          | contradiction
          | split at h
          | simp only [Bind.bind, Pure.pure] at h
  | func code => cases code <;> simp [Veir.interpretOp', Pure.pure] at h <;> grind
  | cir code => cases code <;> simp [Veir.interpretOp', Pure.pure] at h <;> grind
  | riscv_stack code =>
      cases code <;> simp [OpCode.getEffects, Riscv_Stack.getEffects, MemoryEffects.none,
        MemoryEffects.allocate] at effects
  | _ =>
      simp only [Veir.interpretOp'] at h
      repeat first
        | cases h; rfl
        | contradiction
        | split at h
        | simp only [Bind.bind, Pure.pure] at h

open _root_.CTree

private theorem liftedInterp_ok_iff (value : Interp α) (result : α) :
    PureOrErr.CanInterpretTo (liftM value : CTree (ErrorE ⊕ₑ UBE) FreezeC α) (.ok result) ↔
      value = .ok result := by
  cases value <;> simp [liftM, monadLift, MonadLift.monadLift, Veir.fail, Veir.ub,
    _root_.CTree.CTree.trigger_def, Bind.bind, eq_comm]

set_option maxHeartbeats 1000000 in
 theorem Llvm.interpretOpCTree_memory_of_noEffects
    (code : Llvm) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (effects : code.getEffects properties = .none) (nonterm : code.isTerminator = false)
    (h : PureOrErr.CanInterpretTo
      (Llvm.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
      (.ok (results, after, action))) : after = before := by
  unfold Llvm.interpretOpCTree at h
  split at h
  · repeat first
      | split at h
      | simp only [CTree.choose_def, CTree.tau_def, Bind.bind, _root_.CTree.CTree.bind_tau,
          _root_.CTree.CTree.bind_ret, Pure.pure, Veir.fail, CTree.trigger_def,
          _root_.CTree.CTree.bind_vis, PureOrErr.CanInterpretTo.tauG_iff,
          PureOrErr.CanInterpretTo.pure_iff] at h
      | rcases h with ⟨_, h⟩
    all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, Veir.fail, CTree.trigger_def] at h
    all_goals grind
  · exact Llvm.interpretOp'_memory_of_noEffects code properties types operands successors
      before after results action .riscv64 effects nonterm ((liftedInterp_ok_iff _ _).mp h)

set_option maxHeartbeats 1000000 in
theorem GMIR.interpretOpCTree_memory_of_noEffects
    (code : GMIR) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (effects : code.getEffects properties = .none)
    (h : PureOrErr.CanInterpretTo
      (GMIR.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
      (.ok (results, after, action))) : after = before := by
  unfold GMIR.interpretOpCTree at h
  split at h
  · repeat first
      | split at h
      | simp only [CTree.tau_def, PureOrErr.CanInterpretTo.tauG_iff, CTree.ret_pure,
          PureOrErr.CanInterpretTo.pure_iff] at h
      | rcases h with ⟨_, h⟩
    all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, Veir.fail, CTree.trigger_def] at h
    all_goals grind
  · simp only [GMIR.getEffects] at effects
    split at effects <;> contradiction
  · exact GMIR.interpretOp'_memory_of_noEffects code properties types operands successors
      before after results action effects ((liftedInterp_ok_iff _ _).mp h)

set_option maxHeartbeats 1000000 in
theorem Builtin.interpretOpCTree_memory
    (code : Builtin) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (h : PureOrErr.CanInterpretTo
      (Builtin.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
      (.ok (results, after, action))) : after = before := by
  unfold Builtin.interpretOpCTree at h
  simp only [Builtin.interpretUnrealizedConversionCastCTree] at h
  repeat first
    | split at h
    | simp only [Builtin.byteToIntCTree, CTree.choose_def, CTree.tau_def, Bind.bind,
        _root_.CTree.CTree.bind_tau, _root_.CTree.CTree.bind_ret,
        Veir.fail, CTree.trigger_def, _root_.CTree.CTree.bind_vis,
        PureOrErr.CanInterpretTo.tauG_iff, CTree.ret_pure,
        PureOrErr.CanInterpretTo.pure_iff] at h
    | rcases h with ⟨_, h⟩
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, Veir.fail, CTree.trigger_def] at h
  all_goals grind

/-- Empty effect summaries preserve the actual historical memory on successful opcode execution. -/
theorem CTree.interpretOp'_memory_of_noEffects
    (code : OpCode) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (regions : Array RegionPtr)
    (effects : code.getEffects properties = .none) (nonterm : code.isTerminator = false)
    (h : PureOrErr.CanInterpretTo
      (CTree.interpretOp' code properties types operands successors before regions)
      (.ok (results, after, action))) : after = before := by
  cases code with
  | llvm code =>
      exact Llvm.interpretOpCTree_memory_of_noEffects code properties types operands successors
        before after results action effects nonterm h
  | gmir code =>
      exact GMIR.interpretOpCTree_memory_of_noEffects code properties types operands successors
        before after results action effects h
  | builtin code =>
      exact Builtin.interpretOpCTree_memory code properties types operands successors
        before after results action h
  | riscv code =>
      change PureOrErr.CanInterpretTo
        (Riscv.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
        (.ok (results, after, action)) at h
      unfold Riscv.interpretOpCTree at h
      split at h
      all_goals first
        | exact Riscv.interpretOp'_memory_of_noEffects code properties types operands successors
            before after results action effects ((liftedInterp_ok_iff _ _).mp h)
        | simp_all [OpCode.getEffects, Riscv.getEffects, MemoryEffects.read, MemoryEffects.none]
      all_goals split at effects <;> simp_all [MemoryEffects.readWrite]
  | _ =>
      exact Veir.interpretOp'_memory_of_noEffects _ properties types operands successors
        before after results action effects nonterm ((liftedInterp_ok_iff _ _).mp h)

set_option maxHeartbeats 2000000 in
/-- Nonterminator semantics ignore the successor list. -/
theorem CTree.interpretOp'_successors_irrelevant
    (code : OpCode) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (left right : Array BlockPtr)
    (memory : MemoryState) (regions : Array RegionPtr)
    (nonterm : code.isTerminator = false) :
    CTree.interpretOp' code properties types operands left memory regions =
      CTree.interpretOp' code properties types operands right memory regions := by
  cases code <;> rename_i op <;> cases op
  all_goals first
    | rfl
    | change true = false at nonterm; contradiction

end

end Veir
