module

public import Veir.Interpreter.CTreeOpcodeLemmas
public import Veir.Interpreter.Lemmas
import Veir.Dialects.ResultsConform
import all Veir.Interpreter.CTree
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Interp
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Interpreter.Memory
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Interpreter.RuntimeValue.Conforms
import all Veir.Interpreter.RuntimeValue.ArrayConformsSimp

namespace Veir
public section
open _root_.CTree

/-- Replacing a runtime payload while keeping its kind and width preserves type conformance. -/
def RuntimeValue.ResultShapeRefines (left right : Array RuntimeValue) : Prop :=
  ∀ types, RuntimeValue.ArrayConforms left types → RuntimeValue.ArrayConforms right types

private theorem liftedInterp_ok_iff (value : Interp α) (result : α) :
    PureOrErr.CanInterpretTo (liftM value : Tree α) (.ok result) ↔ value = .ok result := by
  cases value <;> simp [liftM, monadLift, MonadLift.monadLift, Veir.fail, Veir.ub,
    CTree.trigger_def, Bind.bind, eq_comm]

private theorem singleton_get (value : α) [Inhabited α] : (#[value])[0]! = value := by simp

set_option maxHeartbeats 1000000 in
theorem Llvm.interpretOpCTree_result_shape
    (code : Llvm) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (h : PureOrErr.CanInterpretTo
      (Llvm.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
      (.ok (results, after, action))) :
    ∃ deterministic, Llvm.interpretOp' code properties types operands successors before .riscv64 =
      .ok (deterministic, after, action) ∧ RuntimeValue.ResultShapeRefines deterministic results := by
  unfold Llvm.interpretOpCTree at h
  split at h
  · repeat first | split at h
    all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff, Veir.fail, CTree.trigger_def] at h
    all_goals simp_all [Llvm.interpretOp', Bind.bind, Pure.pure]
    all_goals try simp_all
    all_goals try rcases h with ⟨⟨choice, rfl⟩, _, _⟩
    all_goals intro ts conf
    all_goals
      simp only [RuntimeValue.ArrayConforms, Array.size_singleton, Nat.lt_one_iff,
        forall_eq] at conf ⊢
      simp only [singleton_get] at conf ⊢
      rcases conf with ⟨size, conf⟩
      refine ⟨size, ?_⟩
      cases hty : ts[0]! with
      | mk val verified => cases val <;> simpa only [RuntimeValue.Conforms, hty, TypeAttr.of_def, Attribute.of_def, IsAttr.inject] using conf
  · exact ⟨results, (liftedInterp_ok_iff _ _).mp h, fun _ ht => ht⟩

set_option maxHeartbeats 1000000 in
theorem GMIR.interpretOpCTree_result_shape
    (code : GMIR) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (h : PureOrErr.CanInterpretTo
      (GMIR.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
      (.ok (results, after, action))) :
    ∃ deterministic, GMIR.interpretOp' code properties types operands successors before =
      .ok (deterministic, after, action) ∧ RuntimeValue.ResultShapeRefines deterministic results := by
  unfold GMIR.interpretOpCTree at h
  split at h
  · repeat first | split at h
    all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
      Veir.fail, CTree.trigger_def] at h
    all_goals simp_all only [GMIR.interpretOp', Bind.bind, Pure.pure, Attribute.of_def, IsAttr.inject]
    all_goals try simp_all
    all_goals try rcases h with ⟨⟨choice, rfl⟩, _, _⟩
    all_goals intro ts conf
    all_goals
      simp only [RuntimeValue.ArrayConforms, Array.size_singleton, Nat.lt_one_iff,
        forall_eq] at conf ⊢
      simp only [singleton_get] at conf ⊢
      rcases conf with ⟨size, conf⟩
      refine ⟨size, ?_⟩
      cases hty : ts[0]! with
      | mk val verified => cases val <;> simpa only [RuntimeValue.Conforms, hty, TypeAttr.of_def, Attribute.of_def, IsAttr.inject] using conf
  · simp only [Bind.bind, PureOrErr.CanInterpretTo.bind_iff] at h
    simp only [liftedInterp_ok_iff, reduceCtorEq, and_false, or_false] at h
    obtain ⟨⟨deterministic, memory, control⟩, hdet, h⟩ := h
    dsimp at h
    split at h
    · rename_i width value hvalues
      have hvalues' : deterministic = #[.int width value] := by
        simpa using congrArg List.toArray hvalues
      subst deterministic
      split at h
      · simp at h
        obtain ⟨⟨choice, rfl⟩, rfl, rfl⟩ := h
        refine ⟨_, hdet, ?_⟩
        intro ts conf
        simp only [RuntimeValue.ArrayConforms, Array.size_singleton, Nat.lt_one_iff,
          forall_eq, singleton_get] at conf ⊢
        rcases conf with ⟨size, conf⟩
        refine ⟨size, ?_⟩
        cases hty : ts[0]! with
        | mk val verified =>
          cases val <;> simpa only [RuntimeValue.Conforms, hty, TypeAttr.of_def,
            Attribute.of_def, IsAttr.inject] using conf
      · simp only [PureOrErr.CanInterpretTo.pure_iff] at h
        cases h
        exact ⟨_, hdet, fun _ ht => ht⟩
    · simp only [PureOrErr.CanInterpretTo.pure_iff] at h
      cases h
      exact ⟨_, hdet, fun _ ht => ht⟩
  · exact ⟨results, (liftedInterp_ok_iff _ _).mp h, fun _ ht => ht⟩

set_option linter.unusedSimpArgs false in
/-- Builtin casts never produce control-flow actions. -/
theorem Builtin.interpretOpCTree_no_action
    (code : Builtin) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (h : PureOrErr.CanInterpretTo
      (Builtin.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
      (.ok (results, after, action))) : action = none := by
  unfold Builtin.interpretOpCTree at h
  simp only [Builtin.interpretUnrealizedConversionCastCTree] at h
  all_goals repeat split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
    Veir.fail, _root_.CTree.CTree.trigger_def, Builtin.byteToIntCTree] at h
  all_goals repeat split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
    Veir.fail, _root_.CTree.CTree.trigger_def, Builtin.byteToIntCTree] at h
  all_goals repeat split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
    Veir.fail, _root_.CTree.CTree.trigger_def, Builtin.byteToIntCTree] at h
  all_goals repeat split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
    Veir.fail, _root_.CTree.CTree.trigger_def, Builtin.byteToIntCTree] at h
  all_goals repeat split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
    Veir.fail, _root_.CTree.CTree.trigger_def, Builtin.byteToIntCTree] at h
  all_goals grind

/-- RISC-V instructions never produce control-flow actions. -/
theorem Riscv.interpretOpCTree_no_action
    (code : Riscv) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (h : PureOrErr.CanInterpretTo
      (Riscv.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
      (.ok (results, after, action))) : action = none := by
  unfold Riscv.interpretOpCTree at h
  split at h
  all_goals first
    | exact (Riscv.interpretOp'_ok_results ((liftedInterp_ok_iff _ _).mp h)).2
    | skip
  all_goals unfold riscvLoadCTree at h
  all_goals split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
    Veir.fail, _root_.CTree.CTree.trigger_def, liftedInterp_ok_iff, Bind.bind] at h
  all_goals grind

/-- Nondeterministic primitive execution either agrees with a deterministic control-flow
outcome, or has no control-flow action. Register payload choices need not preserve x0 conformance. -/
theorem CTree.interpretOp'_controlFlow
    (code : OpCode) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (regions : Array RegionPtr)
    (h : PureOrErr.CanInterpretTo
      (CTree.interpretOp' code properties types operands successors before regions)
      (.ok (results, after, action))) :
    (∃ deterministic, Veir.interpretOp' code properties types operands successors before =
      .ok (deterministic, after, action)) ∨ action = none := by
  cases code with
  | llvm code =>
    obtain ⟨deterministic, legacy, _⟩ := Llvm.interpretOpCTree_result_shape _ _ _ _ _ _ _ _ _ h
    exact .inl ⟨deterministic, legacy⟩
  | gmir code =>
    obtain ⟨deterministic, legacy, _⟩ := GMIR.interpretOpCTree_result_shape _ _ _ _ _ _ _ _ _ h
    exact .inl ⟨deterministic, legacy⟩
  | builtin code =>
    simp only [CTree.interpretOp', CTree.checkResultTypes_ok_iff] at h
    exact .inr (Builtin.interpretOpCTree_no_action _ _ _ _ _ _ _ _ _ h.1)
  | riscv code =>
    simp only [CTree.interpretOp', CTree.checkResultTypes_ok_iff] at h
    exact .inr (Riscv.interpretOpCTree_no_action _ _ _ _ _ _ _ _ _ h.1)
  | _ => exact .inl ⟨results, (liftedInterp_ok_iff _ _).mp h⟩

/-- Successful checked register results conform by construction; integer dialects preserve
conformance across nondeterministic payload choices. -/
theorem CTree.interpretOp'_results_conform {ctx : WfIRContext OpCode} {op : OperationPtr}
    {hop : op.InBounds ctx.raw} (verified : op.Verified ctx hop)
    {operands results : Array RuntimeValue} {before after : MemoryState} {action : Option ControlFlowAction}
    (conforms : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : PureOrErr.CanInterpretTo
      (CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
        operands (op.getSuccessors! ctx.raw) before (op.getRegions! ctx.raw))
      (.ok (results, after, action))) :
    RuntimeValue.ArrayConforms results (op.getResultTypes! ctx.raw) := by
  generalize hc : op.getOpType! ctx.raw = code at h
  cases code with
  | llvm code =>
    obtain ⟨deterministic, legacy, shape⟩ := Llvm.interpretOpCTree_result_shape _ _ _ _ _ _ _ _ _ h
    refine shape _ (Veir.interpretOp'_results_conform (mem := before) (mem' := after)
      (act := action) verified conforms ?_)
    simp only [OperationPtr.interpret]
    rw [hc]
    exact legacy
  | gmir code =>
    obtain ⟨deterministic, legacy, shape⟩ := GMIR.interpretOpCTree_result_shape _ _ _ _ _ _ _ _ _ h
    refine shape _ (Veir.interpretOp'_results_conform (mem := before) (mem' := after)
      (act := action) verified conforms ?_)
    simp only [OperationPtr.interpret]
    rw [hc]
    exact legacy
  | builtin code => exact (CTree.checkResultTypes_ok_iff.mp h).2
  | riscv code => exact (CTree.checkResultTypes_ok_iff.mp h).2
  | _ =>
    apply Veir.interpretOp'_results_conform (mem := before) (mem' := after) (act := action) verified conforms
    simp only [OperationPtr.interpret]
    rw [hc]
    exact (liftedInterp_ok_iff _ _).mp h

end
end Veir
