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
    all_goals simp [ PureOrErr.CanInterpretTo.map_iff, Veir.fail, CTree.trigger_def] at h
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
    all_goals simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
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

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem Builtin.interpretOpCTree_result_shape
    (code : Builtin) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (h : PureOrErr.CanInterpretTo
      (Builtin.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
      (.ok (results, after, action))) :
    ∃ deterministic, Veir.interpretOp' (.builtin code) properties types operands successors before =
      .ok (deterministic, after, action) ∧ RuntimeValue.ResultShapeRefines deterministic results := by
  unfold Builtin.interpretOpCTree at h
  simp only [Builtin.interpretUnrealizedConversionCastCTree] at h
  all_goals repeat split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
      Veir.fail, CTree.trigger_def, Builtin.byteToIntCTree] at h
  all_goals repeat split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
      Veir.fail, CTree.trigger_def, Builtin.byteToIntCTree] at h
  all_goals repeat split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
      Veir.fail, CTree.trigger_def, Builtin.byteToIntCTree] at h
  all_goals repeat split at h
  all_goals try simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
      Veir.fail, CTree.trigger_def, Builtin.byteToIntCTree] at h
  all_goals simp_all only [Veir.interpretOp', Bind.bind, Pure.pure, Attribute.of_def, IsAttr.inject]
  all_goals try
    obtain ⟨choice, choices, hresults, hmemory, haction⟩ := h
    obtain ⟨bits, hbits⟩ := choices
    subst choice
    subst results
    subst after
    subst action
    simp
  all_goals try simp_all
  all_goals try rcases h with ⟨⟨choice, rfl⟩, _, _⟩
  all_goals try rcases result with ⟨choice, rfl⟩
  all_goals intro ts conf
  all_goals try exact conf
  all_goals
    simp only [RuntimeValue.ArrayConforms, Array.size_singleton, Nat.lt_one_iff,
        forall_eq] at conf ⊢
    simp only [singleton_get] at conf ⊢
    rcases conf with ⟨size, conf⟩
    refine ⟨size, ?_⟩
    cases hty : ts[0]! with
      | mk val verified => cases val <;> simpa only [RuntimeValue.Conforms, hty, TypeAttr.of_def, Attribute.of_def, IsAttr.inject] using conf

private theorem loadByte_load_exists (memory : MemoryState) (pointer : Data.Pointer)
    (bytes : Nat) (value : Data.LLVM.Byte (8 * bytes))
    (h : memory.loadByte pointer (8 * bytes) = .ok value) :
    ∃ raw, memory.load pointer bytes.toUInt64 = .ok raw := by
  unfold MemoryState.loadByte at h
  simp only [show 8 * bytes % 8 = 0 by omega, ne_eq, not_true_eq_false,
    ↓reduceIte, show 8 * bytes / 8 = bytes by omega] at h
  cases hp : memory.loadPoison pointer bytes.toUInt64 <;>
    cases hl : memory.load pointer bytes.toUInt64 <;>
    simp_all [Bind.bind, Pure.pure]

private theorem register_result_shape (left right : Data.RISCV.Reg) :
    RuntimeValue.ResultShapeRefines #[.reg left] #[.reg right] := by
  intro ts conf
  simp only [RuntimeValue.ArrayConforms, Array.size_singleton, Nat.lt_one_iff,
    forall_eq, singleton_get] at conf ⊢
  rcases conf with ⟨size, conf⟩
  refine ⟨size, ?_⟩
  cases hty : ts[0]! with
  | mk val verified =>
    cases val <;> simpa only [RuntimeValue.Conforms, hty, TypeAttr.of_def,
      Attribute.of_def, IsAttr.inject] using conf

set_option maxHeartbeats 1000000 in
theorem Riscv.interpretOpCTree_result_shape
    (code : Riscv) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (h : PureOrErr.CanInterpretTo
      (Riscv.interpretOpCTree (E := ErrorE ⊕ₑ UBE) code properties types operands successors before)
      (.ok (results, after, action))) :
    ∃ deterministic, Riscv.interpretOp' code properties types operands successors before =
      .ok (deterministic, after, action) ∧ RuntimeValue.ResultShapeRefines deterministic results := by
  unfold Riscv.interpretOpCTree at h
  split at h
  all_goals first
    | exact ⟨results, (liftedInterp_ok_iff _ _).mp h, fun _ ht => ht⟩
    | skip
  all_goals unfold riscvLoadCTree at h
  all_goals split at h
  all_goals simp [PureOrErr.CanInterpretTo.bind_iff, PureOrErr.CanInterpretTo.map_iff,
    Veir.fail, CTree.trigger_def, liftedInterp_ok_iff, Bind.bind] at h
  all_goals obtain ⟨loaded, hload, ⟨bits, hresults⟩, hmemory, haction⟩ := h
  all_goals first
    | obtain ⟨raw, hraw⟩ := loadByte_load_exists before _ 8 loaded hload
    | obtain ⟨raw, hraw⟩ := loadByte_load_exists before _ 4 loaded hload
    | obtain ⟨raw, hraw⟩ := loadByte_load_exists before _ 2 loaded hload
    | obtain ⟨raw, hraw⟩ := loadByte_load_exists before _ 1 loaded hload
  all_goals subst results; subst after; subst action
  all_goals simp_all only [Riscv.interpretOp', riscvLoad, Bind.bind, Pure.pure]
  all_goals exact ⟨_, rfl, register_result_shape _ _⟩

/-- Every successful nondeterministic primitive result has the type shape of a successful
legacy deterministic result on the same inputs, with identical memory and control flow. -/
theorem CTree.interpretOp'_result_shape
    (code : OpCode) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (regions : Array RegionPtr)
    (h : PureOrErr.CanInterpretTo
      (CTree.interpretOp' code properties types operands successors before regions)
      (.ok (results, after, action))) :
    ∃ deterministic, Veir.interpretOp' code properties types operands successors before =
      .ok (deterministic, after, action) ∧ RuntimeValue.ResultShapeRefines deterministic results := by
  cases code with
  | llvm code => exact Llvm.interpretOpCTree_result_shape _ _ _ _ _ _ _ _ _ h
  | gmir code => exact GMIR.interpretOpCTree_result_shape _ _ _ _ _ _ _ _ _ h
  | builtin code => exact Builtin.interpretOpCTree_result_shape _ _ _ _ _ _ _ _ _ h
  | riscv code => exact Riscv.interpretOpCTree_result_shape _ _ _ _ _ _ _ _ _ h
  | _ => exact ⟨results, (liftedInterp_ok_iff _ _).mp h, fun _ ht => ht⟩

/-- Verified CTree opcode returns conform, using the existing deterministic conformance theorem
and the proved nondeterministic payload correspondence. -/
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
  obtain ⟨deterministic, legacy, shape⟩ := CTree.interpretOp'_result_shape _ _ _ _ _ _ _ _ _ _ h
  exact shape _ (Veir.interpretOp'_results_conform verified conforms legacy)

end
end Veir
