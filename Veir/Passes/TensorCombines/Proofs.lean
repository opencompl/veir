module

import all Veir.Passes.TensorCombines.Combine
import all Veir.Dialects.Tensor.OpInfo
import all Veir.Dialects.Tensor.Properties
import all Veir.Dialects.Tensor.InterpreterLemmas
import all Veir.GlobalOpInfo
import all Veir.Interpreter.RuntimeValue.Tensor
import all Veir.Interpreter.RuntimeValue.Conforms
import all Veir.Interpreter.Refinement.Lemmas
import all Veir.Interpreter.Interp
import all Veir.Interpreter.Basic
import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTree
import all Veir.Data.Tensor

namespace Veir.Passes.TensorCombines

open Puddle
open PureOrErr.CanInterpretTo (monadLift_interp_ok_iff)

private abbrev refineResult :
    (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
    (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Prop :=
  fun target source => OperationResult.isRefinedBy source target

private theorem ctree_interpretOp'_tensor
    (op : Veir.Tensor) (props : propertiesOf (OpCode.tensor op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (mem : MemoryState) :
    CTree.interpretOp' (OpCode.tensor op) props resultTypes operands blockOperands mem =
      monadLift (interpretOp' (OpCode.tensor op) props resultTypes operands blockOperands mem) :=
  rfl

private theorem canInterpretTo_extract_slice_ok
    (props : ExtractSliceProperties) (midTy : TensorType) (src mid : RuntimeValue)
    (mem₀ mem₁ : MemoryState)
    (h : PureOrErr.CanInterpretTo
        (CTree.interpretOp' (OpCode.tensor .extract_slice) props
          #[.of TensorType midTy] #[src] #[] mem₀)
        (.ok (#[mid], mem₁, none))) :
    Tensor.interpretOp' .extract_slice props
      #[.of TensorType midTy] #[src] #[] = .ok (#[mid], none) := by
  rw [ctree_interpretOp'_tensor, monadLift_interp_ok_iff] at h
  cases hT : Tensor.interpretOp' .extract_slice props
      #[.of TensorType midTy] #[src] #[] with
  | fail _ =>
    simp only [interpretOp', hT, Interp.bind_fail] at h
    cases h
  | ub _ =>
    simp only [interpretOp', hT, Interp.bind_ub] at h
    cases h
  | ok pair =>
    obtain ⟨results, act⟩ := pair
    have hok := interpretOp'_tensor_ok (op := .extract_slice) props
      #[.of TensorType midTy] #[src] #[] mem₀ results act hT
    simp only [hok, Interp.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    rfl

private theorem exists_extract_slice_outer_ok
    (outerProps : ExtractSliceProperties) (resTy : TensorType) (mid : RuntimeValue)
    (memory : MemoryState) (v : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (h : interpretOp' (OpCode.tensor .extract_slice) outerProps
        #[.of TensorType resTy] #[mid] #[] memory = .ok v) :
    ∃ out,
      v = (#[out], memory, none) ∧
      Tensor.interpretOp' .extract_slice outerProps
        #[.of TensorType resTy] #[mid] #[] = .ok (#[out], none) := by
  simp only [interpretOp'] at h
  cases hTout : Tensor.interpretOp' .extract_slice outerProps
      #[.of TensorType resTy] #[mid] #[] with
  | fail _ => simp [hTout] at h
  | ub _ => simp [hTout] at h
  | ok pair =>
    obtain ⟨results, act⟩ := pair
    obtain ⟨out, hr, ha⟩ := extract_slice_ok_singleton _ _ _ _ _ _ hTout
    refine ⟨out, ?_, by simp [hr, ha]⟩
    simp only [hTout, Interp.bind_ok, Interp.pure_eq, Interp.ok.injEq] at h
    rw [← h, hr, ha]

private theorem nested_extract_slice_sim_compose_none
    (innerProps outerProps : ExtractSliceProperties)
    (srcTy midTy resTy : TensorType) (src mid : RuntimeValue) (memory : MemoryState)
    (hcompose : composeExtractSliceProperties innerProps outerProps = none)
    (hsrcConf : src.Conforms (.of TensorType srcTy))
    (hinnerOk : Tensor.interpretOp' .extract_slice innerProps
        #[.of TensorType midTy] #[src] #[] = .ok (#[mid], none)) :
    CTree.Sim refineResult
      (fail : FunctionTree _)
      (CTree.interpretOp' (OpCode.tensor .extract_slice) outerProps
        #[.of TensorType resTy] #[mid] #[] memory) := by
  rw [ctree_interpretOp'_tensor, Sim.monadLift_right_iff]
  cases hRoot : interpretOp' (OpCode.tensor .extract_slice) outerProps
      #[.of TensorType resTy] #[mid] #[] memory with
  | fail _ => exact sim_fail _ _
  | ub _ => exact sim_ub _ _
  | ok v =>
    obtain ⟨out, -, hTout⟩ :=
      exists_extract_slice_outer_ok outerProps resTy mid memory v hRoot
    have his := composeExtractSliceProperties_isSome_of_ok innerProps outerProps
      srcTy midTy resTy src mid out #[] hsrcConf hinnerOk hTout
    simp [hcompose] at his

private theorem nested_extract_slice_sim_compose_some
    (innerProps outerProps composedProps : ExtractSliceProperties)
    (srcTy midTy resTy : TensorType) (src mid : RuntimeValue) (memory : MemoryState)
    (hcompose : composeExtractSliceProperties innerProps outerProps = some composedProps)
    (hsrcConf : src.Conforms (.of TensorType srcTy))
    (hinnerOk : Tensor.interpretOp' .extract_slice innerProps
        #[.of TensorType midTy] #[src] #[] = .ok (#[mid], none)) :
    CTree.Sim refineResult
      (CTree.bind
        (CTree.interpretOp' (OpCode.tensor .extract_slice) composedProps
          #[.of TensorType resTy] #[src] #[] memory)
        fun result => pure (#[result.1[0]!], result.2.1, none))
      (CTree.interpretOp' (OpCode.tensor .extract_slice) outerProps
        #[.of TensorType resTy] #[mid] #[] memory) := by
  rw [ctree_interpretOp'_tensor (op := .extract_slice) (props := composedProps),
    Sim.bind_monadLift_left_iff,
    ctree_interpretOp'_tensor (op := .extract_slice) (props := outerProps),
    Sim.monadLift_right_iff]
  cases hRoot : interpretOp' (OpCode.tensor .extract_slice) outerProps
      #[.of TensorType resTy] #[mid] #[] memory with
  | fail _ =>
    cases interpretOp' (OpCode.tensor .extract_slice) composedProps
        #[.of TensorType resTy] #[src] #[] memory with
    | fail _ => exact sim_fail _ _
    | ub _ => exact sim_fail _ _
    | ok _ => exact sim_fail _ _
  | ub _ =>
    cases interpretOp' (OpCode.tensor .extract_slice) composedProps
        #[.of TensorType resTy] #[src] #[] memory with
    | fail _ => exact sim_ub _ _
    | ub _ => exact sim_ub _ _
    | ok _ => exact sim_ub _ _
  | ok v =>
    obtain ⟨out, hv, hTout⟩ :=
      exists_extract_slice_outer_ok outerProps resTy mid memory v hRoot
    cases hv
    have hcomposed :=
      extract_slice_compose_of_ok innerProps outerProps composedProps
        srcTy midTy resTy src mid out #[] hcompose hsrcConf hinnerOk hTout
    have hCreate := interpretOp'_tensor_ok (op := .extract_slice) composedProps
      #[.of TensorType resTy] #[src] #[] memory #[out] none hcomposed
    simp only [hCreate, monadLift, MonadLift.monadLift]
    simp [CTree.Sim.pure, refineResult, OperationResult.isRefinedBy_refl]

theorem nested_extract_slice_pattern_ctree_valid :
    Puddle.CTree.Pattern.Valid nested_extract_slice_pattern := by
  simp only [nested_extract_slice_pattern]
  simpPuddleValid
  intro srcTy midTy resTy src hsrcConf
  intro innerProps _hverifInner mid hCanInner
  intro outerProps _hverifOuter memory
  obtain ⟨mem₀, mem₁, hCan⟩ := hCanInner
  have hinnerOk := canInterpretTo_extract_slice_ok innerProps midTy src mid mem₀ mem₁ hCan
  cases hcompose : composeExtractSliceProperties innerProps outerProps with
  | none =>
    exact nested_extract_slice_sim_compose_none innerProps outerProps
      srcTy midTy resTy src mid memory hcompose hsrcConf hinnerOk
  | some composedProps =>
    simp only
    exact nested_extract_slice_sim_compose_some innerProps outerProps composedProps
      srcTy midTy resTy src mid memory hcompose hsrcConf hinnerOk

end Veir.Passes.TensorCombines
