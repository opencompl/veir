module

public import Veir.Dialects.Tensor.OpInfo
public import Veir.Dialects.Tensor.Properties
public import Veir.Interpreter.RuntimeValue.Tensor
public import Veir.Interpreter.Basic
import all Veir.Dialects.Tensor.OpInfo
import all Veir.Dialects.Tensor.Properties
import all Veir.Data.Tensor
import all Veir.IR.Attribute
import all Veir.Interpreter.Interp
import all Veir.Interpreter.RuntimeValue.Tensor
import all Veir.Interpreter.Basic

/-! Characterisations of `Tensor.interpretOp' .extract_slice` for the nested-slice combine. -/

public section

namespace Veir

open Veir.Data.Tensor
  (composeSliceOffsets composeSliceStrides composeSliceOffsetInts composeSliceStrideInts
    fitsSlice fitsSlice_lengths staticIndices? staticIndices?_compose_offsets
    staticIndices?_compose_strides length_staticIndices? TensorFunctionalModel)

theorem interpretOp'_tensor_ok
    (op : Veir.Tensor) (props : propertiesOf (OpCode.tensor op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (vals : Array RuntimeValue) (act : Option ControlFlowAction)
    (h : Tensor.interpretOp' op props resultTypes operands blockOperands = .ok (vals, act)) :
    interpretOp' (OpCode.tensor op) props resultTypes operands blockOperands mem =
      .ok (vals, mem, act) := by
  simp only [interpretOp', h, Interp.bind_ok, Interp.pure_eq]

/-- Success iff operand/type/static indices decode and `tensorExtractSlice` succeeds. -/
theorem interpretOp'_extract_slice_ok_iff
    (props : ExtractSliceProperties) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (results : Array RuntimeValue) (act : Option ControlFlowAction) :
    Tensor.interpretOp' .extract_slice props resultTypes operands blockOperands
      = .ok (results, act) ↔
    ∃ (tensor : RuntimeValue) (resultType : TypeAttr) (resultTy : TensorType)
      (offsets sizes strides : List Nat) (result : RuntimeValue),
      operands[0]? = some tensor ∧
      resultTypes[0]? = some resultType ∧
      resultType.cast? TensorType = some resultTy ∧
      staticIndices? props.static_offsets.values.toList = some offsets ∧
      staticIndices? props.static_sizes.values.toList = some sizes ∧
      staticIndices? props.static_strides.values.toList = some strides ∧
      RuntimeValue.tensorExtractSlice tensor offsets sizes strides resultTy.shape = some result ∧
      results = #[result] ∧
      act = none := by
  constructor
  · intro h
    simp only [Tensor.interpretOp'] at h
    cases hsrc : operands[0]? with
    | none => simp [hsrc] at h
    | some tensor =>
      cases hty : resultTypes[0]? with
      | none => simp [hsrc, hty] at h
      | some resultType =>
        cases hcast : resultType.cast? TensorType with
        | none => simp [hsrc, hty, hcast] at h
        | some resultTy =>
          cases ho : staticIndices? props.static_offsets.values.toList with
          | none => simp [hsrc, hty, hcast, ho] at h
          | some offsets =>
            cases hs : staticIndices? props.static_sizes.values.toList with
            | none => simp [hsrc, hty, hcast, ho, hs] at h
            | some sizes =>
              cases hst : staticIndices? props.static_strides.values.toList with
              | none => simp [hsrc, hty, hcast, ho, hs, hst] at h
              | some strides =>
                simp only [hsrc, hty, hcast, ho, hs, hst] at h
                cases hsl : RuntimeValue.tensorExtractSlice tensor offsets sizes strides
                    resultTy.shape with
                | none => simp [hsl] at h
                | some result =>
                  simp only [hsl, Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  refine ⟨tensor, resultType, resultTy, offsets, sizes, strides, result,
                    ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
                  all_goals (first | rfl | assumption)
  · rintro ⟨tensor, resultType, resultTy, offsets, sizes, strides, result,
        hsrc, hty, hcast, ho, hs, hst, hsl, rfl, rfl⟩
    simp only [Tensor.interpretOp', hsrc, hty, hcast, ho, hs, hst, hsl, Interp.pure_eq]

theorem extract_slice_ok_singleton
    (props : ExtractSliceProperties) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (results : Array RuntimeValue) (act : Option ControlFlowAction)
    (h : Tensor.interpretOp' .extract_slice props resultTypes operands blockOperands
          = .ok (results, act)) :
    ∃ v, results = #[v] ∧ act = none := by
  obtain ⟨-, -, -, -, -, -, result, -, -, -, -, -, -, -, rfl, rfl⟩ :=
    (interpretOp'_extract_slice_ok_iff _ _ _ _ _ _).mp h
  exact ⟨result, rfl, rfl⟩

theorem extract_slice_ok_decode
    (props : ExtractSliceProperties) (resultTy : TensorType)
    (src result : RuntimeValue) (blockOperands : Array BlockPtr)
    (h : Tensor.interpretOp' .extract_slice props
        #[.of TensorType resultTy] #[src] blockOperands = .ok (#[result], none)) :
    ∃ offsets sizes strides,
      staticIndices? props.static_offsets.values.toList = some offsets ∧
      staticIndices? props.static_sizes.values.toList = some sizes ∧
      staticIndices? props.static_strides.values.toList = some strides ∧
      RuntimeValue.tensorExtractSlice src offsets sizes strides resultTy.shape = some result := by
  obtain ⟨tensor, resultType, resultTy', offsets, sizes, strides, result',
      hsrc, hty, hcast, ho, hs, hst, hsl, hres, -⟩ :=
    (interpretOp'_extract_slice_ok_iff _ _ _ _ _ _).mp h
  have hsrc' : tensor = src := by cases hsrc; rfl
  subst hsrc'
  have hty' : resultType = .of TensorType resultTy := by cases hty; rfl
  subst hty'
  have hcast' : resultTy' = resultTy := by
    have := IsTypeAttr.cast?_of (Attr := TensorType) resultTy
    simp only [this, Option.some.injEq] at hcast
    exact hcast.symm
  subst hcast'
  have hres' : result' = result := by cases hres; rfl
  subst hres'
  exact ⟨offsets, sizes, strides, ho, hs, hst, hsl⟩

private theorem denseArray_size_eq_of_staticIndices?
    {arr : DenseArrayAttr} {xs : List Nat}
    (h : staticIndices? arr.values.toList = some xs) :
    arr.values.size = xs.length := by
  simpa [Array.length_toList] using (length_staticIndices? h).symm

/-- Nested success forces matching ranks, so property composition is defined. -/
theorem composeExtractSliceProperties_isSome_of_ok
    (innerProps outerProps : ExtractSliceProperties)
    (srcTy midTy resTy : TensorType)
    (src mid out : RuntimeValue)
    (blockOperands : Array BlockPtr)
    (hsrcConf : src.Conforms (.of TensorType srcTy))
    (hinner : Tensor.interpretOp' .extract_slice innerProps
        #[.of TensorType midTy] #[src] blockOperands = .ok (#[mid], none))
    (houter : Tensor.interpretOp' .extract_slice outerProps
        #[.of TensorType resTy] #[mid] blockOperands = .ok (#[out], none)) :
    (composeExtractSliceProperties innerProps outerProps).isSome := by
  obtain ⟨srcElems, rfl, _, _⟩ := (RuntimeValue.Conforms.tensorType
    (runtimeValue := src) (tensorType := srcTy)).mp hsrcConf
  obtain ⟨o1, s1, st1, ho1, hs1, hst1, hmidSlice⟩ :=
    extract_slice_ok_decode innerProps midTy _ mid blockOperands hinner
  obtain ⟨hfit1, -, -, hmidEq⟩ :=
    RuntimeValue.tensorExtractSlice_tensor_ok _ _ _ _ _ _ _ hmidSlice
  obtain ⟨hlen_o1, hlen_s1, hlen_st1⟩ := fitsSlice_lengths hfit1
  subst hmidEq
  simp only [RuntimeValue.ofTensorFunctionalModel, TensorFunctionalModel.slice_shape] at houter
  obtain ⟨o2, s2, st2, ho2, hs2, hst2, houtSlice⟩ :=
    extract_slice_ok_decode outerProps resTy _ out blockOperands houter
  have hfit2 : fitsSlice s1 o2 s2 st2 = true :=
    (RuntimeValue.tensorExtractSlice_tensor_ok
      (shape := s1.toArray)
      (elems := ((RuntimeValue.toTensorFunctionalModel srcTy.shape srcElems).slice
        o1 s1 st1).toArray)
      o2 s2 st2 resTy.shape out (by simpa using houtSlice)).1
  obtain ⟨hlen_o2, -, hlen_st2⟩ := fitsSlice_lengths hfit2
  have h_off :
      innerProps.static_offsets.values.size = outerProps.static_offsets.values.size := by
    calc
      innerProps.static_offsets.values.size = o1.length :=
        denseArray_size_eq_of_staticIndices? ho1
      _ = srcTy.shape.toList.length := hlen_o1
      _ = s1.length := hlen_s1.symm
      _ = s1.toArray.toList.length := by simp
      _ = o2.length := hlen_o2.symm
      _ = outerProps.static_offsets.values.size :=
        (denseArray_size_eq_of_staticIndices? ho2).symm
  have h_off_st1 :
      innerProps.static_offsets.values.size = innerProps.static_strides.values.size := by
    calc
      innerProps.static_offsets.values.size = o1.length :=
        denseArray_size_eq_of_staticIndices? ho1
      _ = srcTy.shape.toList.length := hlen_o1
      _ = st1.length := hlen_st1.symm
      _ = innerProps.static_strides.values.size :=
        (denseArray_size_eq_of_staticIndices? hst1).symm
  have h_st :
      innerProps.static_strides.values.size = outerProps.static_strides.values.size := by
    calc
      innerProps.static_strides.values.size = st1.length :=
        denseArray_size_eq_of_staticIndices? hst1
      _ = srcTy.shape.toList.length := hlen_st1
      _ = s1.length := hlen_s1.symm
      _ = s1.toArray.toList.length := by simp
      _ = st2.length := hlen_st2.symm
      _ = outerProps.static_strides.values.size :=
        (denseArray_size_eq_of_staticIndices? hst2).symm
  have h_off_st2 :
      outerProps.static_offsets.values.size = outerProps.static_strides.values.size :=
    h_off.symm.trans (h_off_st1.trans h_st)
  simp [composeExtractSliceProperties, h_off, h_st, h_off_st2]

/-- Nested success equals one composed `extract_slice` under `composeExtractSliceProperties`. -/
theorem extract_slice_compose_of_ok
    (innerProps outerProps composedProps : ExtractSliceProperties)
    (srcTy midTy resTy : TensorType)
    (src mid out : RuntimeValue)
    (blockOperands : Array BlockPtr)
    (hcompose : composeExtractSliceProperties innerProps outerProps = some composedProps)
    (hsrcConf : src.Conforms (.of TensorType srcTy))
    (hinner : Tensor.interpretOp' .extract_slice innerProps
        #[.of TensorType midTy] #[src] blockOperands = .ok (#[mid], none))
    (houter : Tensor.interpretOp' .extract_slice outerProps
        #[.of TensorType resTy] #[mid] blockOperands = .ok (#[out], none)) :
    Tensor.interpretOp' .extract_slice composedProps
        #[.of TensorType resTy] #[src] blockOperands = .ok (#[out], none) := by
  obtain ⟨srcElems, rfl, _, _⟩ := (RuntimeValue.Conforms.tensorType
    (runtimeValue := src) (tensorType := srcTy)).mp hsrcConf
  obtain ⟨o1, s1, st1, ho1, hs1, hst1, hmidSlice⟩ :=
    extract_slice_ok_decode innerProps midTy _ mid blockOperands hinner
  obtain ⟨o2, s2, st2, ho2, hs2, hst2, houtSlice⟩ :=
    extract_slice_ok_decode outerProps resTy _ out blockOperands houter
  simp only [composeExtractSliceProperties] at hcompose
  split at hcompose
  · rename_i hlen
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlen
    obtain ⟨⟨hlen_o_st, hlen_o_o⟩, hlen_st⟩ := hlen
    cases hcompose
    have hlenOff :
        innerProps.static_offsets.values.toList.length =
          innerProps.static_strides.values.toList.length := by
      simpa [Array.length_toList] using hlen_o_st
    have hlenOff2 :
        innerProps.static_offsets.values.toList.length =
          outerProps.static_offsets.values.toList.length := by
      simpa [Array.length_toList] using hlen_o_o
    have hlenStr :
        innerProps.static_strides.values.toList.length =
          outerProps.static_strides.values.toList.length := by
      simpa [Array.length_toList] using hlen_st
    have hoC := staticIndices?_compose_offsets ho1 hst1 ho2 hlenOff hlenOff2
    have hstC := staticIndices?_compose_strides hst1 hst2 hlenStr
    have hcomposed :=
      RuntimeValue.tensorExtractSlice_compose srcTy.shape srcElems
        o1 s1 st1 o2 s2 st2 midTy.shape resTy.shape mid out hmidSlice houtSlice
    refine (interpretOp'_extract_slice_ok_iff _ _ _ _ _ _).mpr ?_
    refine ⟨.tensor srcTy.shape srcElems, .of TensorType resTy, resTy,
      composeSliceOffsets o1 st1 o2, s2, composeSliceStrides st1 st2, out,
      rfl, rfl, IsTypeAttr.cast?_of (Attr := TensorType) resTy, ?_, hs2, ?_, hcomposed, rfl, rfl⟩
    · simpa using hoC
    · simpa using hstC
  · cases hcompose

end Veir

end
