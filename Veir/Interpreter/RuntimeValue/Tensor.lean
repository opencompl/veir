module

public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Data.Tensor

/-!
# Runtime tensors

`RuntimeValue.tensor` is a static shape plus a flat row-major array.
`tensorExtractSlice` gathers from that array; equal to the functional-model round-trip.
-/

public section

namespace Veir

open Veir.Data.Tensor
  (composeSliceOffsets composeSliceStrides fitsSlice fitsSlice_compose
    flatExtractSlice flatExtractSlice_eq_toArray_slice numElements TensorFunctionalModel)

@[expose]
def RuntimeValue.emptyTensor (shape : Array Nat) (elemPoison : RuntimeValue) : RuntimeValue :=
  .tensor shape (Array.replicate (shape.foldl Nat.mul 1) elemPoison)

@[expose]
def RuntimeValue.toTensorFunctionalModel (shape : Array Nat) (elems : Array RuntimeValue) :
    TensorFunctionalModel RuntimeValue :=
  .ofArray shape.toList elems default

@[expose]
def RuntimeValue.ofTensorFunctionalModel (tensor : TensorFunctionalModel RuntimeValue) :
    RuntimeValue :=
  .tensor tensor.shape.toArray tensor.toArray

/--
  Flat gather under `fitsSlice`, `sizes = resultShape`, and a well-sized source.
  Equal to `ofTensorFunctionalModel (toTensorFunctionalModel … |>.slice …)`.
-/
@[expose]
def RuntimeValue.tensorExtractSlice (tensor : RuntimeValue)
    (offsets sizes strides : List Nat) (resultShape : Array Nat) :
    Option RuntimeValue :=
  match tensor with
  | .tensor shape elems =>
    if fitsSlice shape.toList offsets sizes strides = true ∧
        sizes = resultShape.toList ∧
        elems.size = numElements shape.toList then
      some (.tensor resultShape
        (flatExtractSlice shape.toList elems default offsets sizes strides))
    else none
  | _ => none

theorem RuntimeValue.tensorExtractSlice_eq_functional
    (shape : Array Nat) (elems : Array RuntimeValue)
    (offsets sizes strides : List Nat) (resultShape : Array Nat)
    (hfit : fitsSlice shape.toList offsets sizes strides = true)
    (hsizes : sizes = resultShape.toList)
    (hsize : elems.size = numElements shape.toList) :
    tensorExtractSlice (.tensor shape elems) offsets sizes strides resultShape =
      some (ofTensorFunctionalModel
        ((toTensorFunctionalModel shape elems).slice offsets sizes strides)) := by
  subst hsizes
  simp [tensorExtractSlice, hfit, hsize, ofTensorFunctionalModel, toTensorFunctionalModel,
    TensorFunctionalModel.slice_shape, flatExtractSlice_eq_toArray_slice,
    Array.toArray_toList]

theorem RuntimeValue.tensorExtractSlice_tensor_ok
    (shape : Array Nat) (elems : Array RuntimeValue)
    (offsets sizes strides : List Nat) (resultShape : Array Nat) (result : RuntimeValue)
    (h : tensorExtractSlice (.tensor shape elems) offsets sizes strides resultShape = some result) :
    fitsSlice shape.toList offsets sizes strides = true ∧
      sizes = resultShape.toList ∧
      elems.size = numElements shape.toList ∧
      result = ofTensorFunctionalModel
        ((toTensorFunctionalModel shape elems).slice offsets sizes strides) := by
  simp only [tensorExtractSlice] at h
  split at h
  · rename_i hcond
    obtain ⟨hfit, hs, hsize⟩ := hcond
    cases h
    refine ⟨hfit, hs, hsize, ?_⟩
    simp only [ofTensorFunctionalModel, toTensorFunctionalModel,
      TensorFunctionalModel.slice_shape, flatExtractSlice_eq_toArray_slice]
    subst hs
    simp [Array.toArray_toList]
  · cases h

/-- Nested runtime slices equal one slice with composed offsets and strides. -/
theorem RuntimeValue.tensorExtractSlice_compose
    (shape : Array Nat) (elems : Array RuntimeValue)
    (o1 s1 st1 o2 s2 st2 : List Nat)
    (midShape resultShape : Array Nat)
    (mid out : RuntimeValue)
    (hmid : tensorExtractSlice (.tensor shape elems) o1 s1 st1 midShape = some mid)
    (hout : tensorExtractSlice mid o2 s2 st2 resultShape = some out) :
    tensorExtractSlice (.tensor shape elems)
        (composeSliceOffsets o1 st1 o2) s2 (composeSliceStrides st1 st2) resultShape =
      some out := by
  obtain ⟨hfit1, hs1, hsize, hmidEq⟩ :=
    tensorExtractSlice_tensor_ok shape elems o1 s1 st1 midShape mid hmid
  subst hmidEq
  simp only [ofTensorFunctionalModel, TensorFunctionalModel.slice_shape] at hout
  obtain ⟨hfit2, hs2, _hsize2, houtEq⟩ :=
    tensorExtractSlice_tensor_ok s1.toArray
      ((toTensorFunctionalModel shape elems).slice o1 s1 st1).toArray
      o2 s2 st2 resultShape out (by simpa [toTensorFunctionalModel] using hout)
  have hfit := fitsSlice_compose (shape := shape.toList) hfit1 hfit2
  have hround :
      ((toTensorFunctionalModel s1.toArray
          ((toTensorFunctionalModel shape elems).slice o1 s1 st1).toArray).slice
          o2 s2 st2).toArray =
        (((toTensorFunctionalModel shape elems).slice o1 s1 st1).slice
          o2 s2 st2).toArray := by
    simpa [toTensorFunctionalModel, TensorFunctionalModel.slice_shape] using
      (TensorFunctionalModel.toArray_slice_ofArray_toArray
        ((toTensorFunctionalModel shape elems).slice o1 s1 st1)
        (default : RuntimeValue) o2 s2 st2 hfit2)
  have htab :
      (((toTensorFunctionalModel shape elems).slice o1 s1 st1).slice o2 s2 st2).toArray =
        ((toTensorFunctionalModel shape elems).slice
          (composeSliceOffsets o1 st1 o2) s2
          (composeSliceStrides st1 st2)).toArray :=
    TensorFunctionalModel.toArray_slice_slice _ o1 s1 st1 o2 s2 st2
  subst hs2
  rw [tensorExtractSlice_eq_functional shape elems
      (composeSliceOffsets o1 st1 o2) resultShape.toList
      (composeSliceStrides st1 st2) resultShape hfit rfl hsize, houtEq]
  refine congrArg some ?_
  simp only [ofTensorFunctionalModel, TensorFunctionalModel.slice_shape, toTensorFunctionalModel]
  exact congr (congrArg RuntimeValue.tensor rfl) (hround.trans htab).symm

end Veir
