module

public import Veir.IR.Attribute
public import Veir.Data.Tensor
public import Std.Data.HashMap

namespace Veir

public section

open Veir.Data.Tensor (composeSliceOffsetInts composeSliceStrideInts)

/-- Static offsets/sizes/strides plus `operandSegmentSizes` (source, offs, sizes, strides; last three 0 here). -/
structure ExtractSliceProperties where
  static_offsets : DenseArrayAttr
  static_sizes : DenseArrayAttr
  static_strides : DenseArrayAttr
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

/-- Offsets `inner + outer·innerStride`, strides `innerStride·outerStride`; sizes from outer. -/
def composeExtractSliceProperties (inner outer : ExtractSliceProperties) :
    Option ExtractSliceProperties :=
  let o1 := inner.static_offsets.values
  let st1 := inner.static_strides.values
  let o2 := outer.static_offsets.values
  let st2 := outer.static_strides.values
  if o1.size = st1.size && o1.size = o2.size && st1.size = st2.size then
    some {
      static_offsets := {
        elementType := outer.static_offsets.elementType
        values := (composeSliceOffsetInts o1.toList st1.toList o2.toList).toArray
      }
      static_sizes := outer.static_sizes
      static_strides := {
        elementType := outer.static_strides.elementType
        values := (composeSliceStrideInts st1.toList st2.toList).toArray
      }
      operandSegmentSizes := outer.operandSegmentSizes
    }
  else
    none

private def requireDenseArray (attrDict : Std.HashMap ByteArray Attribute)
    (key : String) : Except String DenseArrayAttr := do
  match attrDict[key.toUTF8]? with
  | some (.denseArrayAttr arr) => .ok arr
  | some attr =>
    .error s!"tensor.extract_slice: expected '{key}' to be a dense array attribute, but got {attr}"
  | none => .error s!"tensor.extract_slice: missing '{key}' property"

def ExtractSliceProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ExtractSliceProperties := do
  let static_offsets ← requireDenseArray attrDict "static_offsets"
  let static_sizes ← requireDenseArray attrDict "static_sizes"
  let static_strides ← requireDenseArray attrDict "static_strides"
  let operandSegmentSizes ← requireDenseArray attrDict "operandSegmentSizes"
  return { static_offsets, static_sizes, static_strides, operandSegmentSizes }

def ExtractSliceProperties.toAttrDict (props : ExtractSliceProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 4
  dict := dict.insert "static_offsets".toUTF8 (.denseArrayAttr props.static_offsets)
  dict := dict.insert "static_sizes".toUTF8 (.denseArrayAttr props.static_sizes)
  dict := dict.insert "static_strides".toUTF8 (.denseArrayAttr props.static_strides)
  dict := dict.insert "operandSegmentSizes".toUTF8 (.denseArrayAttr props.operandSegmentSizes)
  dict

end

end Veir
