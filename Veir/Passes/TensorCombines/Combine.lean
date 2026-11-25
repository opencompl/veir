module

public import Veir.PatternRewriter.Puddle.Builders
public import Veir.PatternRewriter.Puddle.Execution
public import Veir.GlobalOpInfo
public import Veir.Dialects.Tensor.Properties

/-! Nested `tensor.extract_slice` → one slice with composed offsets/strides. -/

public section

open Veir
open Veir.Puddle

namespace Veir.Passes.TensorCombines

/-- Fold nested extract_slice: offsets `o1 + o2·st1`, strides `st1·st2`, sizes from outer. -/
def nested_extract_slice_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := TensorType)
      let midTy ← MatchProg.type (Attr := TensorType)
      let resTy ← MatchProg.type (Attr := TensorType)
      let t ← MatchProg.value srcTy
      let mid ← MatchProg.operation (.tensor .extract_slice) #[t] #[midTy]
      let root ← MatchProg.root (.tensor .extract_slice) #[mid.res[0]!] #[resTy]
      return (t, resTy, mid.properties, root.properties))
    (fun (t, resTy, midProps, rootProps) => do
      let composed ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.tensor .extract_slice)))
          (midProps, rootProps)
          fun (inner, outer) => composeExtractSliceProperties inner outer
      CreateProg.operation (.tensor .extract_slice) #[t] #[resTy] (.inr composed))
    (fun op => op.res[0]!)

def nested_extract_slice : CompiledPattern OpCode :=
  nested_extract_slice_pattern.compile

end Veir.Passes.TensorCombines

end
