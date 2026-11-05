import Veir.Dialects.Linalg.Model
import Veir.Dialects.Linalg.Properties

open Veir
open Veir.Data
open Veir.Linalg.Model

/-- The tensor of the given shape with the elements `elems` in row-major order. -/
def ofList (shape : List Nat) (elems : List Int) : Tensor Int where
  shape := shape
  get idx := (((Tensor.indices shape).idxOf? idx).bind (elems[·]?)).getD 0

/-- The elements of every output of `generic`, in row-major order. -/
def run (maps : Array AffineMapAttr) (numInputs : Nat) (bounds : List Nat)
    (body : List Nat → Array Int → Array Int) (operands : Array (Tensor Int)) : List (List Int) :=
  (generic maps numInputs bounds body operands).toList.map Tensor.toList

/-! ## Transpose: `out[d0, d1] = in[d1, d0]` -/

#guard run #[⟨2, #[.dim 1, .dim 0]⟩, ⟨2, #[.dim 0, .dim 1]⟩] 1 [3, 2]
    (fun _ args => #[args[0]!])
    #[ofList [2, 3] [0, 1, 2, 3, 4, 5], ofList [3, 2] [0, 0, 0, 0, 0, 0]] =
  [[0, 3, 1, 4, 2, 5]]

/-! ## Matmul: `out[d0, d1] += a[d0, d2] * b[d2, d1]`, reducing over `d2` -/

/-- The properties of a matmul of a `2x3` and a `3x2` matrix. -/
def matmul : LinalgGenericProperties where
  indexingMaps := #[⟨3, #[.dim 0, .dim 2]⟩, ⟨3, #[.dim 2, .dim 1]⟩, ⟨3, #[.dim 0, .dim 1]⟩]
  iteratorTypes := #[.parallel, .parallel, .reduction]
  numInputs := 2
  numOutputs := 1

/-- The operand shapes of `matmul`. -/
def matmulShapes : Array (Array Nat) := #[#[2, 3], #[3, 2], #[2, 2]]

#guard matmul.verifyIndexingMaps matmulShapes |>.isOk

#guard matmul.loopBounds matmulShapes = some [2, 2, 3]

-- A loop that appears in no indexing map has no bound, and the verifier rejects it.
#guard { matmul with iteratorTypes := matmul.iteratorTypes.push .parallel }.loopBounds
    matmulShapes = none

#guard run matmul.indexingMaps matmul.numInputs (matmul.loopBounds matmulShapes |>.get!)
    (fun _ args => #[args[0]! * args[1]! + args[2]!])
    #[ofList [2, 3] [1, 2, 3, 4, 5, 6], ofList [3, 2] [7, 8, 9, 10, 11, 12],
      ofList [2, 2] [0, 0, 0, 0]] =
  [[58, 64, 139, 154]]

/-! ## Broadcasting a scalar: `out[d0] = s` -/

#guard run #[⟨1, #[]⟩, ⟨1, #[.dim 0]⟩] 1 [3] (fun _ args => #[args[0]!])
    #[ofList [] [7], ofList [3] [0, 0, 0]] =
  [[7, 7, 7]]

/-! ## A constant index: `out[d0] = in[d0, 1]` -/

#guard run #[⟨1, #[.dim 0, .const 1]⟩, ⟨1, #[.dim 0]⟩] 1 [2] (fun _ args => #[args[0]!])
    #[ofList [2, 3] [0, 1, 2, 3, 4, 5], ofList [2] [0, 0]] =
  [[1, 4]]

/-! ## Several outputs: `out0[d0] = in[d0] + 1`, `out1[d0] = in[d0] * 2` -/

#guard run #[⟨1, #[.dim 0]⟩, ⟨1, #[.dim 0]⟩, ⟨1, #[.dim 0]⟩] 1 [3]
    (fun _ args => #[args[0]! + 1, args[0]! * 2])
    #[ofList [3] [1, 2, 3], ofList [3] [0, 0, 0], ofList [3] [0, 0, 0]] =
  [[2, 3, 4], [2, 4, 6]]

/-! ## An order-sensitive reduction with an init: `out[] = out[] * 10 + in[d0]` -/

#guard run #[⟨1, #[.dim 0]⟩, ⟨1, #[]⟩] 1 [3] (fun _ args => #[args[1]! * 10 + args[0]!])
    #[ofList [3] [1, 2, 3], ofList [] [5]] =
  [[5123]]

/-!
  ## Two inputs and two outputs with different maps

  `out0[d0, d1] = a[d0, d1] - b[d1, d0]` and `out1[d1, d0] = a[d0, d1]`.
-/

#guard run #[⟨2, #[.dim 0, .dim 1]⟩, ⟨2, #[.dim 1, .dim 0]⟩, ⟨2, #[.dim 0, .dim 1]⟩,
      ⟨2, #[.dim 1, .dim 0]⟩] 2 [2, 3]
    (fun _ args => #[args[0]! - args[1]!, args[0]!])
    #[ofList [2, 3] [0, 1, 2, 3, 4, 5], ofList [3, 2] [10, 20, 30, 40, 50, 60],
      ofList [2, 3] [0, 0, 0, 0, 0, 0], ofList [3, 2] [0, 0, 0, 0, 0, 0]] =
  [[-10, -29, -48, -17, -36, -55], [0, 3, 1, 4, 2, 5]]

/-! ## Reading the loop index, as `linalg.index` does: `out[d0, d1] = d0 == d1` -/

#guard run #[⟨2, #[.dim 0, .dim 1]⟩] 0 [2, 2]
    (fun idx _ => #[if idx[0]! = idx[1]! then 1 else 0])
    #[ofList [2, 2] [7, 7, 7, 7]] =
  [[1, 0, 0, 1]]

/-! ## A body that can fail: dividing by every element of the input -/

/-- `out[d0] = 12 / in[d0]`, failing on a division by zero. -/
def divide (input : List Int) : Option (List (List Int)) :=
  (genericM (m := Option) (α := Int) #[⟨1, #[.dim 0]⟩, ⟨1, #[.dim 0]⟩] 1 [3]
    (fun _ args => if args[0]! = 0 then none else some #[12 / args[0]!])
    #[ofList [3] input, ofList [3] [0, 0, 0]]).map (·.toList.map Tensor.toList)

#guard divide [1, 2, 3] = some [[12, 6, 4]]

#guard divide [1, 0, 3] = none

/-! ## Accesses within bounds -/

#guard AccessesInBounds matmul.indexingMaps (matmul.loopBounds matmulShapes |>.get!)
  (matmulShapes.map (·.toList))

-- A negative constant is out of bounds, rather than reading index 0.
#guard ¬AccessesInBounds #[⟨1, #[.dim 0, .const (-1)]⟩] [2] #[[2, 3]]

-- The verifier does not check dimensions of size 0, so a loop of size 3 taken from the
-- first operand may access the second operand of shape `[0]`.
def copy : LinalgGenericProperties where
  indexingMaps := #[⟨1, #[.dim 0]⟩, ⟨1, #[.dim 0]⟩]
  iteratorTypes := #[.parallel]
  numInputs := 1
  numOutputs := 1

#guard copy.verifyIndexingMaps #[#[3], #[0]] |>.isOk

#guard ¬AccessesInBounds #[⟨1, #[.dim 0]⟩, ⟨1, #[.dim 0]⟩] [3] #[[3], [0]]
