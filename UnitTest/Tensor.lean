import Veir.Data.Tensor

open Veir.Data

/-! ## Indices are in row-major order -/

#guard Tensor.indices [2, 3] = [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2]]

#guard Tensor.indices [] = [[]]

#guard Tensor.indices [2, 0, 3] = []

/-! ## Reading and writing elements -/

/-- The `2x3` tensor whose element at `[i, j]` is `10 * i + j`. -/
def t : Tensor Nat := ⟨[2, 3], fun | [i, j] => 10 * i + j | _ => 0⟩

#guard t.toList = [0, 1, 2, 10, 11, 12]

#guard (t.set [1, 0] 7).toList = [0, 1, 2, 7, 11, 12]

#guard (t.set [2, 0] 7).toList = t.toList
