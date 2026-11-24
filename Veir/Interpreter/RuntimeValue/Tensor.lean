module

public import Veir.Interpreter.RuntimeValue.Basic

public section

namespace Veir

/--
  A tensor filled with `elemPoison`, sized for `shape`.
  This is the runtime meaning of `tensor.empty` when the element type has poison.
-/
@[expose]
def RuntimeValue.emptyTensor (shape : Array Nat) (elemPoison : RuntimeValue) : RuntimeValue :=
  .tensor shape (Array.replicate (shape.foldl Nat.mul 1) elemPoison)

end Veir
