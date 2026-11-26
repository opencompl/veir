module

public import Veir.Interpreter.RuntimeValue.Basic

public section

namespace Veir

/--
  A tensor filled with `elemPoison`, sized for `ty`.
  This is the runtime meaning of `tensor.empty` when the element type has poison.
-/
@[expose]
def RuntimeValue.emptyTensor (ty : TensorType) (elemPoison : RuntimeValue) : RuntimeValue :=
  .tensor ty.shape (Array.replicate ty.numElements elemPoison)

end Veir
