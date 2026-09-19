module

public import Veir.RuntimeValue
public import Veir.Interpreter.Interp

/-!
  # The memory model signature

  The operations a memory model provides to the interpreter, after the
  `Memory` module type of Cerberus (`ocaml_frontend/memory_model.ml`), whose
  names each operation keeps in Lean spelling. What Cerberus types with a
  `Ctype` is typed here with a `TypeAttr`, its `memM` is `Interp`, and its
  unspecified values are poison.

  Operations join the signature with the features that need them, so that at
  every point it lists exactly what the model provides.
-/

namespace Veir

public section

open Veir.Data (Pointer)
open Veir.Data.LLVM (Ptr)

class MemoryModel (State : Type) where
  /-- `name` -/
  name : String
  /-- `initial_mem_state` -/
  initialMemState : State
  /--
    `allocate_region`: a fresh object of `size` bytes aligned to `align`, and a
    pointer to its start. Fails when the object does not fit in the address
    space.
  -/
  allocateRegion : State → (align size : Nat) → Interp (State × Pointer)
  /-- `load`: the value of `type` stored at `p`. Undefined behaviour if the access is not valid. -/
  load : State → TypeAttr → Pointer → Interp RuntimeValue
  /-- `store`: `val` at `p`. Undefined behaviour if the access is not valid. -/
  store : State → Pointer → RuntimeValue → Interp State
  /-- `validForDeref_ptrval`: whether `size` bytes at `p` may be accessed. -/
  validForDerefPtrval : State → Pointer → (size : Nat) → Bool
  /-- `array_shift_ptrval`: the pointer `bytes` bytes past `p`, wrapping at 64 bits. -/
  arrayShiftPtrval : Pointer → (bytes : Nat) → Pointer
  /-- `ptrfromint`: the pointer an integer denotes; poison for poison. -/
  ptrFromInt : State → Data.LLVM.Int 64 → Ptr
  /-- `intfromptr`: the integer a pointer denotes; poison for poison. -/
  intFromPtr : State → Ptr → Data.LLVM.Int 64

end

end Veir
