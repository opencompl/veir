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

  Where Cerberus threads nondeterminism through its `memM`, the interpreter,
  being a function, draws every such choice from a `MemoryOracle` that the
  initial state is built from.

  Operations join the signature with the features that need them, so that at
  every point it lists exactly what the model provides.
-/

namespace Veir

public section

open Veir.Data.LLVM (Pointer Ptr)

/--
  The choices the interpreter makes where the memory model is nondeterministic.
  The interpreter is a function, so every such choice is drawn from the
  oracle, indexed by how many choices of that kind were made before, and two
  programs being compared are run against the same oracle.
-/
structure MemoryOracle where
  /-- The address of the `n`-th allocation, or `none` to let the model place it. -/
  blockAddress : Nat → Option UInt64 := fun _ => none

instance : Inhabited MemoryOracle := ⟨{}⟩

class MemoryModel (State : Type) where
  /-- `name` -/
  name : String
  /-- `initial_mem_state`, built from the oracle the model's choices are drawn from. -/
  initialMemState : MemoryOracle → State
  /--
    `allocate_region`: a fresh object of `size` bytes aligned to `align`, and a
    pointer to its start. Fails when the oracle names an address the object
    cannot be placed at.
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
  /-- `memcpy`: copy `n` bytes from `src` to `dst`, as they are. Undefined behaviour if either access is not valid. -/
  memcpy : State → (dst src : Pointer) → (n : Nat) → Interp State
  /-- `kill`: end the lifetime of the object `p` points to. -/
  kill : State → Pointer → Interp State
  /-- `realloc`: a fresh object of `size` bytes holding the old object's bytes, the old one killed. -/
  realloc : State → (align size : Nat) → Pointer → Interp (State × Pointer)

end

end Veir
