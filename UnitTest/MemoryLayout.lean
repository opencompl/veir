import Veir.Interpreter.Memory

/-!
  Objects are laid out past every other object: the first lands right past
  the arena, and the next follows it with a guard byte, aligned.

  TODO: This is a simplification. Eventually, addresses should be
  non-deterministic.
-/

open Veir

/- Allocate, and return the new state with the object's address. -/
private def allocated (mem : MemoryState) (size : UInt64) : Option (MemoryState × UInt64) :=
  match mem.alloc size with
  | .ok (mem, p) => some (mem, mem.address p)
  | _ => none

#guard (allocated .empty 4).map (·.2) = some 0x10000
#guard ((allocated .empty 4).bind fun (m, _) => allocated m 4).map (·.2) = some 0x10010
