import Veir.Interpreter.Memory

/-!
  The memory layout is the oracle's choice: an allocation lands at the
  address the oracle names for it, and where the model would place it
  otherwise. An address the object cannot be placed at fails the run.
-/

open Veir

/- Allocate, and return the new state with the object's address. -/
def allocated (mem : MemoryState) (size : Nat) : Option (MemoryState × UInt64) :=
  match mem.alloc size with
  | .ok (mem, p) => some (mem, mem.address p)
  | _ => none

/- With no address named, the first object lands right past the arena, and the next follows it with a guard byte, aligned. -/
#guard (allocated .empty 4).map (·.2) = some 0x10000
#guard ((allocated .empty 4).bind fun (m, _) => allocated m 4).map (·.2) = some 0x10010

/- An oracle that names a valid address for the first allocation is obeyed, and the next allocation goes past it. -/
def placeFirst : MemoryOracle := { blockAddress := fun n => if n = 0 then some 0x20000 else none }

#guard (allocated { MemoryState.empty with oracle := placeFirst } 4).map (·.2) = some 0x20000
#guard ((allocated { MemoryState.empty with oracle := placeFirst } 4).bind fun (m, _) => allocated m 4).map (·.2)
  = some 0x20010

/- An address inside the arena, an unaligned one, and one overlapping an object all fail. -/
#guard (allocated { MemoryState.empty with oracle := { blockAddress := fun _ => some 100 } } 4).isNone
#guard (allocated { MemoryState.empty with oracle := { blockAddress := fun _ => some 0x20001 } } 4).isNone
#guard ((allocated .empty 4).bind fun (m, _) =>
  allocated { m with oracle := { blockAddress := fun _ => some 0x10000 } } 4).isNone
