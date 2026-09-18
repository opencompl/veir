import Veir.Interpreter.Memory

/-!
  The memory layout is the oracle's choice: an allocation lands at the
  address the oracle names for it, and past the end of memory otherwise.
-/

open Veir

/- Fresh memory holds eight poison bytes for the null address, so the first allocation lands at 8. -/
#guard (MemoryState.empty.alloc 4).2 = 8

/- With no address named, the second allocation follows the first. -/
#guard ((MemoryState.empty.alloc 4).1.alloc 4).2 = 12

/- An oracle that names an address for the first allocation is obeyed, and memory grows to fit. -/
def placeFirstAt100 : MemoryOracle := { blockAddress := fun n => if n = 0 then some 100 else none }

#guard ({ MemoryState.empty with oracle := placeFirstAt100 }.alloc 4).2 = 100
#guard ({ MemoryState.empty with oracle := placeFirstAt100 }.alloc 4).1.contents.size = 104

/- The next allocation, which the oracle leaves to the model, goes past the end. -/
#guard (({ MemoryState.empty with oracle := placeFirstAt100 }.alloc 4).1.alloc 4).2 = 104
