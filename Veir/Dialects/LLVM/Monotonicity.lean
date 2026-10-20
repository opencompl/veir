module

public import Veir.Interpreter.Lemmas

public section

/-!
# Monotonicity of the LLVM interpreter

An LLVM opcode is monotone in its operands when refining its operands refines its result.
-/

namespace Veir

/-!
No LLVM opcode has an instance yet. `load` reads memory, so its proof needs that loading
from a refined memory yields refined bytes, which is a lemma about `MemoryState.load`.
-/

end Veir

end
