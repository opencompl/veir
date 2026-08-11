module

/-!
  # Memory effects

  This corresponds roughly to MLIR's `MemoryEffectOpInterface`:
  https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/SideEffectInterfaces.h
-/

namespace Veir

public section

/--
  The memory effects an operation may have.
-/
structure MemoryEffects where
  /-- The operation may dereference memory, without necessarily mutating it. -/
  reads : Bool
  /-- The operation may mutate memory, without necessarily dereferencing it. -/
  writes : Bool
deriving Inhabited, Repr, DecidableEq

namespace MemoryEffects

def none : MemoryEffects := { reads := false, writes := false }

def read : MemoryEffects := { reads := true, writes := false }

def write : MemoryEffects := { reads := false, writes := true }

def readWrite : MemoryEffects := { reads := true, writes := true }

end MemoryEffects

/--
  Is this operation free of memory effects? Mirrors `mlir::isMemoryEffectFree`.

  NOTE: as upstream, this says nothing about whether the operation is safe to
  speculate: an operation can be free of memory effects and still trigger
  immediate UB.
-/
def isMemoryEffectFree (effects : MemoryEffects) : Bool :=
  !effects.reads && !effects.writes

end

end Veir
