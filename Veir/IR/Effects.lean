module

/-!
  # Memory effects

  This file defines the vocabulary used by `HasOpInfo.getEffects` to describe
  the memory effects of an operation. It corresponds to MLIR's
  `MemoryEffectOpInterface`:

  https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/SideEffectInterfaces.h

  Upstream returns a list of effect instances, where an instance is a six-tuple:
  an effect kind, the resource the effect applies to, an optional value (operand,
  result, block argument, or symbol) it applies to, an optional parameter
  attribute, a stage ordering the effects within a single operation, and a flag
  saying whether the effect covers the resource in full or only in part. That
  list is a multiset: two read instances are genuinely different effects when
  they name different values or resources, and its order carries no meaning.

  We record none of those fields, so the only thing an operation can say is
  which kinds of effect it may have. A record of flags states exactly that, and
  no more: unlike a list, it cannot express an order or a multiplicity that the
  semantics does not have, so equality on it is equality of meaning.

  Recovering upstream's precision -- which operand is read, which resource is
  written -- means replacing this record with a collection of instances, not
  extending it. That is a deliberate trade: this file describes what VeIR models
  today rather than reserving room for what it might model later.
-/

namespace Veir

public section

/--
  The memory effects an operation may have.

  A field reports only that the effect may occur. In particular `writes` does
  not imply that the operation completely overwrites any particular location,
  so it is not by itself sufficient to prove that an earlier write is dead;
  that is what upstream's `FullEffect` marker is for.
-/
structure MemoryEffects where
  /-- The operation may dereference memory, without necessarily mutating it. -/
  reads : Bool
  /-- The operation may mutate memory, without necessarily dereferencing it. -/
  writes : Bool
deriving Inhabited, Repr, DecidableEq

namespace MemoryEffects

/-- The operation leaves memory alone. Corresponds to `NoMemoryEffect`. -/
def none : MemoryEffects := { reads := false, writes := false }

/-- The operation only reads memory. -/
def read : MemoryEffects := { reads := true, writes := false }

/-- The operation only writes memory. -/
def write : MemoryEffects := { reads := false, writes := true }

/-- The operation both reads and writes memory. -/
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
