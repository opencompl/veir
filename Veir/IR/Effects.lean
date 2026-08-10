module

/-!
  # Memory effects

  This file defines the vocabulary used by `HasOpInfo.getEffects` to describe
  the memory effects of an operation. It mirrors the effect side of MLIR's
  `MemoryEffectOpInterface`:

  https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/SideEffectInterfaces.h

  Upstream, an effect instance is a six-tuple: an effect kind, the resource the
  effect applies to, an optional value (operand, result, block argument, or
  symbol) it applies to, an optional parameter attribute, a stage ordering the
  effects within a single operation, and a flag saying whether the effect
  covers the resource in full or only in part.

  We currently model only the effect kind. The remaining fields describe
  information that no VeIR dialect records yet, so introducing them now would
  cost proof noise without buying precision. `EffectInstance` is a structure
  precisely so that they can be added later, with defaults, without disturbing
  either the effect vocabulary or the dialect definitions that use it.
-/

namespace Veir

public section

/--
  The kind of a memory effect, mirroring `mlir::MemoryEffects`.

  Upstream additionally has `Allocate` and `Free`, which are what let a pass
  prove that an unused allocation is dead. No VeIR dialect describes allocation
  yet, so they are omitted rather than left unpopulated.
-/
inductive MemoryEffect where
  /-- The operation dereferences a resource, without visibly mutating it. -/
  | read
  /-- The operation mutates a resource, without visibly dereferencing it. -/
  | write
deriving Inhabited, Repr, DecidableEq

/--
  A single memory effect exhibited by an operation, mirroring
  `mlir::SideEffects::EffectInstance`.

  Prefer the `EffectInstance.read` and `EffectInstance.write` constructors over
  the anonymous one, so that call sites keep elaborating when this structure
  grows the fields described at the top of this file.
-/
structure EffectInstance where
  /-- The effect being applied. -/
  effect : MemoryEffect
deriving Inhabited, Repr, DecidableEq

namespace EffectInstance

/-- The operation reads memory. -/
def read : EffectInstance := { effect := .read }

/-- The operation writes memory. -/
def write : EffectInstance := { effect := .write }

end EffectInstance

/--
  Do any of these effect instances have the given kind? Mirrors
  `mlir::hasEffect`.
-/
def hasEffect (effects : Array EffectInstance) (effect : MemoryEffect) : Bool :=
  effects.any (·.effect == effect)

/--
  Are these effects empty, i.e. does the operation they came from leave memory
  alone entirely? Mirrors `mlir::isMemoryEffectFree`.

  NOTE: as upstream, this says nothing about whether the operation is safe to
  speculate: an operation can be free of memory effects and still trigger
  immediate UB.
-/
def isMemoryEffectFree (effects : Array EffectInstance) : Bool :=
  effects.isEmpty

end

end Veir
