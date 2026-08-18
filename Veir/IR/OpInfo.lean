module

public import Veir.IR.OpCode

namespace Veir

public section

inductive RegionKind where
| SSACFG
| Graph
deriving Inhabited, Repr, DecidableEq

/-- The memory effects an operation may have. -/
structure MemoryEffects where
  /-- The operation may dereference memory, without necessarily mutating it. -/
  reads : Bool
  /-- The operation may mutate memory, without necessarily dereferencing it. -/
  writes : Bool
  /--
  The operation may allocate memory, without necessarily reading or writing it.
  -/
  allocates : Bool
deriving Inhabited, Repr, DecidableEq

namespace MemoryEffects

def none : MemoryEffects := { reads := false, writes := false, allocates := false }

def read : MemoryEffects := { reads := true, writes := false, allocates := false }

def write : MemoryEffects := { reads := false, writes := true, allocates := false }

def readWrite : MemoryEffects := { reads := true, writes := true, allocates := false }

def allocate : MemoryEffects := { reads := false, writes := false, allocates := true }

/-- A conservative summary for an operation whose memory effects are unknown. -/
def unknown : MemoryEffects :=
  { reads := true, writes := true, allocates := true }

end MemoryEffects

class HasOpInfo (opCode: Type)
    extends IsOpCode opCode where
  /--
  The memory effects of an operation with this opcode and these properties,
  mirroring MLIR's `MemoryEffectOpInterface::getEffects`.
  -/
  getEffects : (op : opCode) → propertiesOf op → MemoryEffects :=
    fun _ _ => .unknown
  /--
  Whether an operation with this opcode materializes a literal constant
  value: no operands, one result, no side effects, and a result that is
  always determined by the operation's properties. Defaults to `false`
  for every opcode, which conservatively treats nothing as constant.
  -/
  isConstantLike : opCode → Bool := fun _ => false
  /--
  Whether an operation with this opcode acts like a function: a symbol
  whose single region is the function body.
  -/
  isFunctionLike : opCode → Bool := fun _ => false
  /--
  Return the kind of the indexed region inside an operation with this opcode.
  This mirrors MLIR's `RegionKindInterface` default: regions are SSACFG unless
  the operation is known to define graph regions.
  -/
  getRegionKind : opCode → Nat → RegionKind := fun _ _ => .SSACFG
  /--
  Whether definitions in the indexed region must dominate their uses. A false
  result denotes graph-style semantics, where only a single block can be in the
  region, and operation order does not impose SSA dominance.
  -/
  hasSSADominance : opCode → Nat → Bool
  /--
  Whether the indexed region is exempt from the requirement that each of its
  blocks ends in a terminator, mirroring MLIR's `NoTerminator` trait.

  This is deliberately separate from the region kind. A graph region implies
  no terminator, but the converse does not hold: MLIR gives `pdl.rewrite` a
  body that is an ordinary SSACFG region and yet carries `NoTerminator`.
  Encoding such a region as a graph region would silently drop SSA dominance
  from the model in order to relax an unrelated requirement.

  Defaults to `false` for every opcode, which conservatively keeps the
  terminator requirement.
  -/
  hasNoTerminator : opCode → Nat → Bool := fun _ _ => false
  /--
  Does this OpCode count as an MLIR basic block terminator?
  -/
  isTerminator : opCode → Bool := fun _ => false

end -- public section

end Veir
