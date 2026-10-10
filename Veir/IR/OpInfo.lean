module

public import Veir.IR.OpCode
public import Veir.IR.WellFormed
public import Veir.FoldDecision

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

/-- Information exposed by operations that define a symbol. -/
structure SymbolOpInterface (Properties : Type) where
  /-- Return the name of the symbol, or `none` for an optional symbol without a name. -/
  getSymName : Properties → Option StringAttr

/-- Information exposed by operations that behave like functions. -/
structure FunctionOpInterface (Properties : Type) where
  /-- Return the type of the function. -/
  getFunctionType : Properties → FunctionType
  /-- Return the properties with the function type replaced. -/
  setFunctionType : Properties → FunctionType → Properties

/-- The SSA values forwarded from a branch operation to one of its successors. -/
structure SuccessorOperands where
  /-- The SSA values forwarded to the successor. -/
  forwardedOperands : Array ValuePtr
deriving Inhabited, Repr, DecidableEq

instance : GetElem SuccessorOperands Nat ValuePtr
    (fun operands blockArgumentIndex => blockArgumentIndex < operands.forwardedOperands.size) where
  getElem := fun operands blockArgumentIndex h => operands.forwardedOperands[blockArgumentIndex]'h

instance : GetElem? SuccessorOperands Nat ValuePtr
    (fun operands blockArgumentIndex => blockArgumentIndex < operands.forwardedOperands.size) where
  getElem? := fun operands blockArgumentIndex => operands.forwardedOperands[blockArgumentIndex]?

/--
  Information exposed by operations that branch to successor blocks. `Dialect`
  is the opcode type an unconditional replacement branch is drawn from.
-/
structure BranchOpInterface (Dialect : Type) [IsOpCode Dialect] (Properties : Type) where
  /-- Return the operands passed to the indexed successor. -/
  getSuccessorOperandsImpl? :
    Properties → Array ValuePtr → Nat → Option SuccessorOperands
  /-- Return the index of the successor selected by the known constant operands. -/
  getSuccessorIndexForOperandsImpl? :
    Properties → Array (Option RuntimeValue) → Option Nat :=
      fun _ _ => none
  /--
  Return the unconditional branch, with its properties, that replaces this
  operation once its successor is known.
  -/
  getUnconditionalBranchImpl? : Properties → Option (Σ op : Dialect, propertiesOf op) :=
    fun _ => none

/-- Inject a dialect's branch interface into an opcode type containing the dialect. -/
def BranchOpInterface.lift {OpInfo Dialect : Type} [IsOpCode OpInfo] [IsOpCode Dialect]
    [HasDialect OpInfo Dialect] {Properties : Type}
    (interface : BranchOpInterface Dialect Properties) : BranchOpInterface OpInfo Properties :=
  { interface with
    getUnconditionalBranchImpl? := fun props =>
      (interface.getUnconditionalBranchImpl? props).map fun ⟨op, branchProps⟩ =>
        ⟨ofDialect OpInfo op, HasDialect.ofDialectProperties OpInfo op branchProps⟩ }

class HasOpInfo (opCode: Type)
    extends IsOpCode opCode where
  /--
  Verify the local invariants of an operation. This typically includes checking
  that the number of operands, successors, results, and regions match the
  expected values for the operation type, as well as checking that referenced
  types are in bounds.
  -/
  verifyLocalInvariants :
    (opType : opCode) → (op : OperationPtr) → (ctx : WfIRContext opCode) →
    (opIn : op.InBounds ctx.raw) → Except String PUnit :=
      fun _ _ _ _ => pure ()
  /--
  Apply this opcode set's dialect-local fold table. The input array contains
  the known constant value of each operand, or `none` for a nonconstant
  operand. The output array holds one decision per result, in result order: an
  operation folds entirely or not at all, so a table entry for a multi-result
  operation must decide every result. Implementations are responsible for
  returning an in-range operand or a constant conforming to the corresponding
  result type.
  -/
  tryFold : (op : opCode) → propertiesOf op → Array TypeAttr →
    Array (Option RuntimeValue) → Option (Array FoldDecision) := fun _ _ _ _ => none
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
  Whether an operation with this opcode produces a wholly poisoned result
  whenever any one of its operands is wholly poison, mirroring LLVM's
  `propagatesPoison`. Defaults to `false` for every opcode, which
  conservatively propagates nothing.
  -/
  propagatesPoison : opCode → Bool := fun _ => false
  /--
  Information about operations that define a symbol.
  -/
  symbolInterface? : (op : opCode) → Option (SymbolOpInterface (propertiesOf op)) :=
    fun _ => none
  /--
  Information about operations that act like functions.
  -/
  functionInterface? : (op : opCode) → Option (FunctionOpInterface (propertiesOf op)) :=
    fun _ => none
  /--
  Operations that act like functions must define a symbol.
  -/
  functionInterface_requires_symbol :
      ∀ {op f}, functionInterface? op = some f → (symbolInterface? op).isSome := by
    intro op f hf
    cases op <;> cases hf <;> rfl
  /--
  Operations that act like functions always have a symbol name: as in MLIR, a function is never
  an optional symbol.
  -/
  functionInterface_getSymName_isSome :
      ∀ {op f symbolInterface}, functionInterface? op = some f →
        symbolInterface? op = some symbolInterface →
        ∀ {props}, (symbolInterface.getSymName props).isSome := by
    intro op f symbolInterface hf hs props
    cases op <;> cases hf <;> cases hs <;> rfl
  /--
  Information about operations that branch to successor blocks.
  -/
  branchOpInterface? : (op : opCode) → Option (BranchOpInterface opCode (propertiesOf op)) :=
    fun _ => none
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
  /--
  Whether this operation has MLIR's `IsolatedFromAbove` trait. Operations in
  each of its regions may only use values defined in that region or one of its
  nested regions.
  -/
  isIsolatedFromAbove : opCode → Bool := fun _ => false

attribute [get_effects] HasOpInfo.getEffects
attribute [is_terminator] HasOpInfo.isTerminator

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Verify the local invariants of an operation using its opcode interface. -/
@[inline]
abbrev OperationPtr.verifyLocalInvariants (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit :=
  HasOpInfo.verifyLocalInvariants (op.getOpType ctx.raw opIn) op ctx opIn

/--
  Whether this region is exempt from the requirement that each of its blocks
  ends in a terminator.
-/
@[expose, inline]
public def RegionPtr.hasNoTerminator (region : RegionPtr) (ctx : WfIRContext OpInfo) : Bool :=
  match (region.get! ctx.raw).parent with
  | some parentOp =>
    let parent := parentOp.get! ctx.raw
    HasOpInfo.hasNoTerminator parent.opType (parent.regions.idxOf region)
  | none => false

end -- public section

end Veir
