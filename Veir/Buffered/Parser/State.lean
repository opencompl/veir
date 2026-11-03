module

public import Veir.Buffered.Parser.IRPointers
public import Veir.Buffered.Parser.Location

/-!
Context-independent parser bookkeeping. `Liveness.lean` equips these tables with erased
bounds and ownership proofs; `StaticParserState` carries that invariant in production.
Suspended block scopes are explicit, so recursive parsing cannot hide live references from
placeholder reclamation. Source locations are historical metadata, not liveness evidence.
-/
public section
namespace Veir.Buffered.Parser

inductive BlockEntry where
  | Defined (block : IR.Block) (loc : Location)
  | ForwardDeclared (block : IR.Block) (loc : Location)
  deriving Inhabited

@[expose]
def BlockEntry.block : BlockEntry → IR.Block
  | .Defined block _ => block
  | .ForwardDeclared block _ => block

/-- A detached, single-result placeholder for each referenced SSA result index.
The table is flat across regions, as in MLIR's generic-form parser. -/
structure ForwardValue where
  placeholders : Std.HashMap Nat (IR.Op × Location)
  loc : Location
  deriving Inhabited

abbrev BlockTable := Std.HashMap ByteArray BlockEntry

/-- Bookkeeping retained independently while a transaction consumes the IR buffer. -/
structure MlirParserData where
  values : Std.HashMap ByteArray (Array IR.Value × Location)
  definitionsPerScope : Array (Std.HashSet ByteArray)
  forwardValues : Std.HashMap ByteArray ForwardValue
  blocks : BlockTable
  blockScopes : Array BlockTable := #[]
  allowUnregisteredDialect : Bool := false
  typeAliases : Std.HashMap ByteArray TypeAttr := {}
  opLocations : Std.HashMap Buffed.OperationMPtr Location := {}
  deriving Inhabited

end Veir.Buffered.Parser
