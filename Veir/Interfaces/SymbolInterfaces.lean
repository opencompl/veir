module

public import Veir.IR.OpInfo

/-!
# Symbols and Symbol Tables

This file provides the `SymbolOpInterface` interface, which describes operations that define a
symbol. It also provides the lookup of symbols by name in the operations with the `SymbolTable`
trait.

Also see:
https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/IR/SymbolInterfaces.td
https://github.com/llvm/llvm-project/blob/main/mlir/docs/SymbolsAndSymbolTables.md
-/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode]

public section

/-!
## SymbolOp
-/

/--
Whether this operation is a symbol. As in MLIR, an optional symbol without a name is not a symbol.
-/
def OperationPtr.isSymbol (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  (HasOpInfo.symbolInterface? (op.getOpType! ctx)).any fun symbolInterface =>
    (symbolInterface.getSymName (op.getProperties! ctx (op.getOpType! ctx))).isSome

/-- An operation that is a symbol. -/
structure SymbolOp (ctx : IRContext OpCode) (op : OperationPtr) where
  symbolInterface : SymbolOpInterface (propertiesOf (op.getOpType! ctx))
  symbolInterface?_eq : HasOpInfo.symbolInterface? (op.getOpType! ctx) = some symbolInterface
  /-- The symbol has a name, which an optional symbol may lack. -/
  getSymName_isSome :
    (symbolInterface.getSymName (op.getProperties! ctx (op.getOpType! ctx))).isSome

namespace SymbolOp

/--
Try to cast an operation to a `SymbolOp`. This fails for an optional symbol without a name.

This is equivalent to `mlir::dyn_cast<SymbolOpInterface>(op)` in MLIR, where `SymbolOpInterface`
checks for the name in its `extraClassOf`.
-/
@[inline]
def cast? (op : OperationPtr) (ctx : IRContext OpCode) : Option (SymbolOp ctx op) :=
  match h : HasOpInfo.symbolInterface? (op.getOpType! ctx) with
  | some symbolInterface =>
    if hName : (symbolInterface.getSymName (op.getProperties! ctx (op.getOpType! ctx))).isSome then
      some ⟨symbolInterface, h, hName⟩
    else
      none
  | none => none

/--
An operation implements `SymbolOpInterface` in at most one way, so any `SymbolOp` is the cast.
-/
@[simp]
theorem cast?_eq_some {op : OperationPtr} {ctx : IRContext OpCode} (symbolOp : SymbolOp ctx op) :
    cast? op ctx = some symbolOp := by
  cases symbolOp; grind [cast?]

grind_pattern cast?_eq_some => cast? op ctx, symbolOp.symbolInterface

/--
Cast a symbol operation to a `SymbolOp`.

This is equivalent to `mlir::cast<SymbolOpInterface>(op)` in MLIR.
-/
@[inline]
def cast (op : OperationPtr) (ctx : IRContext OpCode) (h : op.isSymbol ctx := by grind) :
    SymbolOp ctx op :=
  (cast? op ctx).get (by grind [cast?, OperationPtr.isSymbol])

variable {ctx : IRContext OpCode} {op : OperationPtr}

/-- Returns the name of the symbol. -/
def getSymName (symbolOp : SymbolOp ctx op) : StringAttr :=
  let opType := op.getOpType! ctx
  let props := op.getProperties! ctx opType
  (symbolOp.symbolInterface.getSymName props).get symbolOp.getSymName_isSome

end SymbolOp

/-!
## Symbol Tables
-/

/-- Whether this operation has the `SymbolTable` trait. -/
def OperationPtr.isSymbolTable (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  HasOpInfo.isSymbolTable (op.getOpType! ctx)

/-- The first operation from `op` onward in its block that defines the symbol `name`. -/
private def OperationPtr.findSymbolFrom? (op : OperationPtr) (ctx : IRContext OpCode)
    (name : StringAttr) : Option OperationPtr := do
  if (SymbolOp.cast? op ctx).map (·.getSymName) = some name then
    return op
  let next ← (op.get! ctx).next
  next.findSymbolFrom? ctx name
partial_fixpoint

/-- Returns the symbol named `name` defined directly in the symbol table `op`. -/
def OperationPtr.lookupSymbolIn? (op : OperationPtr) (ctx : IRContext OpCode)
    (name : StringAttr) (_hst : op.isSymbolTable ctx := by grind) : Option OperationPtr := do
  let region ← (op.get! ctx).regions[0]?
  let block ← (region.get! ctx).firstBlock
  let firstOp ← (block.get! ctx).firstOp
  firstOp.findSymbolFrom? ctx name

/--
Returns the symbol named `name` defined directly in `op`, panicking if `op` is not a symbol table.
-/
def OperationPtr.lookupSymbolIn! (op : OperationPtr) (ctx : IRContext OpCode)
    (name : StringAttr) : Option OperationPtr :=
  if hst : op.isSymbolTable ctx then
    op.lookupSymbolIn? ctx name hst
  else
    panic "OperationPtr.lookupSymbolIn! failed: operation is not a symbol table"

@[grind =_, eq_bang ←]
theorem OperationPtr.lookupSymbolIn!_eq_lookupSymbolIn? {op : OperationPtr}
    {ctx : IRContext OpCode} {name : StringAttr} (hst : op.isSymbolTable ctx) :
    op.lookupSymbolIn! ctx name = op.lookupSymbolIn? ctx name hst := by
  simp [lookupSymbolIn!, hst]

/--
Returns the closest symbol table containing `op`, which is `op` itself if it is a symbol table.

This differs from upstream MLIR in that an unregistered operation does not end the search.
-/
def OperationPtr.getNearestSymbolTable? (op : OperationPtr) (ctx : IRContext OpCode) :
    Option {table : OperationPtr // table.isSymbolTable ctx} := do
  if h : op.isSymbolTable ctx then
    return ⟨op, h⟩
  let parent ← op.getParentOp! ctx
  parent.getNearestSymbolTable? ctx
partial_fixpoint

/--
Returns the symbol named `name` in the closest symbol table containing `op`.
-/
def OperationPtr.lookupNearestSymbolFrom? (op : OperationPtr) (ctx : IRContext OpCode)
    (name : StringAttr) : Option OperationPtr := do
  let ⟨table, hst⟩ ← op.getNearestSymbolTable? ctx
  table.lookupSymbolIn? ctx name hst

end

end Veir
