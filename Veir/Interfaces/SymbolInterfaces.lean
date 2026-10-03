module

public import Veir.IR.OpInfo

/-!
# SymbolOpInterface

This file provides the `SymbolOpInterface` interface, which describes operations that define a
symbol.

Also see:
https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/IR/SymbolInterfaces.td
https://github.com/llvm/llvm-project/blob/main/mlir/docs/SymbolsAndSymbolTables.md
-/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode]

public section

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

end

end Veir
