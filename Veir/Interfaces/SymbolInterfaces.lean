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
The `SymbolOp` view of `op`, or `none` if it is not a symbol.

As with `mlir::dyn_cast<SymbolOpInterface>(op)` in MLIR, an optional symbol without a name is not a
symbol.
-/
@[inline]
def of? (op : OperationPtr) (ctx : IRContext OpCode) : Option (SymbolOp ctx op) :=
  match h : HasOpInfo.symbolInterface? (op.getOpType! ctx) with
  | some symbolInterface =>
    if hName : (symbolInterface.getSymName (op.getProperties! ctx (op.getOpType! ctx))).isSome then
      some ⟨symbolInterface, h, hName⟩
    else
      none
  | none => none

/--
An operation implements `SymbolOpInterface` in at most one way, so any `SymbolOp` for `op` is the
one `of?` returns.
-/
@[simp]
theorem of?_eq_some {op : OperationPtr} {ctx : IRContext OpCode} (symbolOp : SymbolOp ctx op) :
    of? op ctx = some symbolOp := by
  cases symbolOp; grind [of?]

grind_pattern of?_eq_some => of? op ctx, symbolOp.symbolInterface

/--
The `SymbolOp` view of a symbol operation.

This is equivalent to `mlir::cast<SymbolOpInterface>(op)` in MLIR.
-/
@[inline]
def of (op : OperationPtr) (ctx : IRContext OpCode) (h : op.isSymbol ctx := by grind) :
    SymbolOp ctx op :=
  (of? op ctx).get (by grind [of?, OperationPtr.isSymbol])

variable {ctx : IRContext OpCode} {op : OperationPtr}

/-- Returns the name of the symbol. -/
def getSymName (symbolOp : SymbolOp ctx op) : StringAttr :=
  let opType := op.getOpType! ctx
  let props := op.getProperties! ctx opType
  (symbolOp.symbolInterface.getSymName props).get symbolOp.getSymName_isSome

end SymbolOp

end

end Veir
