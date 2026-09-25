module

public import Veir.IR.OpInfo

/-!
# SymbolOpInterface

This file provides the `SymbolOpInterface` interface, describes an operation that may define a `Symbol`.

Also see:
- Definition of 'Symbol' and 'SymbolTable':
https://github.com/llvm/llvm-project/blob/main/mlir/docs/SymbolsAndSymbolTables.md
- Upstream `SymbolOpInterface`:
https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/IR/SymbolInterfaces.td
-/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode]

public section

namespace SymbolOpInterface

/-- Returns the name of the symbol defined by this operation, or `none` if it defines none. -/
def getSymName? (op : OperationPtr) (raw : IRContext OpCode) : Option StringAttr := do
  let opType := op.getOpType! raw
  let interface ← HasOpInfo.symbolInterface? opType
  interface.getSymName (op.getProperties! raw opType)

end SymbolOpInterface

end

end Veir
