module

public import Veir.Interfaces.SymbolInterfaces
public import Veir.IR.SymbolRef

/-!
# CallOpInterface

This file provides the `CallOpInterface` interface, which describes call-like operations such as
`func.call` and `llvm.call`.

Also see:
https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/CallInterfaces.td
-/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode]

public section

/-- A call-like operation. -/
structure CallOp (ctx : IRContext OpCode) (op : OperationPtr) where
  callOpInterface : CallOpInterface (propertiesOf (op.getOpType! ctx))
  callOpInterface?_eq : HasOpInfo.callOpInterface? (op.getOpType! ctx) = some callOpInterface

namespace CallOp

/--
The `CallOp` view of `op`, or `none` if it is not call-like.

This is equivalent to `mlir::dyn_cast<CallOpInterface>(op)` in MLIR.
-/
@[inline]
def of? (op : OperationPtr) (ctx : IRContext OpCode) : Option (CallOp ctx op) :=
  match h : HasOpInfo.callOpInterface? (op.getOpType! ctx) with
  | some callOpInterface => some ⟨callOpInterface, h⟩
  | none => none

@[simp]
theorem of?_eq_some {op : OperationPtr} {ctx : IRContext OpCode} (callOp : CallOp ctx op) :
    of? op ctx = some callOp := by
  cases callOp; grind [of?]

grind_pattern of?_eq_some => of? op ctx, callOp.callOpInterface

variable {ctx : IRContext OpCode} {op : OperationPtr}

/-- Returns the callee of the call. -/
def getCallableForCallee? (callOp : CallOp ctx op) : Option CallInterfaceCallable :=
  let props := op.getProperties! ctx (op.getOpType! ctx)
  callOp.callOpInterface.getCallableForCallee? props (op.getOperands! ctx)

/-- Returns the operation defining the callee of the call. -/
def resolveCallable? (callOp : CallOp ctx op) : Option OperationPtr :=
  match callOp.getCallableForCallee? with
  | some (.symbol ref) => do op.lookupNearestSymbolFrom? ctx ⟨← ref.getName?⟩
  | some (.value value) => value.definingOp?
  | none => none

end CallOp

end

end Veir
