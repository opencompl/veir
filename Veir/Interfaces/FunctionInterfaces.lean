module

public import Veir.Rewriter.WfRewriter

/-!
# FunctionOpInterface

This file provides the `FunctionOpInterface` interface, which provides support
for interacting with operations that behave like functions.
This includes source functions such as `llvm.func` and `func.func`, and
machine functions represented by `riscv_cf.func`.

Also see:
https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/FunctionInterfaces.td
-/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode]

public section

/-- Whether this operation acts like a function. -/
def OperationPtr.isFunctionLike (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  (HasOpInfo.functionInterface? (op.getOpType! ctx)).isSome

/-- A function-like operation. -/
structure FunctionOp (ctx : IRContext OpCode) (op : OperationPtr) where
  interface : FunctionOpInterface (propertiesOf (op.getOpType! ctx))
  functionInterface?_eq : HasOpInfo.functionInterface? (op.getOpType! ctx) = some interface

namespace FunctionOp

/--
Try to cast an operation to a `FunctionOp`.

This is equivalent to `mlir::dyn_cast<FunctionOpInterface>(op)` in MLIR.
-/
@[inline]
def cast? (op : OperationPtr) (ctx : IRContext OpCode) : Option (FunctionOp ctx op) :=
  match h : HasOpInfo.functionInterface? (op.getOpType! ctx) with
  | some interface => some ⟨interface, h⟩
  | none => none

@[simp]
theorem cast?_eq_some {op : OperationPtr} {ctx : IRContext OpCode} (funcOp : FunctionOp ctx op) :
    cast? op ctx = some funcOp := by
  cases funcOp; grind [cast?]

grind_pattern cast?_eq_some => cast? op ctx, funcOp.interface

/--
Cast a function-like operation to a `FunctionOp`.

This is equivalent to `mlir::cast<FunctionOpInterface>(op)` in MLIR.
-/
@[inline]
def cast (op : OperationPtr) (ctx : IRContext OpCode) (h : op.isFunctionLike ctx := by grind) :
    FunctionOp ctx op :=
  (cast? op ctx).get (by grind [cast?, OperationPtr.isFunctionLike])

variable {ctx : IRContext OpCode} {op : OperationPtr}

/-- Returns the symbol name of the function. -/
def getSymName (funcOp : FunctionOp ctx op) : StringAttr :=
  let opType := op.getOpType! ctx
  funcOp.interface.getSymName (op.getProperties! ctx opType)

/-- Returns the type of the function. -/
def getFunctionType (funcOp : FunctionOp ctx op) : FunctionType :=
  let opType := op.getOpType! ctx
  funcOp.interface.getFunctionType (op.getProperties! ctx opType)

/-!
## Body Handling
-/

/-- Returns the region containing the body of this function. -/
def getFunctionBody (_funcOp : FunctionOp ctx op)
    (opInBounds : op.InBounds ctx := by grind)
    (hasRegion : 0 < op.getNumRegions ctx opInBounds := by grind) : RegionPtr :=
  op.getRegion ctx 0 opInBounds hasRegion

/-- Returns the region containing the body of this function. -/
def getFunctionBody! (_funcOp : FunctionOp ctx op) : RegionPtr :=
  op.getRegion! ctx 0

@[grind =_, eq_bang ←]
theorem getFunctionBody!_eq_getFunctionBody {funcOp : FunctionOp ctx op}
    {opInBounds} (hasRegion : 0 < op.getNumRegions ctx opInBounds) :
    funcOp.getFunctionBody! = funcOp.getFunctionBody opInBounds hasRegion := by
  grind [getFunctionBody, getFunctionBody!]

theorem getFunctionBody!_inBounds {funcOp : FunctionOp ctx op}
    (ctxInBounds : ctx.FieldsInBounds)
    (opInBounds : op.InBounds ctx)
    (hasRegion : 0 < op.getNumRegions! ctx) :
    funcOp.getFunctionBody!.InBounds ctx := by
  grind [getFunctionBody!, OperationPtr.getRegions!_inBounds]

grind_pattern getFunctionBody!_inBounds => (getFunctionBody! (ctx := ctx) funcOp), ctx.FieldsInBounds

/-- Returns the first block in the body region, or `none` if the body is empty. -/
def getEntryBlock? (funcOp : FunctionOp ctx op) : Option BlockPtr :=
  if op.getNumRegions! ctx = 0 then none else (funcOp.getFunctionBody!.get! ctx).firstBlock

/--
Returns true if the function has no body, e.g. a declaration of an external function.
-/
def isExternal (funcOp : FunctionOp ctx op) : Bool :=
  funcOp.getEntryBlock?.isNone

/-!
## Type Attribute Handling
-/

/-- Sets the function type to the given input/output type lists. -/
def setFunctionType (wfCtx : WfIRContext OpCode) (funcOp : FunctionOp wfCtx.raw op)
    (inputs outputs : Array Attribute)
    (opInBounds : op.InBounds wfCtx.raw := by grind) : WfIRContext OpCode :=
  let opType := op.getOpType! wfCtx.raw
  let props := op.getProperties! wfCtx.raw opType
  let newProps := funcOp.interface.setFunctionType props { inputs, outputs }
  WfRewriter.setProperties wfCtx op opType newProps opInBounds

/-- Sets the function type to the given input/output type lists, panicking if the op
    is out of bounds. -/
def setFunctionType! (wfCtx : WfIRContext OpCode) (funcOp : FunctionOp wfCtx.raw op)
    (inputs outputs : Array Attribute) : WfIRContext OpCode :=
  if opInBounds : op.InBounds wfCtx.raw then
    setFunctionType wfCtx funcOp inputs outputs opInBounds
  else
    panic "FunctionOp.setFunctionType! failed: operation is out of bounds"

/-!
## Argument and Result Handling
-/

/-- Returns the number of function arguments. -/
def getNumArguments (funcOp : FunctionOp ctx op) : Nat :=
  funcOp.getFunctionType.inputs.size

/-- Returns the argument types of the function. -/
def getArgumentTypes (funcOp : FunctionOp ctx op) : Array Attribute :=
  funcOp.getFunctionType.inputs

/-- Returns the number of function results. -/
def getNumResults (funcOp : FunctionOp ctx op) : Nat :=
  funcOp.getFunctionType.outputs.size

/-- Returns the result types of the function. -/
def getResultTypes (funcOp : FunctionOp ctx op) : Array Attribute :=
  funcOp.getFunctionType.outputs

end FunctionOp

end

end Veir
