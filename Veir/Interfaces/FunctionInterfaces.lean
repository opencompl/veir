module

public import Veir.Rewriter.WfRewriter

/-!
# FunctionOpInterface

This file provides the `FunctionOpInterface` interface, which provides support
for interacting with operations that behave like functions.
Currently, this supports llvm.func and func.func.

Also see:
https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/FunctionInterfaces.td
-/

namespace Veir

variable {OpCode : Type}

public section

section

variable [HasOpTraits OpCode]

/-- A function-like operation -/
structure FunctionOp (ctx : IRContext OpCode) where
  op : OperationPtr
  interface : FunctionOpInterface (propertiesOf (op.getOpType! ctx))
  functionInterface?_eq : HasOpTraits.functionInterface? (op.getOpType! ctx) = some interface

namespace FunctionOp

/--
Try to cast an operation to a `FunctionOp`.

This is equivalent to `mlir::dyn_cast<FunctionOpInterface>(op)` in MLIR.
-/
@[inline]
def cast? (op : OperationPtr) (ctx : IRContext OpCode) : Option (FunctionOp ctx) :=
  match h : HasOpTraits.functionInterface? (op.getOpType! ctx) with
  | some interface => some ⟨op, interface, h⟩
  | none => none

@[simp]
theorem cast?_eq_some_iff (op : OperationPtr) (ctx : IRContext OpCode) (funcOp : FunctionOp ctx) :
    cast? op ctx = some funcOp ↔ funcOp.op = op := by
  cases funcOp; grind [cast?]

grind_pattern cast?_eq_some_iff => cast? op ctx, funcOp.op

variable {ctx : IRContext OpCode}

/-- Returns the symbol name of the function. -/
def getSymName? (funcOp : FunctionOp ctx) : Option StringAttr :=
  let opType := funcOp.op.getOpType! ctx
  funcOp.interface.getSymName (funcOp.op.getProperties! ctx opType)

/-- Returns the type of the function. -/
def getFunctionType (funcOp : FunctionOp ctx) : FunctionType :=
  let opType := funcOp.op.getOpType! ctx
  funcOp.interface.getFunctionType (funcOp.op.getProperties! ctx opType)

/-!
## Body Handling
-/

/-- Returns the region containing the body of this function. -/
def getFunctionBody (funcOp : FunctionOp ctx)
    (opInBounds : funcOp.op.InBounds ctx := by grind)
    (hasRegion : 0 < funcOp.op.getNumRegions ctx opInBounds := by grind) : RegionPtr :=
  funcOp.op.getRegion ctx 0 opInBounds hasRegion

/-- Returns the region containing the body of this function. -/
def getFunctionBody! (funcOp : FunctionOp ctx) : RegionPtr :=
  funcOp.op.getRegion! ctx 0

@[grind =_, eq_bang ←]
theorem getFunctionBody!_eq_getFunctionBody {funcOp : FunctionOp ctx}
    {opInBounds} (hasRegion : 0 < funcOp.op.getNumRegions ctx opInBounds) :
    funcOp.getFunctionBody! = funcOp.getFunctionBody opInBounds hasRegion := by
  grind [getFunctionBody, getFunctionBody!]

theorem getFunctionBody!_inBounds {funcOp : FunctionOp ctx}
    (ctxInBounds : ctx.FieldsInBounds)
    (opInBounds : funcOp.op.InBounds ctx)
    (hasRegion : 0 < funcOp.op.getNumRegions! ctx) :
    funcOp.getFunctionBody!.InBounds ctx := by
  grind [getFunctionBody!, OperationPtr.getRegions!_inBounds]

grind_pattern getFunctionBody!_inBounds => (getFunctionBody! (ctx := ctx) funcOp), ctx.FieldsInBounds

/-- Returns the first block in the body region. -/
def getEntryBlock? (funcOp : FunctionOp ctx) : Option BlockPtr :=
  (funcOp.getFunctionBody!.get! ctx).firstBlock

/-!
## Argument and Result Handling
-/

/-- Returns the number of function arguments. -/
def getNumArguments (funcOp : FunctionOp ctx) : Nat :=
  funcOp.getFunctionType.inputs.size

/-- Returns the argument types of the function. -/
def getArgumentTypes (funcOp : FunctionOp ctx) : Array Attribute :=
  funcOp.getFunctionType.inputs

/-- Returns the number of function results. -/
def getNumResults (funcOp : FunctionOp ctx) : Nat :=
  funcOp.getFunctionType.outputs.size

/-- Returns the result types of the function. -/
def getResultTypes (funcOp : FunctionOp ctx) : Array Attribute :=
  funcOp.getFunctionType.outputs

end FunctionOp

end

namespace FunctionOp

/-!
## Type Attribute Handling

Setting the function type rewrites the operation, which needs `HasOpInfo`.
-/

variable [HasOpInfo OpCode]

/-- Sets the function type to the given input/output type lists. -/
def setFunctionType (wfCtx : WfIRContext OpCode) (funcOp : FunctionOp wfCtx.raw)
    (inputs outputs : Array Attribute)
    (opInBounds : funcOp.op.InBounds wfCtx.raw := by grind) : WfIRContext OpCode :=
  let opType := funcOp.op.getOpType! wfCtx.raw
  let props := funcOp.op.getProperties! wfCtx.raw opType
  let newProps := funcOp.interface.setFunctionType props { inputs, outputs }
  WfRewriter.setProperties wfCtx funcOp.op opType newProps opInBounds

/-- Sets the function type to the given input/output type lists, panicking if the op
    is out of bounds. -/
def setFunctionType! (wfCtx : WfIRContext OpCode) (funcOp : FunctionOp wfCtx.raw)
    (inputs outputs : Array Attribute) : WfIRContext OpCode :=
  if opInBounds : funcOp.op.InBounds wfCtx.raw then
    setFunctionType wfCtx funcOp inputs outputs opInBounds
  else
    panic "FunctionOp.setFunctionType! failed: operation is out of bounds"

end FunctionOp

end

end Veir
