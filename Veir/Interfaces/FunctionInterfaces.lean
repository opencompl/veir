module

public import Veir.GlobalOpInfo
public import Veir.IR.Fields
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

public section

namespace FunctionOpInterface

/-- Returns the symbol name of the function. -/
def getSymName? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option StringAttr :=
  match funcOp.getOpType! raw with
  | .func .func =>
    (funcOp.getProperties! raw (.func .func) : FuncFuncProperties).sym_name
  | .llvm .func =>
    (funcOp.getProperties! raw (.llvm .func) : LLVMFuncProperties).sym_name
  | _ => none

/-- Returns the type of the function. -/
def getFunctionType? (funcOp : OperationPtr) (raw : IRContext OpCode) :
    Option FunctionType := do
  match funcOp.getOpType! raw with
  | .func .func =>
    let ta ← (funcOp.getProperties! raw (.func .func) : FuncFuncProperties).function_type
    match ta.val with
    | .functionType ft => some ft
    | _ => none
  | .llvm .func =>
    let ta ← (funcOp.getProperties! raw (.llvm .func) : LLVMFuncProperties).function_type
    match ta.val with
    | .llvmFunctionType ft => some ft
    | _ => none
  | _ => none

/-!
## Body Handling
-/

/-- Returns the region containing the body of this function. -/
def getFunctionBody (funcOp : OperationPtr) (raw : IRContext OpCode)
    (opInBounds : funcOp.InBounds raw := by grind)
    (hasRegion : 0 < funcOp.getNumRegions raw opInBounds := by grind) : RegionPtr :=
  funcOp.getRegion raw 0 opInBounds hasRegion

/-- Returns the region containing the body of this function. -/
def getFunctionBody! (funcOp : OperationPtr) (raw : IRContext OpCode) : RegionPtr :=
  funcOp.getRegion! raw 0

@[grind =_, eq_bang ←]
theorem getFunctionBody!_eq_getFunctionBody {funcOp : OperationPtr} {raw : IRContext OpCode}
    {opInBounds} (hasRegion : 0 < funcOp.getNumRegions raw opInBounds) :
    getFunctionBody! funcOp raw = getFunctionBody funcOp raw opInBounds hasRegion := by
  grind [getFunctionBody, getFunctionBody!]

theorem getFunctionBody!_inBounds
    (ctxInBounds : raw.FieldsInBounds)
    (opInBounds : funcOp.InBounds raw)
    (hasRegion : 0 < funcOp.getNumRegions! raw) :
    (getFunctionBody! funcOp raw).InBounds raw := by
  grind [getFunctionBody!, OperationPtr.getRegions!_inBounds]

grind_pattern getFunctionBody!_inBounds => (getFunctionBody! funcOp raw), raw.FieldsInBounds

/-- Returns the first block in the body region. -/
def getEntryBlock? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option BlockPtr :=
  ((getFunctionBody! funcOp raw).get! raw).firstBlock

/-!
## Type Attribute Handling
-/

/-- Sets the function type to the given input/output type lists.
    `llvm.func` is canonicalized to the `.llvmFunctionType` spelling, regardless of
    which spelling the original attribute used. -/
def setFunctionType (wfCtx : WfIRContext OpCode) (funcOp : OperationPtr)
    (inputs outputs : Array Attribute)
    (opInBounds : funcOp.InBounds wfCtx.raw := by grind) : WfIRContext OpCode :=
  match h : funcOp.getOpType wfCtx.raw opInBounds with
  | .func .func =>
    let ftType : TypeAttr := ⟨.functionType { inputs, outputs }, by simp⟩
    let props : FuncFuncProperties := funcOp.getProperties! wfCtx.raw (.func .func)
    let newProps : FuncFuncProperties := { props with function_type := some ftType }
    WfRewriter.setProperties (opCode := .func .func) wfCtx funcOp newProps opInBounds
  | .llvm .func =>
    let ftType : TypeAttr := ⟨.llvmFunctionType { inputs, outputs }, by simp⟩
    let props : LLVMFuncProperties := funcOp.getProperties! wfCtx.raw (.llvm .func)
    let newProps : LLVMFuncProperties := { props with function_type := some ftType }
    WfRewriter.setProperties (opCode := .llvm .func) wfCtx funcOp newProps opInBounds
  | _ => wfCtx

/-- Sets the function type to the given input/output type lists, panicking if the op
    is out of bounds.
    `llvm.func` is canonicalized to the `.llvmFunctionType` spelling, regardless of
    which spelling the original attribute used. -/
def setFunctionType! (c : WfIRContext OpCode) (funcOp : OperationPtr)
    (inputs outputs : Array Attribute) : WfIRContext OpCode :=
  if opInBounds : funcOp.InBounds c.raw then
    setFunctionType c funcOp inputs outputs opInBounds
  else
    panic "FunctionOpInterface.setFunctionType! failed: operation is out of bounds"

/-!
## Argument and Result Handling
-/

/-- Returns the number of function arguments. -/
def getNumArguments? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option Nat := do
  rlet ft ← getFunctionType? funcOp raw
  ft.inputs.size

/-- Returns the argument types of the function. -/
def getArgumentTypes? (funcOp: OperationPtr) (raw: IRContext OpCode) :
    Option (Array Attribute) := do
  rlet ft ← getFunctionType? funcOp raw
  ft.inputs

/-- Returns the number of function results. -/
def getNumResults? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option Nat := do
  rlet ft ← getFunctionType? funcOp raw
  ft.outputs.size

/-- Returns the result types of the function. -/
def getResultTypes? (funcOp : OperationPtr) (raw : IRContext OpCode) :
    Option (Array Attribute) := do
  rlet ft ← getFunctionType? funcOp raw
  ft.outputs

/-- Returns the result types of the function. -/
def getResultTypes! (funcOp : OperationPtr) (raw : IRContext OpCode) : Array Attribute :=
  (getResultTypes? funcOp raw).get!

end FunctionOpInterface

end

end Veir
