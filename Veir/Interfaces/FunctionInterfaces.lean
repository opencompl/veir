module

public import Veir.GlobalOpInfo
public import Veir.IR.Fields

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
