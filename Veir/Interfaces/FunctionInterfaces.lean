module

/- FunctionOpInterface

  This file provides the `FunctionOpInterface` interface, which provides support
  for interacting with operations that behave like functions.
  Currently, this supports llvm.func and func.func.

  Also see:
  https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/FunctionInterfaces.td
-/

public import Veir.GlobalOpInfo
public import Veir.IR.Fields

namespace Veir

public section

namespace FunctionOpInterface

/-- Returns the symbol name of the function. -/
public def getSymName? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option StringAttr :=
  match funcOp.getOpType! raw with
  | .func .func =>
    (funcOp.getProperties! raw (.func .func) : FuncFuncProperties).sym_name
  | .llvm .func =>
    (funcOp.getProperties! raw (.llvm .func) : LLVMFuncProperties).sym_name
  | _ => none

/-- Returns the type of the function. -/
public def getFunctionType? (funcOp : OperationPtr) (raw : IRContext OpCode) :
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

/-
  Body Handling
-/

/-- Returns the region containing the body of this function. -/
public def getFunctionBody (funcOp : OperationPtr) (raw : IRContext OpCode)
    (opInBounds : funcOp.InBounds raw := by grind)
    (hasRegion : 0 < funcOp.getNumRegions raw opInBounds := by grind) : RegionPtr :=
  funcOp.getRegion raw 0 opInBounds hasRegion

public def getFunctionBody! (funcOp : OperationPtr) (raw : IRContext OpCode) : RegionPtr :=
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
public def getFirstBlock? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option BlockPtr :=
  ((getFunctionBody! funcOp raw).get! raw).firstBlock

/-- Returns the last block in the body region. -/
public def getLastBlock? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option BlockPtr :=
  ((getFunctionBody! funcOp raw).get! raw).lastBlock

/-
  Argument and Result Handling
-/

/-- Returns the number of function arguments. -/
public def getNumArguments? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option Nat := do
  rlet ft ← getFunctionType? funcOp raw
  ft.inputs.size

/-- Returns the result types of the function. -/
public def getResultTypes? (funcOp : OperationPtr) (raw : IRContext OpCode) :
    Option (Array Attribute) := do
  rlet ft ← getFunctionType? funcOp raw
  ft.outputs

end FunctionOpInterface

end -- public section

end Veir
