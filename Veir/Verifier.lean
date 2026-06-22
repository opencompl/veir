module

public import Veir.IR.Basic
public import Veir.IR.Fields
public import Veir.Properties
public import Veir.GlobalOpInfo
public import Veir.IR.WellFormed
import Veir.ForLean

namespace Veir

/--
  Walk up from `op` (a return-like terminator named `opName`) to the
  operation that encloses its parent region, i.e. the enclosing function
  operation.
-/
def OperationPtr.getEnclosingFunctionOp (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opName : String) : Except String OperationPtr := do
  let some block := (op.get! ctx.raw).parent
    | throw s!"Expected {opName} to have a parent block"
  let some region := (block.get! ctx.raw).parent
    | throw s!"Expected {opName}'s parent block to have a parent region"
  let some funcOp := (region.get! ctx.raw).parent
    | throw s!"Expected {opName}'s parent region to have a parent operation"
  pure funcOp

/--
  Check that a `func.return` returns the declared result types of its
  enclosing `func.func`.
-/
def OperationPtr.verifyFuncReturnTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let funcOp ← op.getEnclosingFunctionOp ctx "func.return"
  let .func .func := funcOp.getOpType! ctx.raw
    | throw "Expected func.return to be enclosed by func.func"
  let props := funcOp.getProperties! ctx.raw (.func .func)
  let outputs ← match props.extra.entries.find? (fun entry => entry.1 == "function_type".toUTF8) with
    | some (_, .functionType ft) => pure ft.outputs
    | some _ => throw "Expected enclosing func.func's function_type to be a function type"
    | none => throw "Expected enclosing func.func to have a function_type attribute"
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected func.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if (opTypes[i]!).val ≠ outputs[i]! then
      throw s!"func.return operand {i} type does not match the function's declared result type"

/--
  Check that an `llvm.return` returns the declared result types of its
  enclosing `llvm.func`. A single `llvm.void` result is normalized to no
  results.
-/
def OperationPtr.verifyLLVMReturnTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let funcOp ← op.getEnclosingFunctionOp ctx "llvm.return"
  let .llvm .func := funcOp.getOpType! ctx.raw
    | throw "Expected llvm.return to be enclosed by llvm.func"
  let props := funcOp.getProperties! ctx.raw (.llvm .func)
  let some functionType := props.function_type
    | throw "Expected enclosing llvm.func to have a function_type attribute"
  let ft ← match functionType.val with
    | .functionType ft | .llvmFunctionType ft => pure ft
    | _ => throw "Expected enclosing llvm.func's function_type to be a function type"
  -- A single `llvm.void` result corresponds to no return operands.
  let outputs := match ft.outputs with
    | #[.llvmVoidType _] => #[]
    | outputs => outputs
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected llvm.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if (opTypes[i]!).val ≠ outputs[i]! then
      throw s!"llvm.return operand {i} type does not match the function's declared result type"

def TypeAttr.verifyIntegerType (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .integerType _ => pure ()
  | _ => throw errMsg

def TypeAttr.verifyIntegerOrPointerType (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .integerType _ => pure ()
  | .llvmPointerType _ => pure ()
  | _ => throw errMsg

def TypeAttr.verifyI1 (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .integerType intType =>
    if intType.bitwidth ≠ 1 then
      throw errMsg
    else
      pure ()
  | _ => throw errMsg

/--
  Check that the operands forwarded to a successor block match the types of that
  block's arguments. `operandBase` is the index of the first forwarded operand;
  the forwarded operands are `operandBase .. operandBase + dest.numArguments`,
  mapped positionally onto `dest`'s arguments. Callers must have already verified
  that this operand range is in bounds (i.e. the relevant segment size equals the
  successor's argument count).
-/
def OperationPtr.verifyBranchSuccessorArgTypes
    (op : OperationPtr) (ctx : WfIRContext OpCode)
    (operandBase : Nat) (dest : BlockPtr) (errPrefix : String) :
    Except String PUnit := do
  for j in [0:dest.getNumArguments! ctx.raw] do
    let opTy := (op.getOperand! ctx.raw (operandBase + j)).getType! ctx.raw
    let argTy := ((dest.getArgument j).get! ctx.raw).type
    if opTy.val ≠ argTy.val then
      throw s!"{errPrefix} argument {j} type mismatch: operand has type {opTy}, block argument has type {argTy}"

def OperationPtr.verifyRISCVBranchOperandSegmentSizes
    (op : OperationPtr) (ctx : WfIRContext OpCode) (opIn : op.InBounds ctx.raw)
    (sizes : DenseArrayAttr) (fixedOperands : Nat) :
    Except String PUnit := do
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  if _ : sizes.values.size ≠ fixedOperands + 2 then
    throw s!"{instrName}: operandSegmentSizes expected {fixedOperands + 2} entries, got {sizes.values.size}"
  let mut operandSegmentSizes : Array Nat := #[]
  for size in sizes.values do
    if size < 0 then
      throw s!"{instrName}: operandSegmentSizes contains negative size {size}"
    operandSegmentSizes := operandSegmentSizes.push size.toNat
  for i in [0:fixedOperands] do
    if operandSegmentSizes[i]! ≠ 1 then
      throw s!"{instrName}: fixed operand segment {i} expected size 1, got {operandSegmentSizes[i]!}"
  let operandSegmentSum := operandSegmentSizes.foldl (init := 0) fun acc size => acc + size
  if operandSegmentSum ≠ op.getNumOperands ctx.raw opIn then
    throw s!"{instrName}: operandSegmentSizes describes {operandSegmentSum} operands, got {op.getNumOperands ctx.raw opIn}"
  let trueArgCount := operandSegmentSizes[fixedOperands]!
  let falseArgCount := operandSegmentSizes[fixedOperands + 1]!
  let trueDest := op.getSuccessor! ctx.raw 0
  let falseDest := op.getSuccessor! ctx.raw 1
  if trueArgCount ≠ trueDest.getNumArguments! ctx.raw then
    throw s!"{instrName}: true operand segment expected operand count {trueDest.getNumArguments! ctx.raw}, got {trueArgCount}"
  if falseArgCount ≠ falseDest.getNumArguments! ctx.raw then
    throw s!"{instrName}: false operand segment expected operand count {falseDest.getNumArguments! ctx.raw}, got {falseArgCount}"
  op.verifyBranchSuccessorArgTypes ctx fixedOperands trueDest s!"{instrName}: true successor"
  op.verifyBranchSuccessorArgTypes ctx (fixedOperands + trueArgCount) falseDest s!"{instrName}: false successor"

def OperationPtr.verifyRISCVimm12 (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (imm : Int) : Except String PUnit :=
  if imm < -2048 ∨ imm > 2047 then
    let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
    throw s!"{instrName} immediate out of bounds: must fit in a signed 12-bit field [-2048, 2047]"
  else
    pure ()

/--
  Check that a shift-amount/bit-index immediate fits in an unsigned 5-bit field
  `[0, 31]`. Used by the word-width (`*w`) shift and rotate instructions, whose
  shift amount operates on a 32-bit value.
-/
def OperationPtr.verifyRISCVuimm5 (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (imm : Int) : Except String PUnit :=
  if imm < 0 ∨ imm > 31 then
    let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
    throw s!"{instrName} immediate out of bounds: must fit in an unsigned 5-bit field [0, 31]"
  else
    pure ()

/--
  Check that a shift-amount/bit-index immediate fits in an unsigned 6-bit field
  `[0, 63]`. Used by the full-width (64-bit) shift, rotate, and single-bit
  instructions, whose immediate indexes a 64-bit register.
-/
def OperationPtr.verifyRISCVuimm6 (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (imm : Int) : Except String PUnit :=
  if imm < 0 ∨ imm > 63 then
    let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
    throw s!"{instrName} immediate out of bounds: must fit in an unsigned 6-bit field [0, 63]"
  else
    pure ()

def OperationPtr.verifyOperandTypesMatch (op : OperationPtr) (ctx : WfIRContext OpCode)
    (firstIdx secondIdx : Nat) (errMsg : String) : Except String TypeAttr := do
  let firstType := (op.getOperand! ctx.raw firstIdx).getType! ctx.raw
  let secondType := (op.getOperand! ctx.raw secondIdx).getType! ctx.raw
  if secondType.val ≠ firstType.val then
    throw errMsg
  pure firstType

def OperationPtr.verifyResultTypeMatches (op : OperationPtr) (ctx : WfIRContext OpCode)
    (expectedType : TypeAttr) (errMsg : String) : Except String PUnit := do
  if ((op.getResult 0).get! ctx.raw).type.val ≠ expectedType.val then
    throw errMsg

def OperationPtr.verifyIntegerBinopTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (instrName : String) : Except String PUnit := do
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 0 to have integer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 1 to have integer type"
  let operandType ← op.verifyOperandTypesMatch ctx 0 1 s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType s!"{instrName}: Expected result type to match operand type"

def OperationPtr.verifyICmpTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (instrName : String) : Except String PUnit := do
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 0 to have integer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 1 to have integer type"
  let _ ← op.verifyOperandTypesMatch ctx 0 1 s!"{instrName}: Expected operands to have the same type"
  ((op.getResult 0).get! ctx.raw).type.verifyI1 s!"{instrName}: Expected i1 result"

def OperationPtr.verifyLLVMICmpTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (instrName : String) : Except String PUnit := do
  -- `llvm.icmp` also compares pointers.
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerOrPointerType
    s!"{instrName}: Expected operand 0 to have integer or pointer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerOrPointerType
    s!"{instrName}: Expected operand 1 to have integer or pointer type"
  let _ ← op.verifyOperandTypesMatch ctx 0 1 s!"{instrName}: Expected operands to have the same type"
  ((op.getResult 0).get! ctx.raw).type.verifyI1 s!"{instrName}: Expected i1 result"

def OperationPtr.verifySelectTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (instrName : String) : Except String PUnit := do
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyI1 s!"{instrName}: Expected i1 condition"
  -- Both `arith.select` and `llvm.select` accept values of any type.
  let operandType ← op.verifyOperandTypesMatch ctx 1 2 s!"{instrName}: Expected select values to have the same type"
  op.verifyResultTypeMatches ctx operandType s!"{instrName}: Expected result type to match select value type"

def OperationPtr.verifyIntegerTruncTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (instrName : String) : Except String PUnit := do
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  let resultType := ((op.getResult 0).get! ctx.raw).type
  let .integerType operandInt := operandType.val
    | throw s!"{instrName}: Expected operand 0 to have integer type"
  let .integerType resultInt := resultType.val
    | throw s!"{instrName}: Expected integer result type"
  if operandInt.bitwidth ≤ resultInt.bitwidth then
    throw s!"{instrName}: Result's width must be smaller than operand's width"
  else
    pure ()

def OperationPtr.verifyIntegerExtTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (instrName : String) : Except String PUnit := do
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  let resultType := ((op.getResult 0).get! ctx.raw).type
  let .integerType operandInt := operandType.val
    | throw s!"{instrName}: Expected operand 0 to have integer type"
  let .integerType resultInt := resultType.val
    | throw s!"{instrName}: Expected integer result type"
  if resultInt.bitwidth ≤ operandInt.bitwidth then
    throw s!"{instrName}: Operand's width must be smaller than result's width"
  else
    pure ()

def OperationPtr.verifyRISCVneg (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (imm : Int) : Except String PUnit :=
  if imm < 0 ∨ 1048575 < imm then -- 1048575 = 2 ^ 20 - 1
    let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
    throw s!"{instrName} immediate out of bounds: must fit in a unsigned 20-bit field."
  else
    pure ()

/--
  Ensure that every operand and result of a RISC-V register instruction has
  type `!riscv.reg`. The caller is responsible for only invoking this on
  `.riscv` operations.
-/

def OperationPtr.verifyRISCVRegisterTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:opTypes.size] do
    match (opTypes[i]!).val with
    | .registerType _ => pure ()
    | _ => throw s!"{instrName}: Expected operand {i} to have !riscv.reg type"
  for i in [0:op.getNumResults ctx.raw opIn] do
    match ((op.getResult i).get! ctx.raw).type.val with
    | .registerType _ => pure ()
    | _ => throw s!"{instrName}: Expected result {i} to have !riscv.reg type"

/--
  Verify local invariants of an operation.
  This typically includes checking that the number of operands, successors, results, and regions
  match the expected values for the given operation type.
  This also checks that the given types are in bounds.
-/
def OperationPtr.verifyLocalInvariants (op : OperationPtr) (ctx : WfIRContext OpCode) (opIn : op.InBounds ctx.raw) : Except String PUnit :=
  match op.getOpType ctx.raw opIn with
  | .builtin .unregistered => pure ()
  | .builtin .unrealized_conversion_cast => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- ARITH -/
  | .arith .addi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.addi"
    pure ()
  | .arith .addui_extended => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 2 then
      throw "Expected 2 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith .andi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.andi"
    pure ()
  | .arith .ceildivsi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.ceildivsi"
    pure ()
  | .arith .ceildivui => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.ceildivui"
    pure ()
  | .arith .cmpi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyICmpTypes ctx "arith.cmpi"
    pure ()
   | .arith .constant => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    else if _ : op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    else if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    else if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    else if (op.getProperties! ctx.raw (.arith .constant)).value.type ≠
          ((op.getResult 0).get ctx.raw).type.val then
        throw "Expected result type to be equal to the constant's type"
    pure ()
  | .arith .divsi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.divsi"
    pure ()
  | .arith .divui => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.divui"
    pure ()
  | .arith .extui => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerExtTypes ctx "arith.extui"
    pure ()
  | .arith .extsi => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerExtTypes ctx "arith.extsi"
    pure ()
  | .arith .floordivsi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.floordivsi"
    pure ()
  | .arith .maxsi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.maxsi"
    pure ()
  | .arith .maxui => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.maxui"
    pure ()
  | .arith .minsi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.minsi"
    pure ()
  | .arith .minui => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.minui"
    pure ()
  | .arith .muli => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.muli"
    pure ()
  | .arith .mulsi_extended => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 2 then
      throw "Expected 2 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith .mului_extended => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 2 then
      throw "Expected 2 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith .ori => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.ori"
    pure ()
  | .arith .remsi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.remsi"
    pure ()
  | .arith .remui => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.remui"
    pure ()
  | .arith .select => do
    if op.getNumOperands ctx.raw opIn ≠ 3 then
      throw "Expected 3 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifySelectTypes ctx "arith.select"
    pure ()
  | .arith .shli => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.shli"
    pure ()
  | .arith .shrsi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.shrsi"
    pure ()
  | .arith .shrui => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.shrui"
    pure ()
  | .arith .subi => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.subi"
    pure ()
  | .arith .trunci => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerTruncTypes ctx "arith.trunci"
    pure ()
  | .arith .xori => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "arith.xori"
    pure ()
  | .builtin .module => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .datapath .compress => do
    if op.getNumOperands ctx.raw opIn ≤ op.getNumResults ctx.raw opIn then
      throw "Number of inputs must be greater than the number of results"
    if op.getNumResults ctx.raw opIn < 2 then
      throw "Expected at least 2 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .datapath .partial_product => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .datapath .pos_partial_product => do
    if op.getNumOperands ctx.raw opIn ≠ 3 then
      throw "Expected 3 operands"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- FUNC -/
  | .func .func => do
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .func .call => do
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .func .return => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyFuncReturnTypes ctx opIn
  /- CF -/
  | .cf .br => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 1 then
      throw "Expected 1 successor"
    pure ()
  | .cf .cond_br => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let weights := (op.getProperties! ctx.raw (OpCode.cf .cond_br)).branch_weights
    if weights.values.size ≠ 2 && weights.values.size ≠ 0 then
      throw "Expected 0 or 2 branch weights"
    let sizes := (op.getProperties! ctx.raw (OpCode.cf .cond_br)).operandSegmentSizes
    if _ : sizes.values.size ≠ 3 then
      throw "Expected 1 operand plus 2 variadic operands"
    if sizes.values[0]! ≠ 1 then
      throw "Expected 1 operand plus 2 variadic operands"
    pure ()
  /- TEST -/
  | .test .test => do
    pure ()
  /- LLVM -/
  | .llvm .mlir__constant => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    -- Unlike `arith.constant`, `llvm.mlir.constant` does not require the value
    -- attribute's type to match the result type exactly. An integer attribute
    -- only requires an integer result type of any width (e.g. a boolean constant
    -- may be written with a wider integer attribute). A float attribute requires
    -- a same-width float result, or a same-width integer result (the workaround
    -- for builtin MLIR float types without an LLVM equivalent).
    let resultType := ((op.getResult 0).get! ctx.raw).type.val
    match (op.getProperties! ctx.raw (.llvm .mlir__constant)).value with
    | .integer _ =>
      match resultType with
      | .integerType _ => pure ()
      | _ => throw "llvm.mlir.constant: Expected integer result type for an integer constant"
    | .float floatAttr =>
      match resultType with
      | .floatType floatType =>
        if floatType.bitwidth ≠ floatAttr.type.bitwidth then
          throw s!"llvm.mlir.constant: Expected float result type with bitwidth {floatAttr.type.bitwidth}"
      | .integerType intType =>
        if intType.bitwidth ≠ floatAttr.type.bitwidth then
          throw s!"llvm.mlir.constant: Expected integer result type with bitwidth {floatAttr.type.bitwidth}"
      | _ => throw "llvm.mlir.constant: Expected float or integer result type for a float constant"
    pure ()
  | .llvm .and => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.and"
    pure ()
  | .llvm .or => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.or"
    pure ()
  | .llvm .xor => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.xor"
    pure ()
  | .llvm .add => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.add"
    pure ()
  | .llvm .sub => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.sub"
    pure ()
  | .llvm .shl => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.shl"
    pure ()
  | .llvm .lshr => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.lshr"
    pure ()
  | .llvm .ashr => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.ashr"
    pure ()
  | .llvm .mul => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.mul"
    pure ()
  | .llvm .sdiv => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.sdiv"
    pure ()
  | .llvm .udiv => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.udiv"
    pure ()
  | .llvm .srem => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.srem"
    pure ()
  | .llvm .urem => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerBinopTypes ctx "llvm.urem"
    pure ()
  | .llvm .icmp => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyLLVMICmpTypes ctx "llvm.icmp"
    pure ()
  | .llvm .select => do
    if op.getNumOperands ctx.raw opIn ≠ 3 then
      throw "Expected 3 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifySelectTypes ctx "llvm.select"
    pure ()
  | .llvm .trunc => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerTruncTypes ctx "llvm.trunc"
    pure ()
  | .llvm .sext => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerExtTypes ctx "llvm.sext"
    pure ()
  | .llvm .zext => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyIntegerExtTypes ctx "llvm.zext"
    pure ()
  | .llvm .return => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyLLVMReturnTypes ctx opIn
  | .llvm .unreachable => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .br => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 1 then
      throw "Expected 1 successor"
    pure ()
  | .llvm .cond_br => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let weights := (op.getProperties! ctx.raw (.llvm .cond_br)).branch_weights
    if weights.values.size ≠ 2 && weights.values.size ≠ 0 then
      throw "Expected 0 or 2 branch weights"
    let sizes := (op.getProperties! ctx.raw (.llvm .cond_br)).operandSegmentSizes
    if _ : sizes.values.size ≠ 3 then
      throw "Expected 1 operand plus 2 variadic operands"
    if sizes.values[0]! ≠ 1 then
      throw "Expected 1 operand plus 2 variadic operands"
    pure ()
  | .llvm .alloca => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    let properties := (op.getProperties! ctx.raw (.llvm .alloca))
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.alloca' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"

    pure ()
  | .llvm .load => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    let properties := (op.getProperties! ctx.raw (.llvm .load))
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.load' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"

    pure ()
  | .llvm .store => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    let properties := (op.getProperties! ctx.raw (.llvm .store))
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.store' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"
    pure ()
  | .llvm .getelementptr => do
    let props := op.getProperties! ctx.raw (.llvm .getelementptr)
    let dynamicCount := props.rawConstantIndices.values.filter (· == -2147483648) |>.size
    if op.getNumOperands ctx.raw opIn ≠ 1 + dynamicCount then
      throw s!"Expected {1 + dynamicCount} operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .call => do
    if op.getNumResults ctx.raw opIn > 1 then
      throw "Expected at most 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .func => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .fadd | .llvm .fsub | .llvm .fmul | .llvm .fdiv | .llvm .frem => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .module_flags => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .freeze => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyResultTypeMatches ctx ((op.getOperand! ctx.raw 0).getType! ctx.raw)
      "llvm.freeze: Expected result type to match operand type"
    pure ()
  /- MOD_ARITH -/
  | .mod_arith .add => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .mod_arith .constant => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .mod_arith .mul => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .mod_arith .sub => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- RISCV -/
  | .riscv .li => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .lui => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVneg ctx opIn (op.getProperties! ctx.raw (.riscv .lui)).value.value
    pure ()
  | .riscv .auipc => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVneg ctx opIn (op.getProperties! ctx.raw (.riscv .auipc)).value.value
    pure ()
  | .riscv .addi => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .addi)).value.value
    pure ()
  | .riscv .slti => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .slti)).value.value
    pure ()
  | .riscv .sltiu => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .sltiu)).value.value
    pure ()
  | .riscv .andi => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .andi)).value.value
    pure ()
  | .riscv .ori => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .ori)).value.value
    pure ()
  | .riscv .xori => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .xori)).value.value
    pure ()
  | .riscv .addiw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .addiw)).value.value
    pure ()
  | .riscv .slli => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .slli)).value.value
    pure ()
  | .riscv .srli => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .srli)).value.value
    pure ()
  | .riscv .srai => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .srai)).value.value
    pure ()
  | .riscv .add => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sub => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sll => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .slt => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sltu => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .xor => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .srl => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sra => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .or => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .and => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .slliw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw (.riscv .slliw)).value.value
    pure ()
  | .riscv .srliw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw (.riscv .srliw)).value.value
    pure ()
  | .riscv .sraiw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw (.riscv .sraiw)).value.value
    pure ()
  | .riscv .addw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .subw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sllw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .srlw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sraw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rem => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .remu => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .remw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .remuw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mul => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mulh => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mulhu => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mulhsu => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mulw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .div => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .divw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .divu => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .divuw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .adduw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh1adduw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh2adduw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh3adduw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh1add => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh2add => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh3add => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .slliuw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .slliuw)).value.value
    pure ()
  | .riscv .andn => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .orn => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .xnor => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .max => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .maxu => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .min => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .minu => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rol => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .ror => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rolw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rorw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sextb => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sexth => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .zexth => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .clz => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .clzw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .ctz => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .ctzw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .cpop => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .cpopw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .orcb => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rev8 => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .roriw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw (.riscv .roriw)).value.value
    pure ()
  | .riscv .rori => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .rori)).value.value
    pure ()
  | .riscv .bclr => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .bext => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .binv => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .bset => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .bclri => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .bclri)).value.value
    pure ()
  | .riscv .bexti => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .bexti)).value.value
    pure ()
  | .riscv .binvi => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .binvi)).value.value
    pure ()
  | .riscv .bseti => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .bseti)).value.value
    pure ()
  | .riscv .pack => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .packh => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .packw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .ld | .riscv .lw | .riscv .lwu
  | .riscv .lh | .riscv .lhu | .riscv .lb | .riscv .lbu => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .ld)).value.value
    pure ()
  | .riscv .sd => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .sd)).value.value
    pure ()
  | .riscv .sw => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .sw)).value.value
    pure ()
  | .riscv .sh => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .sh)).value.value
    pure ()
  | .riscv .sb => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    op.verifyRISCVimm12 ctx opIn (op.getProperties! ctx.raw (.riscv .sb)).value.value
    pure ()
  | .riscv .mv => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .not => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .neg => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .negw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sextw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .zextb => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .zextw => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .seqz => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .snez => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sltz => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sgtz => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- RISCV CF -/
  | .riscv_cf .branch => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 1 then
      throw "Expected 1 successor"
    let dest := op.getSuccessor! ctx.raw 0
    if op.getNumOperands ctx.raw opIn ≠ dest.getNumArguments! ctx.raw then
      throw s!"RISCV branch expected operand count {dest.getNumArguments! ctx.raw}, got {op.getNumOperands ctx.raw opIn}"
    let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
    op.verifyBranchSuccessorArgTypes ctx 0 dest s!"{instrName}: successor"
    pure ()
  | .riscv_cf .beq => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .beq)).operandSegmentSizes
    op.verifyRISCVBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .bne => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bne)).operandSegmentSizes
    op.verifyRISCVBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .blt => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .blt)).operandSegmentSizes
    op.verifyRISCVBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .bge => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bge)).operandSegmentSizes
    op.verifyRISCVBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .bltu => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bltu)).operandSegmentSizes
    op.verifyRISCVBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .bgeu => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bgeu)).operandSegmentSizes
    op.verifyRISCVBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .beqz => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .beqz)).operandSegmentSizes
    op.verifyRISCVBranchOperandSegmentSizes ctx opIn sizes 1
    pure ()
  | .riscv_cf .bnez => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 2 then
      throw "Expected 2 successors"
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes
    op.verifyRISCVBranchOperandSegmentSizes ctx opIn sizes 1
    pure ()
  /- RISCV Stack -/
  | .riscv_stack .alloca => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- RISCV 64-bit -/
  | .rv64 .get_register => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- Comb -/
  | .comb .add | .comb .and | .comb .mul | .comb .or | .comb .xor => do
    if op.getNumOperands ctx.raw opIn < 1 then
      throw "Expected 1 or more operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .comb .concat => do
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .comb .divs | .comb .divu | .comb .icmp | .comb .mods | .comb .modu | .comb .shl
  | .comb .shrs | .comb .shru | .comb .sub => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .comb .extract | .comb .parity | .comb .replicate | .comb .reverse => do
    if op.getNumOperands ctx.raw opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .comb .mux => do
    if op.getNumOperands ctx.raw opIn ≠ 3 then
      throw "Expected 3 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- HW -/
  | .hw .constant => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .hw .module => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .hw .output => do
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()

/--
  Return the kind of this region.
-/
def RegionPtr.getRegionKind (region : RegionPtr) (ctx : WfIRContext OpCode) : RegionKind :=
  match (region.get! ctx.raw).parent with
  | some parentOp =>
    let parent := parentOp.get! ctx.raw
    parent.opType.getRegionKind (parent.regions.idxOf region)
  | none => .SSACFG

/--
  Verify that a terminator only ever appears as the last operation of its block:
  an operation that is a terminator must not be followed by another operation.
-/
def OperationPtr.verifyTerminatorPosition (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let operation := op.get ctx.raw opIn
  if operation.opType.isTerminator && operation.next.isSome then
    throw "Expected a terminator to be the last operation of its block"

/--
  Check that a block is non-empty and its last operation is a
  terminator.
-/
def BlockPtr.verifyTerminator (block : BlockPtr) (ctx : WfIRContext OpCode)
    (blockIn : block.InBounds ctx.raw) : Except String PUnit := do
  let b := block.get ctx.raw blockIn
  match b.lastOp with
  | none => throw "Expected the block to end in a terminator, but the block is empty"
  | some lastOp =>
    if !(lastOp.getOpType! ctx.raw).isTerminator then
      throw "Expected the last operation of a block to be a terminator"

public section

/--
  Verify that all operations in the IRContext satisfy their local invariants.
-/
def WfIRContext.verify (ctx : WfIRContext OpCode) : Except String Unit := do
  ctx.raw.forOpsDepM (fun op opIn => do
    op.verifyLocalInvariants ctx opIn
    if let .riscv _ := op.getOpType ctx.raw opIn then
      op.verifyRISCVRegisterTypes ctx opIn
    match (op.get ctx.raw opIn).parent with
    | some _ => op.verifyTerminatorPosition ctx opIn
    | none => pure ())
  ctx.raw.forBlocksDepM (fun block blockIn => do
    match (block.get ctx.raw blockIn).parent with
    | some region =>
      if region.getRegionKind ctx = .SSACFG then
        block.verifyTerminator ctx blockIn
    | none => pure ())

/--
Assert that all operations in the IRContext satisfy their local invariants.
-/
def WfIRContext.Verified (ctx : WfIRContext OpCode) : Prop :=
  ctx.verify = .ok ()

/--
Assert that a given operation satisfies its local invariants.
-/
def OperationPtr.Verified (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds ctx.raw := by grind) : Prop :=
  op.verifyLocalInvariants ctx opInBounds = .ok ()

set_option warn.sorry false in
/--
If the context satisfies the invariants of all operations, any operation in bounds is verified.
-/
@[grind →]
theorem OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants {ctx : WfIRContext OpCode} {op : OperationPtr}
    (ctxVerify : ctx.Verified) (opInBounds : op.InBounds ctx.raw := by grind) :
    op.Verified ctx opInBounds := by
  sorry -- This requires to reason about `IRContext.forOpsDepM`.

/-!
## Lemmas for verified operations

These are the lemmas that give the information about the structure of verified operations.
There is one lemma per operation, and they are all of the same form: given that an operation
satisfies its local invariants, we can conclude that it has the expected number of operands,
results, regions, and successors, and that the types of its operands and results are as expected.
-/

theorem OperationPtr.Verified.arith_constant {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .constant) :
    op.getNumResults! ctx.raw = 1 ∧
    op.getNumOperands! ctx.raw = 0 ∧
    op.getNumSuccessors! ctx.raw = 0 ∧
    op.getNumRegions! ctx.raw = 0 ∧
    ((op.getResult 0).get! ctx.raw).type =
      ⟨(op.getProperties! ctx.raw (.arith .constant)).value.type, (by grind)⟩ := by
  simp only [Verified, verifyLocalInvariants, ← getOpType!_eq_getOpType, opType, ne_eq,
    bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, dite_not,
    ite_not] at opVerify
  simp only [TypeAttr.inj]
  grind

theorem OperationPtr.Verified.arith_addi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .addi) :
    op.getNumResults! ctx.raw = 1 ∧
    op.getNumOperands! ctx.raw = 2 ∧
    op.getNumSuccessors! ctx.raw = 0 ∧
    op.getNumRegions! ctx.raw = 0 ∧
    ∃ integerType,
      ((op.getResult 0).get! ctx.raw).type = ⟨.integerType integerType, (by grind)⟩ ∧
      ((op.getOperand! ctx.raw 0).getType! ctx.raw) = ⟨.integerType integerType, (by grind)⟩ ∧
      ((op.getOperand! ctx.raw 1).getType! ctx.raw) = ⟨.integerType integerType, (by grind)⟩ := by
  simp only [Verified, verifyLocalInvariants, ← getOpType!_eq_getOpType, opType, ne_eq,
    verifyIntegerBinopTypes, verifyOperandTypesMatch, verifyResultTypeMatches,
    TypeAttr.verifyIntegerType, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure, ite_not] at opVerify
  simp only [TypeAttr.inj]
  grind

end
end Veir
