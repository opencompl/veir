module

public import Veir.IR.Basic
public import Veir.IR.Dominance
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
  Verify the operand and result counts of a "plain" operation: one that has no
  regions and no successors. The instruction name is included in each error
  message.
-/
def OperationPtr.verifyPlainOpCounts (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (operands results : Nat) : Except String PUnit := do
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  if op.getNumOperands ctx.raw opIn ≠ operands then
    throw s!"{instrName}: Expected {operands} operand(s)"
  if op.getNumResults ctx.raw opIn ≠ results then
    throw s!"{instrName}: Expected {results} result(s)"
  if op.getNumRegions ctx.raw opIn ≠ 0 then
    throw s!"{instrName}: Expected 0 regions"
  if op.getNumSuccessors ctx.raw opIn ≠ 0 then
    throw s!"{instrName}: Expected 0 successors"

/--
  Verify the result, region, and successor counts of a terminator: one that
  produces no results, has no regions, and transfers control to `successors`
  successor blocks. The operand count is left to the caller, since terminators
  are typically variadic in their forwarded arguments. The instruction name is
  included in each error message.
-/
def OperationPtr.verifyTerminatorCounts (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (successors : Nat) : Except String PUnit := do
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  if op.getNumResults ctx.raw opIn ≠ 0 then
    throw s!"{instrName}: Expected 0 results"
  if op.getNumRegions ctx.raw opIn ≠ 0 then
    throw s!"{instrName}: Expected 0 regions"
  if op.getNumSuccessors ctx.raw opIn ≠ successors then
    throw s!"{instrName}: Expected {successors} successor(s)"

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

/--
  Verify an unconditional branch with a single successor: every operand is
  forwarded positionally to the successor block's arguments, so the operand
  count must equal the successor's argument count and the operand types must
  match the block argument types.
-/
def OperationPtr.verifyUnconditionalBranch (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyTerminatorCounts ctx opIn 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  let dest := op.getSuccessor! ctx.raw 0
  if op.getNumOperands ctx.raw opIn ≠ dest.getNumArguments! ctx.raw then
    throw s!"{instrName}: branch expected operand count {dest.getNumArguments! ctx.raw}, got {op.getNumOperands ctx.raw opIn}"
  op.verifyBranchSuccessorArgTypes ctx 0 dest s!"{instrName}: successor"

def OperationPtr.verifyCondBranchOperandSegmentSizes
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
    (opIn : op.InBounds ctx.raw) (operands results : Nat) (imm : Int) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn operands results
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
    (opIn : op.InBounds ctx.raw) (imm : Int) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
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
    (opIn : op.InBounds ctx.raw) (imm : Int) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
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

def OperationPtr.verifyIntegerBinop (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 0 to have integer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 1 to have integer type"
  let operandType ← op.verifyOperandTypesMatch ctx 0 1 s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType s!"{instrName}: Expected result type to match operand type"

def OperationPtr.verifyIntegerTernop (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 3 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 0 to have integer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 1 to have integer type"
  ((op.getOperand! ctx.raw 2).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 2 to have integer type"
  let _ ← op.verifyOperandTypesMatch ctx 0 1 s!"{instrName}: Expected operands to have the same type"
  let operandType ← op.verifyOperandTypesMatch ctx 0 2 s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType s!"{instrName}: Expected result type to match operand type"

def OperationPtr.verifyIntegerUnop (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String TypeAttr := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  operandType.verifyIntegerType s!"{instrName}: Expected operand 0 to have integer type"
  op.verifyResultTypeMatches ctx operandType s!"{instrName}: Expected result type to match operand type"
  pure operandType

def OperationPtr.verifyICmp (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 0 to have integer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 1 to have integer type"
  let _ ← op.verifyOperandTypesMatch ctx 0 1 s!"{instrName}: Expected operands to have the same type"
  ((op.getResult 0).get! ctx.raw).type.verifyI1 s!"{instrName}: Expected i1 result"

def OperationPtr.verifyLLVMICmp (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  -- `llvm.icmp` also compares pointers.
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerOrPointerType
    s!"{instrName}: Expected operand 0 to have integer or pointer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerOrPointerType
    s!"{instrName}: Expected operand 1 to have integer or pointer type"
  let _ ← op.verifyOperandTypesMatch ctx 0 1 s!"{instrName}: Expected operands to have the same type"
  ((op.getResult 0).get! ctx.raw).type.verifyI1 s!"{instrName}: Expected i1 result"

def OperationPtr.verifySelectTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 3 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyI1 s!"{instrName}: Expected i1 condition"
  -- Both `arith.select` and `llvm.select` accept values of any type.
  let operandType ← op.verifyOperandTypesMatch ctx 1 2 s!"{instrName}: Expected select values to have the same type"
  op.verifyResultTypeMatches ctx operandType s!"{instrName}: Expected result type to match select value type"

def OperationPtr.verifyIntegerTruncTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
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
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
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
    (opIn : op.InBounds ctx.raw) (operands results : Nat) (imm : Int) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn operands results
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
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()
  /- ARITH -/
  | .arith .addi | .arith .andi | .arith .ceildivsi | .arith .ceildivui
  | .arith .divsi | .arith .divui | .arith .floordivsi | .arith .maxsi
  | .arith .maxui | .arith .minsi | .arith .minui | .arith .muli
  | .arith .ori | .arith .remsi | .arith .remui | .arith .shli
  | .arith .shrsi | .arith .shrui | .arith .subi | .arith .xori => do
    op.verifyIntegerBinop ctx opIn
    pure ()
  | .arith .addui_extended | .arith .mulsi_extended | .arith .mului_extended => do
    op.verifyPlainOpCounts ctx opIn 2 2
    pure ()
  | .arith .cmpi => do
    op.verifyICmp ctx opIn
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
  | .arith .extui | .arith .extsi => do
    op.verifyIntegerExtTypes ctx opIn
    pure ()
  | .arith .select => do
    op.verifySelectTypes ctx opIn
    pure ()
  | .arith .trunci => do
    op.verifyIntegerTruncTypes ctx opIn
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
    op.verifyTerminatorCounts ctx opIn 0
    op.verifyFuncReturnTypes ctx opIn
  /- CF -/
  | .cf .br => do
    op.verifyUnconditionalBranch ctx opIn
  | .cf .cond_br => do
    op.verifyTerminatorCounts ctx opIn 2
    let weights := (op.getProperties! ctx.raw (OpCode.cf .cond_br)).branch_weights
    if weights.values.size ≠ 2 && weights.values.size ≠ 0 then
      throw "Expected 0 or 2 branch weights"
    let sizes := (op.getProperties! ctx.raw (OpCode.cf .cond_br)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 1
  /- TEST -/
  | .test .test => do
    pure ()
  /- LLVM -/
  | .llvm .mlir__constant => do
    op.verifyPlainOpCounts ctx opIn 0 1
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
  | .llvm .mlir__poison => do
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()
  | .llvm .and | .llvm .or | .llvm .xor | .llvm .intr__smax | .llvm .intr__smin
  | .llvm .intr__umax | .llvm .intr__umin | .llvm .add | .llvm .sub | .llvm .shl
  | .llvm .lshr | .llvm .ashr | .llvm .mul | .llvm .sdiv | .llvm .udiv
  | .llvm .srem | .llvm .urem => do
    op.verifyIntegerBinop ctx opIn
    pure ()
  | .llvm .intr__fshl | .llvm .intr__fshr => do
    op.verifyIntegerTernop ctx opIn
    pure ()
  | .llvm .intr__ctlz | .llvm .intr__cttz | .llvm .intr__ctpop
  | .llvm .intr__bitreverse => do
    let _ ← op.verifyIntegerUnop ctx opIn
    pure ()
  | .llvm .intr__bswap => do
    let operandType ← op.verifyIntegerUnop ctx opIn
    let .integerType intType := operandType.val
      | throw "llvm.intr.bswap: Expected operand 0 to have integer type"
    if intType.bitwidth ∉ [16, 32, 64] then
      throw "llvm.intr.bswap: bitwidth must be 16, 32, or 64"
    pure ()
  | .llvm .icmp => do
    op.verifyLLVMICmp ctx opIn
    pure ()
  | .llvm .select => do
    op.verifySelectTypes ctx opIn
    pure ()
  | .llvm .trunc => do
    op.verifyIntegerTruncTypes ctx opIn
    pure ()
  | .llvm .sext | .llvm .zext => do
    op.verifyIntegerExtTypes ctx opIn
    pure ()
  | .llvm .return => do
    op.verifyTerminatorCounts ctx opIn 0
    op.verifyLLVMReturnTypes ctx opIn
  | .llvm .unreachable => do
    op.verifyPlainOpCounts ctx opIn 0 0
    pure ()
  | .llvm .br => do
    op.verifyUnconditionalBranch ctx opIn
  | .llvm .cond_br => do
    op.verifyTerminatorCounts ctx opIn 2
    let weights := (op.getProperties! ctx.raw (.llvm .cond_br)).branch_weights
    if weights.values.size ≠ 2 && weights.values.size ≠ 0 then
      throw "Expected 0 or 2 branch weights"
    let sizes := (op.getProperties! ctx.raw (.llvm .cond_br)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 1
  | .llvm .alloca => do
    op.verifyPlainOpCounts ctx opIn 1 1
    let properties := (op.getProperties! ctx.raw (.llvm .alloca))
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.alloca' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"

    pure ()
  | .llvm .load => do
    op.verifyPlainOpCounts ctx opIn 1 1
    let properties := (op.getProperties! ctx.raw (.llvm .load))
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.load' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"

    pure ()
  | .llvm .store => do
    op.verifyPlainOpCounts ctx opIn 2 0
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
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .llvm .module_flags => do
    op.verifyPlainOpCounts ctx opIn 0 0
    pure ()
  | .llvm .freeze => do
    op.verifyPlainOpCounts ctx opIn 1 1
    op.verifyResultTypeMatches ctx ((op.getOperand! ctx.raw 0).getType! ctx.raw)
      "llvm.freeze: Expected result type to match operand type"
    pure ()
  /- MOD_ARITH -/
  | .mod_arith .add | .mod_arith .mul | .mod_arith .sub => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .mod_arith .constant => do
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()
  /- RISCV -/
  | .riscv .li => do
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()
  | .riscv .lui => do
    op.verifyRISCVneg ctx opIn 0 1 (op.getProperties! ctx.raw (.riscv .lui)).value.value
    pure ()
  | .riscv .auipc => do
    op.verifyRISCVneg ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .auipc)).value.value
    pure ()
  | .riscv .addi => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .addi)).value.value
    pure ()
  | .riscv .slti => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .slti)).value.value
    pure ()
  | .riscv .sltiu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .sltiu)).value.value
    pure ()
  | .riscv .andi => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .andi)).value.value
    pure ()
  | .riscv .ori => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .ori)).value.value
    pure ()
  | .riscv .xori => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .xori)).value.value
    pure ()
  | .riscv .addiw => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .addiw)).value.value
    pure ()
  | .riscv .slli => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .slli)).value.value
    pure ()
  | .riscv .srli => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .srli)).value.value
    pure ()
  | .riscv .srai => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .srai)).value.value
    pure ()
  | .riscv .add | .riscv .sub | .riscv .sll | .riscv .slt | .riscv .sltu
  | .riscv .xor | .riscv .srl | .riscv .sra | .riscv .or | .riscv .and => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .riscv .slliw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw (.riscv .slliw)).value.value
    pure ()
  | .riscv .srliw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw (.riscv .srliw)).value.value
    pure ()
  | .riscv .sraiw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw (.riscv .sraiw)).value.value
    pure ()
  | .riscv .addw | .riscv .subw | .riscv .sllw | .riscv .srlw | .riscv .sraw
  | .riscv .rem | .riscv .remu | .riscv .remw | .riscv .remuw
  | .riscv .mul | .riscv .mulh | .riscv .mulhu | .riscv .mulhsu | .riscv .mulw
  | .riscv .div | .riscv .divw | .riscv .divu | .riscv .divuw
  | .riscv .adduw | .riscv .sh1adduw | .riscv .sh2adduw | .riscv .sh3adduw
  | .riscv .sh1add | .riscv .sh2add | .riscv .sh3add => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .riscv .slliuw => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .slliuw)).value.value
    pure ()
  | .riscv .andn | .riscv .orn | .riscv .xnor
  | .riscv .max | .riscv .maxu | .riscv .min | .riscv .minu
  | .riscv .rol | .riscv .ror | .riscv .rolw | .riscv .rorw => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .riscv .sextb | .riscv .sexth | .riscv .zexth
  | .riscv .clz | .riscv .clzw | .riscv .ctz | .riscv .ctzw
  | .riscv .cpop | .riscv .cpopw | .riscv .orcb | .riscv .rev8 => do
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()
  | .riscv .roriw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw (.riscv .roriw)).value.value
    pure ()
  | .riscv .rori => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .rori)).value.value
    pure ()
  | .riscv .bclr | .riscv .bext | .riscv .binv | .riscv .bset => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .riscv .bclri => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .bclri)).value.value
    pure ()
  | .riscv .bexti => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .bexti)).value.value
    pure ()
  | .riscv .binvi => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .binvi)).value.value
    pure ()
  | .riscv .bseti => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw (.riscv .bseti)).value.value
    pure ()
  | .riscv .pack | .riscv .packh | .riscv .packw
  | .riscv .czeroeqz | .riscv .czeronez => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .riscv .ld => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .ld)).value.value
    pure ()
  | .riscv .lw => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .lw)).value.value
    pure ()
  | .riscv .lwu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .lwu)).value.value
    pure ()
  | .riscv .lh => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .lh)).value.value
    pure ()
  | .riscv .lhu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .lhu)).value.value
    pure ()
  | .riscv .lb => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .lb)).value.value
    pure ()
  | .riscv .lbu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw (.riscv .lbu)).value.value
    pure ()
  | .riscv .sd => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw (.riscv .sd)).value.value
    pure ()
  | .riscv .sw => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw (.riscv .sw)).value.value
    pure ()
  | .riscv .sh => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw (.riscv .sh)).value.value
    pure ()
  | .riscv .sb => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw (.riscv .sb)).value.value
    pure ()
  | .riscv .mv | .riscv .not | .riscv .neg | .riscv .negw | .riscv .sextw
  | .riscv .zextb | .riscv .zextw | .riscv .seqz | .riscv .snez
  | .riscv .sltz | .riscv .sgtz => do
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()
  /- RISCV CF -/
  | .riscv_cf .branch => do
    op.verifyUnconditionalBranch ctx opIn
  | .riscv_cf .beq => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .beq)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .bne => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bne)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .blt => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .blt)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .bge => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bge)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .bltu => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bltu)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .bgeu => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bgeu)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .riscv_cf .beqz => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .beqz)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 1
    pure ()
  | .riscv_cf .bnez => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 1
    pure ()
  /- RISCV Stack -/
  | .riscv_stack .alloca => do
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()
  /- RISCV 64-bit -/
  | .rv64 .get_register => do
    op.verifyPlainOpCounts ctx opIn 0 1
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
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .comb .extract | .comb .parity | .comb .replicate | .comb .reverse => do
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()
  | .comb .mux => do
    op.verifyPlainOpCounts ctx opIn 3 1
    pure ()
  /- HW -/
  | .hw .constant => do
    op.verifyPlainOpCounts ctx opIn 0 1
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
    op.verifyTerminatorCounts ctx opIn 0
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
  Verify that no operation branches to the entry block of a region. The entry
  block of a region may not have predecessors: it is the unique block that the
  region is entered through, and dominance assumes it dominates every other block
  in the region.
-/
def OperationPtr.verifyDoesNotBranchToEntryBlock (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  for succ in op.getSuccessors ctx.raw opIn do
    match (succ.get! ctx.raw).parent with
    | some region =>
      if (region.get! ctx.raw).firstBlock = some succ then
        throw "entry block of a region may not have predecessors"
    | none => pure ()

/--
  Verify that every successor of an operation lies in the same region as the
  operation itself. Control flow may not branch out of its enclosing region.

  This cannot be expressed in the textual format (block labels are region-scoped,
  so the parser already rejects a reference to a block in another region), but it
  guards against passes that build malformed cross-region control flow.
-/
def OperationPtr.verifySuccessorsInSameRegion (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match (op.get ctx.raw opIn).parent with
  | none => pure ()
  | some block =>
    let blockRegion := (block.get! ctx.raw).parent
    for succ in op.getSuccessors ctx.raw opIn do
      if (succ.get! ctx.raw).parent ≠ blockRegion then
        throw "branching to a block of a different region"

/--
  Verify that graph regions of registered operations contain at most one block.
  Like MLIR, this restriction limits the cases transforms must handle; it applies
  only to registered operations, so unregistered ops and the test dialect may
  still use multi-block graph regions.
-/
def OperationPtr.verifyGraphRegionBlockCount (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let opCode := op.getOpType ctx.raw opIn
  match opCode with
  | .builtin .unregistered | .test .test => pure ()
  | _ =>
    for i in [0:op.getNumRegions ctx.raw opIn] do
      if opCode.getRegionKind i = .Graph then
        match (op.getRegion! ctx.raw i |>.get! ctx.raw).firstBlock with
        | some b =>
          if (b.get! ctx.raw).next.isSome then
            throw s!"expects graph region {i} to have 0 or 1 blocks"
        | none => pure ()

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

def ValuePtr.dominatesBeforeOp?
    (value : ValuePtr) (useOp : OperationPtr)
    (dfCtx : DataFlowContext) (ctx : IRContext OpCode) : Bool :=
  match value with
  | .opResult result =>
      OperationPtr.properlyDominatesByAnalysis result.op useOp dfCtx ctx
  | .blockArgument arg =>
      match (useOp.get! ctx).parent with
      | some useBlock => BlockPtr.dominatesByAnalysis arg.block useBlock dfCtx ctx
      | none => false

def OperationPtr.verifyOperandDominance
    (op : OperationPtr) (ctx : WfIRContext OpCode)
    (dfCtx : DataFlowContext) (opIn : op.InBounds ctx.raw) :
    Except String PUnit := do
  -- The SSA dominance constraint only applies inside SSACFG regions and, as in
  -- LLVM/MLIR, only to uses in blocks reachable from the region entry. Operands
  -- used in graph regions or in unreachable code impose no dominance requirement;
  -- the analysis records no dominator fact for unreachable blocks (whereas the
  -- entry block has a fact with no immediate dominator).
  let shouldCheck : Bool := Id.run do
    let some useBlock := (op.get ctx.raw opIn).parent | return false
    let some region := (useBlock.get! ctx.raw).parent | return false
    let .SSACFG := region.getRegionKind ctx | return false
    return (useBlock.getDominatorFact? dfCtx ctx.raw).isSome
  if shouldCheck then
    let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
    for i in [0:op.getNumOperands ctx.raw opIn] do
      let value := op.getOperand! ctx.raw i
      if !value.dominatesBeforeOp? op dfCtx ctx.raw then
        throw s!"{instrName}: operand {i} ({reprStr value}) does not dominate its use in operation {reprStr op}"

/--
  Dynamically check the SSA dominance condition used by `ctx.Dom`: every ordinary operation
  operand must dominate the point immediately before the operation that uses it.

  This is intentionally an executable checker. It does not yet provide a Lean proof of
  `ctx.Dom`, but its algorithm is structured to match that property.
-/
def WfIRContext.verifyDominance
    (ctx : WfIRContext OpCode) (top : OperationPtr) : Except String Unit := do
  if _ : top.InBounds ctx.raw then
    let some dfCtx := fixpointSolve top #[DominanceAnalysis] ctx.raw
      | throw "dominance analysis did not terminate"
    ctx.raw.forOpsDepM fun op opIn =>
      op.verifyOperandDominance ctx dfCtx opIn
  else
    throw s!"dominance root operation is not in bounds: {reprStr top}"

public section

/--
  Verify that all operations in the IRContext satisfy their local invariants. If `top?` is
  provided, also run the dynamic SSA dominance checker rooted at that operation.
-/
def WfIRContext.verify (ctx : WfIRContext OpCode)
    (top? : Option OperationPtr := none) : Except String Unit := do
  ctx.raw.forOpsDepM (fun op opIn => do
    op.verifyLocalInvariants ctx opIn
    if let .riscv _ := op.getOpType ctx.raw opIn then
      op.verifyRISCVRegisterTypes ctx opIn
    match (op.get ctx.raw opIn).parent with
    | some _ => op.verifyTerminatorPosition ctx opIn
    | none => pure ()
    op.verifyDoesNotBranchToEntryBlock ctx opIn
    op.verifySuccessorsInSameRegion ctx opIn
    op.verifyGraphRegionBlockCount ctx opIn)
  ctx.raw.forBlocksDepM (fun block blockIn => do
    match (block.get ctx.raw blockIn).parent with
    | some region =>
      if region.getRegionKind ctx = .SSACFG then
        block.verifyTerminator ctx blockIn
    | none => pure ())
  match top? with
  | some top => ctx.verifyDominance top
  | none => pure ()

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
    verifyIntegerBinop, verifyPlainOpCounts, verifyOperandTypesMatch, verifyResultTypeMatches,
    TypeAttr.verifyIntegerType, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure, ite_not] at opVerify
  simp only [TypeAttr.inj]
  grind

end
end Veir
