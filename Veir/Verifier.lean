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
    (opName : String) : Except String OperationPtr :=
  match op.getParentOp! ctx.raw with
  | some funcOp => pure funcOp
  | none => throw s!"Expected {opName} to have an enclosing function operation"

/-- Read a function op's declared `function_type`. `func.func` keeps it in `extra`;
    `llvm.func` has a first-class `function_type` field. -/
public def readFunctionType? (raw : IRContext OpCode) (funcOp : OperationPtr) :
    Option FunctionType :=
  match funcOp.getOpType! raw with
  | .func .func =>
    match (funcOp.getProperties! raw (.func .func) : FuncFuncProperties).extra.entries.find?
        (fun e => e.1 == "function_type".toUTF8) with
    | some (_, .functionType ft) => some ft
    | _ => none
  | .llvm .func =>
    match (funcOp.getProperties! raw (.llvm .func) : LLVMFuncProperties).function_type with
    | some ta =>
      match ta.val with
      | .functionType ft | .llvmFunctionType ft => some ft
      | _ => none
    | none => none
  | _ => none

/--
  Type compatibility for matching an actual value's type against a declared type.
  Register types are compatible when their register constraints agree, treating an
  unconstrained `!riscv.reg` (no index) as matching any physical register such as
  `!riscv.reg<x0>`. This lets a hard-wired register like `x0` be forwarded into a
  generic register slot, whether that's a successor block argument (see
  `verifyBranchSuccessorArgTypes`) or a function return value. All other types must
  be equal.
-/
def Attribute.branchArgCompatible (opTy argTy : Attribute) : Bool :=
  match opTy, argTy with
  | .registerType r1, .registerType r2 =>
      decide (r1.index = r2.index) || r1.index.isNone || r2.index.isNone
  | _, _ => decide (opTy = argTy)

/--
  Check that a `func.return` returns the declared result types of its
  enclosing `func.func`.
-/
def OperationPtr.verifyFuncReturnTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let funcOp ← op.getEnclosingFunctionOp ctx "func.return"
  let .func .func := funcOp.getOpType! ctx.raw
    | throw "Expected func.return to be enclosed by func.func"
  let some ft := readFunctionType? ctx.raw funcOp
    | throw "Expected enclosing func.func to have a function_type attribute"
  let outputs := ft.outputs
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected func.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if !Attribute.branchArgCompatible (opTypes[i]!).val outputs[i]! then
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
  let some ft := readFunctionType? ctx.raw funcOp
    | throw "Expected enclosing llvm.func to have a function_type attribute"
  -- A single `llvm.void` result corresponds to no return operands.
  let outputs := match ft.outputs with
    | #[.llvmVoidType _] => #[]
    | outputs => outputs
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected llvm.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if !Attribute.branchArgCompatible (opTypes[i]!).val outputs[i]! then
      throw s!"llvm.return operand {i} type does not match the function's declared result type"

def TypeAttr.verifyIntegerType (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .integerType _ => pure ()
  | _ => throw errMsg

def TypeAttr.verifyIntegerOrByteType (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .integerType _ => pure ()
  | .byteType _ => pure ()
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
    if !Attribute.branchArgCompatible opTy.val argTy.val then
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

def OperationPtr.verifyLLVMShift (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerOrByteType s!"{instrName}: Expected operand 0 to have integer or byte type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 1 to have integer type"
  op.verifyResultTypeMatches ctx ((op.getOperand! ctx.raw 0).getType! ctx.raw) s!"{instrName}: Expected result type to match first operand type"

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

def OperationPtr.verifyTruncTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (allowByte : Bool) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  let resultType := ((op.getResult 0).get! ctx.raw).type
  match operandType.val, resultType.val, allowByte with
  | .integerType ⟨bw1⟩, .integerType ⟨bw2⟩, _ =>
    if bw1 ≤ bw2 then
      throw s!"{instrName}: Result's width must be smaller than operand's width"
    else
      pure ()
  | .byteType ⟨bw1⟩, .byteType ⟨bw2⟩, true =>
    if bw1 ≤ bw2 then
      throw s!"{instrName}: Result's width must be smaller than operand's width"
    else
      pure ()
  | _, _, _ => throw s!"{instrName}: Expected 1 integer operand and 1 integer result"

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

def TypeAttr.verifyModArithType (ty : TypeAttr) (msg : String): Except String ModArithType :=
  match ty.val with
  | .modArithType type => do
    let modulus := type.modulus.value
    let bitWidth := type.modulus.type.bitwidth
    if modulus ≤ 0 then
      throw s!"{msg} but found invalid ModArithType type: modulus {modulus} must be positive."
    if modulus ≥ (2 ^ bitWidth) then
      throw s!"{msg} but found invalid ModArithType type: modulus {modulus} does not fit into the underlying storage type 'i{bitWidth}'."
    pure type
  | type => throw s!"{msg} but found {type} instead."

def OperationPtr.verifyModArithBinOp (op : OperationPtr) (ctx: WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
    op.verifyPlainOpCounts ctx opIn 2 1
    let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
    let operandType ← op.verifyOperandTypesMatch ctx 0 1 s!"{instrName}: Expected operands to have the same type"
    op.verifyResultTypeMatches ctx operandType s!"{instrName}: Expected result type to match operand type"
    let _ ← operandType.verifyModArithType s!"{instrName}: Expected ModArithType"

def OperationPtr.verifyModArithConstantOp (op : OperationPtr) (ctx: WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
    op.verifyPlainOpCounts ctx opIn 0 1
    let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
    let mat ← ((op.getResult 0).get! ctx.raw).type.verifyModArithType s!"{instrName}: Expected result to have ModArithType"
    let value := (op.getProperties! ctx.raw (.mod_arith .constant)).value.value
    let bw := mat.modulus.type.bitwidth
    -- slightly odd range because the storage type is signless
    if value < -(2 ^ (bw - 1) : Int) ∨ (2 ^ bw : Int) ≤ value then
      throw s!"{instrName}: constant value {value} does not fit in storage type 'i{bw}'."


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
    op.verifyTruncTypes ctx opIn false
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
    | .dense _ =>
      match resultType with
      | .llvmArrayType _ => pure ()
      | _ => throw "llvm.mlir.constant: Expected array result type for a dense elements constant"
    pure ()
  | .llvm .mlir__poison => do
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()
  | .llvm .and | .llvm .or | .llvm .xor | .llvm .intr__smax | .llvm .intr__smin
  | .llvm .intr__umax | .llvm .intr__umin | .llvm .add | .llvm .sub
  | .llvm .ashr | .llvm .mul | .llvm .sdiv | .llvm .udiv
  | .llvm .srem | .llvm .urem
  | .llvm .intr__sadd__sat | .llvm .intr__uadd__sat
  | .llvm .intr__ssub__sat | .llvm .intr__usub__sat
  | .llvm .intr__sshl__sat | .llvm .intr__ushl__sat => do
    op.verifyIntegerBinop ctx opIn
    pure ()
  | .llvm .lshr | .llvm .shl => do
    op.verifyLLVMShift ctx opIn
    pure ()
  | .llvm .intr__abs => do
    let _ ← op.verifyIntegerUnop ctx opIn
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
    op.verifyTruncTypes ctx opIn true
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
  | .llvm .bitcast => do
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()
  /- MOD_ARITH -/
  | .mod_arith .add | .mod_arith .mul | .mod_arith .sub => do
    op.verifyModArithBinOp ctx opIn
    pure ()
  | .mod_arith .constant => do
    op.verifyModArithConstantOp ctx opIn
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

/--
If the context satisfies the invariants of all operations, any operation in bounds is verified.
-/
@[grind →]
axiom OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants {ctx : WfIRContext OpCode}
    {op : OperationPtr} (ctxVerify : ctx.Verified) (opInBounds : op.InBounds ctx.raw := by grind) :
    op.Verified ctx opInBounds

/-!
## Lemmas for verified operations

These are the lemmas that give the information about the structure of verified operations.
There is one lemma per operation, and they are all of the same form: given that an operation
satisfies its local invariants, we can conclude that it has the expected number of operands,
results, regions, and successors, and that the types of its operands and results are as expected.
-/

/--
  The structural facts shared by every integer binary operation: exactly 2 operands and 1 result,
  no regions or successors, and both operands and the result share a single integer type.
-/
def OperationPtr.IsVerifiedIntegerBinop (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 2 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ integerType,
    ((op.getResult 0).get! ctx.raw).type = ⟨.integerType integerType, (by grind)⟩ ∧
    ((op.getOperand! ctx.raw 0).getType! ctx.raw) = ⟨.integerType integerType, (by grind)⟩ ∧
    ((op.getOperand! ctx.raw 1).getType! ctx.raw) = ⟨.integerType integerType, (by grind)⟩

/--
  Structural facts extracted from a successful `verifyIntegerBinop` check. This is the shared
  core behind every integer binary operation's `Verified.*` lemma.
-/
private theorem OperationPtr.verifyIntegerBinop_eq_ok {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (h : op.verifyIntegerBinop ctx opInBounds = .ok ()) :
    op.IsVerifiedIntegerBinop ctx := by
  simp only [IsVerifiedIntegerBinop, verifyIntegerBinop, verifyPlainOpCounts,
    verifyOperandTypesMatch, verifyResultTypeMatches, TypeAttr.verifyIntegerType, ne_eq, bind,
    Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h ⊢
  simp only [TypeAttr.inj]
  grind

/--
  Reduce a verified integer binary operation to a successful `verifyIntegerBinop` check.
  The hypothesis `armReduces` says the operation's local-invariant check is exactly the
  `verifyIntegerBinop` arm; it is discharged per operation by unfolding the dispatcher at the
  concrete opcode.
-/
private theorem OperationPtr.verifyIntegerBinop_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.verifyIntegerBinop ctx opInBounds >>= fun _ => pure ())) :
    op.verifyIntegerBinop ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  cases hb : op.verifyIntegerBinop ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

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

/--
  Every integer binary operation's `Verified.*` lemma: given that the operation is verified and
  has the given binary-operation opcode, it satisfies `IsVerifiedIntegerBinop`. Each is a thin
  wrapper that reduces `op.Verified` to a successful `verifyIntegerBinop` and applies the
  workhorse `verifyIntegerBinop_eq_ok`.
-/
private theorem OperationPtr.Verified.integerBinop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.verifyIntegerBinop ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedIntegerBinop ctx :=
  op.verifyIntegerBinop_eq_ok <| op.verifyIntegerBinop_ok_of_Verified opVerify armReduces

theorem OperationPtr.Verified.arith_addi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .addi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_andi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .andi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_ceildivsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .ceildivsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_ceildivui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .ceildivui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_divsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .divsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_divui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .divui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_floordivsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .floordivsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_maxsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .maxsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_maxui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .maxui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_minsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .minsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_minui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .minui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_muli {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .muli) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_ori {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .ori) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_remsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .remsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_remui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .remui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_shli {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .shli) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_shrsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .shrsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_shrui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .shrui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_subi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .subi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_xori {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .xori) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_and {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .and) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_or {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .or) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_xor {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .xor) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/--
  Structural facts guaranteed by the verifier for `llvm.mlir.constant`: no operands, one
  result, no successors or regions.
-/
theorem OperationPtr.Verified.llvm_mlir__constant {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .mlir__constant) :
    op.getNumResults! ctx.raw = 1 ∧
    op.getNumOperands! ctx.raw = 0 ∧
    op.getNumSuccessors! ctx.raw = 0 ∧
    op.getNumRegions! ctx.raw = 0 := by
  simp only [Verified, verifyLocalInvariants, ← getOpType!_eq_getOpType, opType,
    verifyPlainOpCounts, ne_eq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure] at opVerify
  grind

theorem OperationPtr.Verified.llvm_intr__smax {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__smax) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__smin {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__smin) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__umax {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__umax) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__umin {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__umin) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/--
  The structural facts shared by every integer unary operation: exactly 1 operand and 1 result,
  no regions or successors, the result type matches the operand type, and that type is an integer
  type.
-/
def OperationPtr.IsVerifiedIntegerUnop (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 1 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ((op.getResult 0).get! ctx.raw).type = (op.getOperand! ctx.raw 0).getType! ctx.raw ∧
  ∃ integerType isT,
    ((op.getResult 0).get! ctx.raw).type = ⟨.integerType integerType, isT⟩

/--
  Structural facts extracted from a successful `verifyIntegerUnop` check. This is the shared
  core behind every integer unary operation's `Verified.*` lemma.
-/
private theorem OperationPtr.verifyIntegerUnop_eq_ok {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} {ty} (h : op.verifyIntegerUnop ctx opInBounds = .ok ty) :
    op.IsVerifiedIntegerUnop ctx := by
  simp only [IsVerifiedIntegerUnop, verifyIntegerUnop, verifyPlainOpCounts,
    verifyResultTypeMatches, TypeAttr.verifyIntegerType, ne_eq, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure] at h ⊢
  simp only [TypeAttr.inj]
  split at h <;> grind

/--
  Reduce a verified integer unary operation to a successful `verifyIntegerUnop` check.
  The hypothesis `armReduces` says the operation's local-invariant check is exactly the
  `verifyIntegerUnop` arm; it is discharged per operation by unfolding the dispatcher at the
  concrete opcode.
-/
private theorem OperationPtr.verifyIntegerUnop_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.verifyIntegerUnop ctx opInBounds >>= fun _ => pure ())) :
    ∃ ty, op.verifyIntegerUnop ctx opInBounds = .ok ty := by
  rw [Verified, armReduces] at opVerify
  cases hb : op.verifyIntegerUnop ctx opInBounds with
  | ok ty => exact ⟨ty, rfl⟩
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/-- Structural facts from the verifier for a verified `llvm.intr.ctlz`. -/
theorem OperationPtr.Verified.llvm_intr__ctlz {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__ctlz) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty

/-- Structural facts from the verifier for a verified `llvm.intr.cttz`. -/
theorem OperationPtr.Verified.llvm_intr__cttz {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__cttz) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty

/-- Structural facts from the verifier for a verified `llvm.intr.ctpop`. -/
theorem OperationPtr.Verified.llvm_intr__ctpop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__ctpop) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty

/-- Structural facts from the verifier for a verified `llvm.intr.bswap`. Unlike the other integer
    unops, `llvm.intr.bswap`'s verifier arm runs `verifyIntegerUnop` and *then* an extra
    bitwidth-∈-{16,32,64} check, so it does not reduce to the plain `verifyIntegerUnop >>= pure`
    arm; we instead peel the leading `verifyIntegerUnop` bind directly. -/
theorem OperationPtr.Verified.llvm_intr__bswap {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__bswap) :
    op.IsVerifiedIntegerUnop ctx := by
  rw [Verified] at opVerify
  simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType] at opVerify
  cases hb : op.verifyIntegerUnop ctx opInBounds with
  | ok ty => exact op.verifyIntegerUnop_eq_ok hb
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/--
  Structural facts guaranteed by the verifier for a three-operand integer operation (e.g.
  `llvm.intr.fshl`/`fshr`): one result, three operands, no successors or regions, and all three
  operands *and* the result share one integer type. This is the ternary analogue of
  `IsVerifiedIntegerBinop`.
-/
def OperationPtr.IsVerifiedIntegerTernop (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 3 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ integerType,
    ((op.getResult 0).get! ctx.raw).type = ⟨.integerType integerType, (by grind)⟩ ∧
    ((op.getOperand! ctx.raw 0).getType! ctx.raw) = ⟨.integerType integerType, (by grind)⟩ ∧
    ((op.getOperand! ctx.raw 1).getType! ctx.raw) = ⟨.integerType integerType, (by grind)⟩ ∧
    ((op.getOperand! ctx.raw 2).getType! ctx.raw) = ⟨.integerType integerType, (by grind)⟩

/--
  Structural facts extracted from a successful `verifyIntegerTernop` check. Shared core behind
  every integer ternary operation's `Verified.*` lemma.
-/
private theorem OperationPtr.verifyIntegerTernop_eq_ok {ctx : WfIRContext OpCode}
    {op : OperationPtr} {opInBounds : op.InBounds ctx.raw}
    (h : op.verifyIntegerTernop ctx opInBounds = .ok ()) :
    op.IsVerifiedIntegerTernop ctx := by
  simp only [IsVerifiedIntegerTernop, verifyIntegerTernop, verifyPlainOpCounts,
    verifyOperandTypesMatch, verifyResultTypeMatches, TypeAttr.verifyIntegerType, ne_eq, bind,
    Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h ⊢
  simp only [TypeAttr.inj]
  split at h <;> grind

/--
  Reduce a verified integer ternary operation to a successful `verifyIntegerTernop` check.
  `armReduces` says the operation's local-invariant check is exactly the `verifyIntegerTernop`
  arm; it is discharged per operation by unfolding the dispatcher at the concrete opcode.
-/
private theorem OperationPtr.verifyIntegerTernop_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.verifyIntegerTernop ctx opInBounds >>= fun _ => pure ())) :
    op.verifyIntegerTernop ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  cases hb : op.verifyIntegerTernop ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/--
  Every integer ternary operation's `Verified.*` lemma reduces to this: given a verified operation
  whose local-invariant check is the `verifyIntegerTernop` arm, it satisfies
  `IsVerifiedIntegerTernop`.
-/
private theorem OperationPtr.Verified.integerTernop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.verifyIntegerTernop ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedIntegerTernop ctx :=
  op.verifyIntegerTernop_eq_ok <| op.verifyIntegerTernop_ok_of_Verified opVerify armReduces

/-- Structural facts from the verifier for a verified `llvm.intr.fshl`. -/
theorem OperationPtr.Verified.llvm_intr__fshl {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__fshl) :
    op.IsVerifiedIntegerTernop ctx := OperationPtr.Verified.integerTernop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/-- Structural facts from the verifier for a verified `llvm.intr.fshr`. -/
theorem OperationPtr.Verified.llvm_intr__fshr {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__fshr) :
    op.IsVerifiedIntegerTernop ctx := OperationPtr.Verified.integerTernop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/--
  Structural facts guaranteed by the verifier for an integer extension operation
  (`llvm.sext`/`llvm.zext`): one result, one operand, no successors or regions, and both the
  operand and the result have integer types, with the operand's strictly narrower than the
  result's. This is the width-crossing cousin of `IsVerifiedIntegerUnop`.
-/
def OperationPtr.IsVerifiedIntegerExtop (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 1 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ operandType resultType,
    ((op.getOperand! ctx.raw 0).getType! ctx.raw) = ⟨.integerType operandType, (by grind)⟩ ∧
    ((op.getResult 0).get! ctx.raw).type = ⟨.integerType resultType, (by grind)⟩ ∧
    operandType.bitwidth < resultType.bitwidth

/--
  Structural facts extracted from a successful `verifyIntegerExtTypes` check. Shared core behind
  every integer extension operation's `Verified.*` lemma.
-/
private theorem OperationPtr.verifyIntegerExtTypes_eq_ok {ctx : WfIRContext OpCode}
    {op : OperationPtr} {opInBounds : op.InBounds ctx.raw}
    (h : op.verifyIntegerExtTypes ctx opInBounds = .ok ()) :
    op.IsVerifiedIntegerExtop ctx := by
  simp only [IsVerifiedIntegerExtop, verifyIntegerExtTypes, verifyPlainOpCounts, ne_eq, bind,
    Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h ⊢
  simp only [TypeAttr.inj]
  split at h <;> grind

/--
  Reduce a verified integer extension operation to a successful `verifyIntegerExtTypes` check.
  `armReduces` says the operation's local-invariant check is exactly the `verifyIntegerExtTypes`
  arm; it is discharged per operation by unfolding the dispatcher at the concrete opcode.
-/
private theorem OperationPtr.verifyIntegerExtTypes_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.verifyIntegerExtTypes ctx opInBounds >>= fun _ => pure ())) :
    op.verifyIntegerExtTypes ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  cases hb : op.verifyIntegerExtTypes ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/--
  Every integer extension operation's `Verified.*` lemma reduces to this: given a verified
  operation whose local-invariant check is the `verifyIntegerExtTypes` arm, it satisfies
  `IsVerifiedIntegerExtop`.
-/
private theorem OperationPtr.Verified.integerExtop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.verifyIntegerExtTypes ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedIntegerExtop ctx :=
  op.verifyIntegerExtTypes_eq_ok <| op.verifyIntegerExtTypes_ok_of_Verified opVerify armReduces

/-- Structural facts from the verifier for a verified `llvm.sext`. -/
theorem OperationPtr.Verified.llvm_sext {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .sext) :
    op.IsVerifiedIntegerExtop ctx := OperationPtr.Verified.integerExtop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/-- Structural facts from the verifier for a verified `llvm.zext`. -/
theorem OperationPtr.Verified.llvm_zext {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .zext) :
    op.IsVerifiedIntegerExtop ctx := OperationPtr.Verified.integerExtop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_add {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .add) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_sub {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .sub) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_ashr {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .ashr) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_mul {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .mul) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_sdiv {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .sdiv) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_udiv {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .udiv) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_srem {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .srem) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_urem {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .urem) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/- Verified ModArith Op Lemmas -/

def OperationPtr.IsVerifiedModArithBinop (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 2 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ modArithType,
    modArithType.modulus.value > 0 ∧
    modArithType.modulus.value < 2 ^ modArithType.modulus.type.bitwidth ∧
    ((op.getResult 0).get! ctx.raw).type = ⟨.modArithType modArithType, (by grind)⟩ ∧
    ((op.getOperand! ctx.raw 0).getType! ctx.raw) = ⟨.modArithType modArithType, (by grind)⟩ ∧
    ((op.getOperand! ctx.raw 1).getType! ctx.raw) = ⟨.modArithType modArithType, (by grind)⟩


/- Unpack a long `Except` chain that succeeds overall into a conjunction of successes. -/
private theorem Except_bind_ok_iff {ε α β} {x : Except ε α} {f : α → Except ε β}
    {b : β} :
    (x >>= f) = Except.ok b ↔ ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x <;> simp [bind, Except.bind]

/- Remove the existential binders produced by successful `PUnit` checks. -/
private theorem exists_punit {p : PUnit → Prop} :
    (∃ u, p u) ↔ p PUnit.unit :=
  ⟨fun ⟨⟨⟩, h⟩ => h, fun h => ⟨PUnit.unit, h⟩⟩

private theorem OperationPtr.verifyModArithBinOp_eq_ok {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (h : op.verifyModArithBinOp ctx opInBounds = .ok ()) :
    op.IsVerifiedModArithBinop ctx := by
  simp only [IsVerifiedModArithBinop, TypeAttr.inj]
  simp only [verifyModArithBinOp, verifyPlainOpCounts, verifyOperandTypesMatch,
             verifyResultTypeMatches, TypeAttr.verifyModArithType,
             Except_bind_ok_iff, exists_punit] at h
  obtain ⟨hPlainOpCounts, operandType, hOperandTypesMatch,
          hResultTypeMatches, modArithType, hModArithType, _⟩ := h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
    at hPlainOpCounts hOperandTypesMatch hResultTypeMatches hModArithType
  grind

private theorem OperationPtr.Verified.modArithBinop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.verifyModArithBinOp ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedModArithBinop ctx := by
  rw [Verified, armReduces] at opVerify
  have h : op.verifyModArithBinOp ctx opInBounds = .ok () := by
    cases hb : op.verifyModArithBinOp ctx opInBounds with
    | ok _ => rfl
    | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify
  exact op.verifyModArithBinOp_eq_ok h

theorem OperationPtr.Verified.mod_arith_add {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .mod_arith .add) :
    op.IsVerifiedModArithBinop ctx := OperationPtr.Verified.modArithBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.mod_arith_mul {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .mod_arith .mul) :
    op.IsVerifiedModArithBinop ctx := OperationPtr.Verified.modArithBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.mod_arith_sub {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .mod_arith .sub) :
    op.IsVerifiedModArithBinop ctx := OperationPtr.Verified.modArithBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

def OperationPtr.IsVerifiedModArithConstant (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumOperands! ctx.raw = 0 ∧
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ modArithType,
    ((op.getResult 0).get! ctx.raw).type = ⟨.modArithType modArithType, (by grind)⟩ ∧
    modArithType.modulus.value > 0 ∧
    modArithType.modulus.value < 2 ^ modArithType.modulus.type.bitwidth ∧
    -(2 ^ (modArithType.modulus.type.bitwidth - 1) : Int)
        ≤ (op.getProperties! ctx.raw (.mod_arith .constant)).value.value ∧
    (op.getProperties! ctx.raw (.mod_arith .constant)).value.value
        < 2 ^ modArithType.modulus.type.bitwidth

theorem OperationPtr.Verified.mod_arith_constant {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .mod_arith .constant) :
    op.IsVerifiedModArithConstant ctx := by
  simp only [Verified, verifyLocalInvariants, ← getOpType!_eq_getOpType, opType] at opVerify
  have h : op.verifyModArithConstantOp ctx opInBounds = .ok () := by
    cases hb : op.verifyModArithConstantOp ctx opInBounds with
    | ok _ => rfl
    | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify
  simp only [IsVerifiedModArithConstant, TypeAttr.inj]
  simp only [verifyModArithConstantOp, verifyPlainOpCounts, TypeAttr.verifyModArithType,
            Except_bind_ok_iff, exists_punit] at h
  obtain ⟨hPlainOpCounts, modArithType, hModArithType, hAttr⟩ := h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
    at hPlainOpCounts hModArithType hAttr
  grind

end
end Veir
