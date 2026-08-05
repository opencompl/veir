module

public import Veir.IR.WellFormed

/-!
# Verifier

This file contains a collection of utilities for building program verifiers.
A verifier is a function that checks invariants of programs that go beyond the basic
well-formedness checks of the IR. For instance, checking that the operands of a binary
add have the same type, or that a branch instruction forwards the correct number of operands to
its successor blocks.
-/

namespace Veir

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
  Type compatibility for values forwarded to block arguments or returned from
  functions. Register types are compatible when their register constraints
  agree, treating an unconstrained `!riscv.reg` (no index) as matching any
  physical register such as `!riscv.reg<x0>`. All other types must be equal.
-/
def Attribute.branchArgCompatible (opTy argTy : Attribute) : Bool :=
  match opTy, argTy with
  | .registerType r1, .registerType r2 =>
      decide (r1.index = r2.index) || r1.index.isNone || r2.index.isNone
  | _, _ => decide (opTy = argTy)

/--
  Verify the result, region, and successor counts of a terminator: one that
  produces no results, has no regions, and transfers control to `successors`
  successor blocks. The operand count is left to the caller, since terminators
  are typically variadic in their forwarded arguments. The instruction name is
  included in each error message.
-/
def OperationPtr.verifyTerminatorCounts (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (successors : Nat) : Except String PUnit := do
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
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
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
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
def OperationPtr.verifyUnconditionalBranch (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyTerminatorCounts ctx opIn 1
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
  let dest := op.getSuccessor! ctx.raw 0
  if op.getNumOperands ctx.raw opIn ≠ dest.getNumArguments! ctx.raw then
    throw s!"{instrName}: branch expected operand count {dest.getNumArguments! ctx.raw}, got {op.getNumOperands ctx.raw opIn}"
  op.verifyBranchSuccessorArgTypes ctx 0 dest s!"{instrName}: successor"

/--
  Validate an `operandSegmentSizes` property that splits an operation's operands
  into `expectedSegments` consecutive groups, and return the group sizes.
-/
def OperationPtr.verifyOperandSegmentSizes
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw)
    (sizes : DenseArrayAttr) (expectedSegments : Nat) :
    Except String (Array Nat) := do
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
  if sizes.values.size ≠ expectedSegments then
    throw s!"{instrName}: operandSegmentSizes expected {expectedSegments} entries, got {sizes.values.size}"
  let mut segmentSizes : Array Nat := #[]
  for size in sizes.values do
    if size < 0 then
      throw s!"{instrName}: operandSegmentSizes contains negative size {size}"
    segmentSizes := segmentSizes.push size.toNat
  let segmentSum := segmentSizes.foldl (init := 0) fun acc size => acc + size
  if segmentSum ≠ op.getNumOperands ctx.raw opIn then
    throw s!"{instrName}: operandSegmentSizes describes {segmentSum} operands, got {op.getNumOperands ctx.raw opIn}"
  return segmentSizes

def OperationPtr.verifyCondBranchOperandSegmentSizes
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw)
    (sizes : DenseArrayAttr) (fixedOperands : Nat) :
    Except String PUnit := do
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
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

/--
  Walk up from `op` (a return-like terminator named `opName`) to the
  operation that encloses its parent region, i.e. the enclosing function
  operation.
-/
def OperationPtr.getEnclosingFunctionOp (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opName : String) : Except String OperationPtr :=
  match op.getParentOp! ctx.raw with
  | some funcOp => pure funcOp
  | none => throw s!"Expected {opName} to have an enclosing function operation"

def TypeAttr.verifyIntegerType
    (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .integerType _ => pure ()
  | _ => throw errMsg

def TypeAttr.verifyIntegerOrByteType
    (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .integerType _ => pure ()
  | .byteType _ => pure ()
  | _ => throw errMsg

def TypeAttr.verifyIntegerOrPointerType
    (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .integerType _ => pure ()
  | .llvmPointerType _ => pure ()
  | _ => throw errMsg

def TypeAttr.verifyI1
    (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
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
def OperationPtr.verifyPlainOpCounts (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (operands results : Nat) : Except String PUnit := do
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
  if op.getNumOperands ctx.raw opIn ≠ operands then
    throw s!"{instrName}: Expected {operands} operand(s)"
  if op.getNumResults ctx.raw opIn ≠ results then
    throw s!"{instrName}: Expected {results} result(s)"
  if op.getNumRegions ctx.raw opIn ≠ 0 then
    throw s!"{instrName}: Expected 0 regions"
  if op.getNumSuccessors ctx.raw opIn ≠ 0 then
    throw s!"{instrName}: Expected 0 successors"

def OperationPtr.verifyOperandTypesMatch (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (firstIdx secondIdx : Nat) (errMsg : String) : Except String TypeAttr := do
  let firstType := (op.getOperand! ctx.raw firstIdx).getType! ctx.raw
  let secondType := (op.getOperand! ctx.raw secondIdx).getType! ctx.raw
  if secondType.val ≠ firstType.val then
    throw errMsg
  pure firstType

def OperationPtr.verifyResultTypeMatches (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (expectedType : TypeAttr) (errMsg : String) : Except String PUnit := do
  if ((op.getResult 0).get! ctx.raw).type.val ≠ expectedType.val then
    throw errMsg

def OperationPtr.verifyIntegerBinop (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 0 to have integer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 1 to have integer type"
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"

def OperationPtr.verifyIntegerTernop (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 3 1
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 0 to have integer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 1 to have integer type"
  ((op.getOperand! ctx.raw 2).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 2 to have integer type"
  let _ ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  let operandType ← op.verifyOperandTypesMatch ctx 0 2
    s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"

def OperationPtr.verifyIntegerUnop (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String TypeAttr := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  operandType.verifyIntegerType s!"{instrName}: Expected operand 0 to have integer type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"
  pure operandType

def OperationPtr.verifyICmp (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 0 to have integer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 1 to have integer type"
  let _ ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  ((op.getResult 0).get! ctx.raw).type.verifyI1 s!"{instrName}: Expected i1 result"

def OperationPtr.verifySelectTypes (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 3 1
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyI1 s!"{instrName}: Expected i1 condition"
  let operandType ← op.verifyOperandTypesMatch ctx 1 2
    s!"{instrName}: Expected select values to have the same type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match select value type"

def OperationPtr.verifyTruncTypes (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (allowByte : Bool) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
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

def OperationPtr.verifyIntegerExtTypes (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
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

/--
  Reject any operand or result whose type is a zero-width integer (`i0`).
  Whether `i0` is legal is a per-dialect policy, so callers must apply this
  check explicitly to operations that forbid it.
-/
def OperationPtr.checkIsNonNullIntegerType (op : OperationPtr)
    (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (HasOpInfo.name (op.getOpType ctx.raw opIn))
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:opTypes.size] do
    if let .integerType intType := (opTypes[i]!).val then
      if intType.bitwidth = 0 then
        throw s!"{instrName}: operand {i} has forbidden i0 type"
  for i in [0:op.getNumResults ctx.raw opIn] do
    if let .integerType intType := ((op.getResult i).get! ctx.raw).type.val then
      if intType.bitwidth = 0 then
        throw s!"{instrName}: result {i} has forbidden i0 type"

def denseElementsElementType? (typeStr : String) : Option String :=
  let s := typeStr.replace " " ""
  let segments := s.splitOn "x"
  if "tensor<".isPrefixOf s && s.endsWith ">" && segments.length ≥ 2 then
    some ((segments.getLast!.splitOn ">").head!)
  else
    none

/-- Check that every successor belongs to the same region as its predecessor. -/
def WfIRContext.successorsHaveSameParent (ctx : WfIRContext OpInfo) : Bool :=
  ctx.raw.blocks.keys.all fun block =>
    (block.getSuccessors! ctx.raw).all fun successor =>
      (successor.get! ctx.raw).parent = (block.get! ctx.raw).parent

end

end Veir
