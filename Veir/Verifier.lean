module

public import Veir.Verifier.Lemmas
public import Veir.Interfaces.FunctionInterfaces

import all Veir.Verifier.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]


/--
  Whether `attr` is *definitely* a non-zero initializer. TODO: This
  does not yet completely match MLIR's behavior.
-/
def Attribute.isKnownNonZero (attr : Attribute) : Bool :=
  match attr with
  | .integerAttr intAttr => intAttr.value != 0
  | .floatAttr fltAttr => fltAttr.value != 0.0
  | _ => false

/--
  Whether `n` is a valid alignment: a strictly positive power of two.
-/
def isValidLLVMAlignment (n : Int) : Bool :=
  decide (0 < n) && (n.toNat &&& (n.toNat - 1)) == 0

/--
  Check that a `func.return` returns the declared result types of its
  enclosing `func.func`.
-/
def OperationPtr.verifyFuncReturnTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let funcOp ← op.getEnclosingFunctionOp ctx "func.return"
  let .func .func := funcOp.getOpType! ctx.raw
    | throw "Expected func.return to be enclosed by func.func"
  let some outputs := FunctionOpInterface.getResultTypes? funcOp ctx.raw
    | throw "Expected enclosing func.func to have a function_type attribute"
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected func.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if !Attribute.branchArgCompatible (opTypes[i]!).val outputs[i]! then
      throw s!"func.return operand {i} type does not match the function's declared result type"

/--
  Check an `llvm.return` against its enclosing `llvm.func`'s declared results.
  A single `llvm.void` result means no operands.
-/
def OperationPtr.verifyLLVMFuncReturnTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (funcOp : OperationPtr) : Except String PUnit := do
  let some ft := FunctionOpInterface.getFunctionType? funcOp ctx.raw
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

/--
  Check an `llvm.return` against its `llvm.mlir.global`'s `global_type`.
-/
def OperationPtr.verifyLLVMGlobalReturnTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (globalOp : OperationPtr) : Except String PUnit := do
  let globalType :=
    (globalOp.getProperties! ctx.raw Llvm.mlir__global).global_type
  if op.getNumOperands ctx.raw opIn ≠ 1 then
    throw "Expected llvm.return in llvm.mlir.global to have 1 operand"
  let opTypes := op.getOperandTypes! ctx.raw
  if (opTypes[0]!).val ≠ globalType.val then
    throw "llvm.return operand type does not match the global's declared global_type"

/--
  Check an `llvm.return`'s operands against its enclosing `llvm.func` or `llvm.mlir.global`.
-/
def OperationPtr.verifyLLVMReturnTypes (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let enclosingOp ← op.getEnclosingFunctionOp ctx "llvm.return"
  let badEnclosure : Except String PUnit :=
    throw "Expected llvm.return to be enclosed by llvm.func or llvm.mlir.global"
  match enclosingOp.getOpType! ctx.raw with
  | .llvm .func => op.verifyLLVMFuncReturnTypes ctx opIn enclosingOp
  | .llvm .mlir__global => op.verifyLLVMGlobalReturnTypes ctx opIn enclosingOp
  | _ => badEnclosure

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

def OperationPtr.verifyLLVMShift (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerOrByteType s!"{instrName}: Expected operand 0 to have integer or byte type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType s!"{instrName}: Expected operand 1 to have integer type"
  op.verifyResultTypeMatches ctx ((op.getOperand! ctx.raw 0).getType! ctx.raw) s!"{instrName}: Expected result type to match first operand type"

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

def OperationPtr.verifyRISCVneg (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opIn : op.InBounds ctx.raw) (operands results : Nat) (imm : Int) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn operands results
  if imm < 0 ∨ 1048575 < imm then -- 1048575 = 2 ^ 20 - 1
    let instrName := String.fromUTF8! (op.getOpType ctx.raw opIn).name
    throw s!"{instrName} immediate out of bounds: must fit in an unsigned 20-bit field."
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
    let value := (op.getProperties! ctx.raw Mod_Arith.constant).value.value
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
  | .arith opType => Arith.verifyLocalInvariants opType op ctx opIn
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
    if (FunctionOpInterface.getFunctionType? op ctx.raw).isNone then
      throw "Expected function type"
    if (FunctionOpInterface.getSymName? op ctx.raw).isNone then
      throw "Expected symbol name"
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
  | .cf opType => Cf.verifyLocalInvariants opType op ctx opIn
  /- PDL -/
  | .pdl opType => PDL.verifyLocalInvariants opType op ctx opIn
  /- TEST -/
  | .test .test => do
    pure ()
  /- LLVM -/
  | .llvm .mlir__constant => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 0 1
    -- Unlike `arith.constant`, `llvm.mlir.constant` does not require the value
    -- attribute's type to match the result type exactly. An integer attribute
    -- only requires an integer result type of any width (e.g. a boolean constant
    -- may be written with a wider integer attribute). A float attribute requires
    -- a same-width float result, or a same-width integer result (the workaround
    -- for builtin MLIR float types without an LLVM equivalent).
    let resultType := ((op.getResult 0).get! ctx.raw).type.val
    match (op.getProperties! ctx.raw Llvm.mlir__constant).value with
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
    | .dense denseAttr =>
      match resultType with
      | .llvmArrayType { type := .llvmArrayType _, .. } => pure ()
      | .llvmArrayType arrType =>
        match denseElementsElementType? denseAttr.type with
        | some elemType =>
          let baseType := toString arrType.type
          if elemType ≠ baseType then
            throw s!"llvm.mlir.constant: dense elements type '{elemType}' does not match array element type '{baseType}'"
        | none => pure ()
      | _ => throw "llvm.mlir.constant: Expected array result type for a dense elements constant"
    | .string stringAttr =>
      match resultType with
      | .llvmArrayType arrType =>
        if arrType.type ≠ .integerType ⟨8⟩ then
          throw "llvm.mlir.constant: Expected array<N x i8> result type for a string constant"
        if stringAttr.value.size ≠ arrType.size then
          throw s!"llvm.mlir.constant: string length {stringAttr.value.size} does not match declared array size {arrType.size}"
      | _ => throw "llvm.mlir.constant: Expected array result type for a string constant"
      pure ()
  | .llvm .mlir__poison => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()
  | .llvm .mlir__global => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    let properties := op.getProperties! ctx.raw Llvm.mlir__global
    if let some alignment := properties.alignment then
      if alignment.type.bitwidth ≠ 64 then
        throw "'alignment' must be a 64-bit signless integer attribute"
      if !isValidLLVMAlignment alignment.value then
        throw "alignment attribute is not a power of 2"
    if properties.addr_space.type.bitwidth ≠ 32 then
      throw "'addr_space' must be a 32-bit signless integer attribute"
    -- A global is initialized either by the `value` attribute or by the body
    -- region, never both. An empty body with no `value` is a declaration, which
    -- is legal for every linkage.
    if let some value := properties.value then
      let body := (op.getRegion! ctx.raw 0).get! ctx.raw
      if body.firstBlock.isSome then
        throw "cannot have both initializer value and region"
      if properties.linkage.value == "common" && value.isKnownNonZero then
        throw "expected zero value for 'common' linkage"
    pure ()
  | .llvm .mlir__addressof => do
    op.verifyPlainOpCounts ctx opIn 0 1
    let resultType := ((op.getResult 0).get! ctx.raw).type
    let .llvmPointerType _ := resultType.val
      | throw "Expected result to have !llvm.ptr type"
    pure ()
  | .llvm .and | .llvm .or | .llvm .xor | .llvm .intr__smax | .llvm .intr__smin
  | .llvm .intr__umax | .llvm .intr__umin | .llvm .add | .llvm .sub
  | .llvm .ashr | .llvm .mul | .llvm .sdiv | .llvm .udiv
  | .llvm .srem | .llvm .urem
  | .llvm .intr__sadd__sat | .llvm .intr__uadd__sat
  | .llvm .intr__ssub__sat | .llvm .intr__usub__sat
  | .llvm .intr__sshl__sat | .llvm .intr__ushl__sat => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyIntegerBinop ctx opIn
    pure ()
  | .llvm .lshr | .llvm .shl => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyLLVMShift ctx opIn
    pure ()
  | .llvm .intr__abs => do
    op.checkIsNonNullIntegerType ctx opIn
    let _ ← op.verifyIntegerUnop ctx opIn
    pure ()
  | .llvm .intr__fshl | .llvm .intr__fshr => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyIntegerTernop ctx opIn
    pure ()
  | .llvm .intr__ctlz | .llvm .intr__cttz | .llvm .intr__ctpop
  | .llvm .intr__bitreverse => do
    op.checkIsNonNullIntegerType ctx opIn
    let _ ← op.verifyIntegerUnop ctx opIn
    pure ()
  | .llvm .intr__bswap => do
    op.checkIsNonNullIntegerType ctx opIn
    let operandType ← op.verifyIntegerUnop ctx opIn
    let .integerType intType := operandType.val
      | throw "llvm.intr.bswap: Expected operand 0 to have integer type"
    if intType.bitwidth ∉ [16, 32, 64] then
      throw "llvm.intr.bswap: bitwidth must be 16, 32, or 64"
    pure ()
  | .llvm .icmp => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyLLVMICmp ctx opIn
    pure ()
  | .llvm .select => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifySelectTypes ctx opIn
    pure ()
  | .llvm .trunc => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyTruncTypes ctx opIn true
    pure ()
  | .llvm .sext | .llvm .zext => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyIntegerExtTypes ctx opIn
    pure ()
  | .llvm .return => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyTerminatorCounts ctx opIn 0
    op.verifyLLVMReturnTypes ctx opIn
  | .llvm .unreachable => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 0 0
    pure ()
  | .llvm .br => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyUnconditionalBranch ctx opIn
  | .llvm .cond_br => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyTerminatorCounts ctx opIn 2
    let weights := (op.getProperties! ctx.raw Llvm.cond_br).branch_weights
    if weights.values.size ≠ 2 && weights.values.size ≠ 0 then
      throw "Expected 0 or 2 branch weights"
    let sizes := (op.getProperties! ctx.raw Llvm.cond_br).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 1
  | .llvm .alloca => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 1 1
    let properties := (op.getProperties! ctx.raw Llvm.alloca)
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.alloca' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"

    pure ()
  | .llvm .load => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 1 1
    let properties := (op.getProperties! ctx.raw Llvm.load)
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.load' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"

    pure ()
  | .llvm .store => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 2 0
    let properties := (op.getProperties! ctx.raw Llvm.store)
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.store' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"
    pure ()
  | .llvm .getelementptr => do
    op.checkIsNonNullIntegerType ctx opIn
    let props := op.getProperties! ctx.raw Llvm.getelementptr
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
    op.checkIsNonNullIntegerType ctx opIn
    if op.getNumResults ctx.raw opIn > 1 then
      throw "Expected at most 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .func => do
    op.checkIsNonNullIntegerType ctx opIn
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    if (FunctionOpInterface.getFunctionType? op ctx.raw).isNone then
      throw "Expected function type"
    if (FunctionOpInterface.getSymName? op ctx.raw).isNone then
      throw "Expected symbol name"
    pure ()
  | .llvm .fadd | .llvm .fsub | .llvm .fmul | .llvm .fdiv | .llvm .frem => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .llvm .module_flags => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 0 0
    pure ()
  | .llvm .freeze => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 1 1
    op.verifyResultTypeMatches ctx ((op.getOperand! ctx.raw 0).getType! ctx.raw)
      "llvm.freeze: Expected result type to match operand type"
    pure ()
  | .llvm .bitcast => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 1 1
    if Attribute.bitwidthOfType ((op.getOperand! ctx.raw 0).getType! ctx.raw) ≠ Attribute.bitwidthOfType (op.getResultTypes! ctx.raw)[0]! then
      throw "llvm.bitcast: Expected types of the same bitwidth"
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
    op.verifyRISCVneg ctx opIn 0 1 (op.getProperties! ctx.raw Riscv.lui).value.value
    pure ()
  | .riscv .auipc => do
    op.verifyRISCVneg ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.auipc).value.value
    pure ()
  | .riscv .addi => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.addi).value.value
    pure ()
  | .riscv .slti => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.slti).value.value
    pure ()
  | .riscv .sltiu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.sltiu).value.value
    pure ()
  | .riscv .andi => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.andi).value.value
    pure ()
  | .riscv .ori => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.ori).value.value
    pure ()
  | .riscv .xori => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.xori).value.value
    pure ()
  | .riscv .addiw => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.addiw).value.value
    pure ()
  | .riscv .slli => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.slli).value.value
    pure ()
  | .riscv .srli => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.srli).value.value
    pure ()
  | .riscv .srai => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.srai).value.value
    pure ()
  | .riscv .add | .riscv .sub | .riscv .sll | .riscv .slt | .riscv .sltu
  | .riscv .xor | .riscv .srl | .riscv .sra | .riscv .or | .riscv .and => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .riscv .slliw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw Riscv.slliw).value.value
    pure ()
  | .riscv .srliw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw Riscv.srliw).value.value
    pure ()
  | .riscv .sraiw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw Riscv.sraiw).value.value
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
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.slliuw).value.value
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
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw Riscv.roriw).value.value
    pure ()
  | .riscv .rori => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.rori).value.value
    pure ()
  | .riscv .bclr | .riscv .bext | .riscv .binv | .riscv .bset => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .riscv .bclri => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.bclri).value.value
    pure ()
  | .riscv .bexti => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.bexti).value.value
    pure ()
  | .riscv .binvi => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.binvi).value.value
    pure ()
  | .riscv .bseti => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.bseti).value.value
    pure ()
  | .riscv .pack | .riscv .packh | .riscv .packw
  | .riscv .czeroeqz | .riscv .czeronez => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .riscv .ld => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.ld).value.value
    pure ()
  | .riscv .lw => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lw).value.value
    pure ()
  | .riscv .lwu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lwu).value.value
    pure ()
  | .riscv .lh => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lh).value.value
    pure ()
  | .riscv .lhu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lhu).value.value
    pure ()
  | .riscv .lb => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lb).value.value
    pure ()
  | .riscv .lbu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lbu).value.value
    pure ()
  | .riscv .sd => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw Riscv.sd).value.value
    pure ()
  | .riscv .sw => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw Riscv.sw).value.value
    pure ()
  | .riscv .sh => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw Riscv.sh).value.value
    pure ()
  | .riscv .sb => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw Riscv.sb).value.value
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
    op.verifyRISCVRegisterTypes ctx opIn
    let properties := op.getProperties! ctx.raw Riscv_Stack.alloca
    if properties.size.type.bitwidth ≠ 64 then
      throw "attribute 'size' must be a 64-bit signless integer attribute"
    if properties.size.value < 0 then
      throw "size must be nonnegative"
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "attribute 'alignment' must be a 64-bit signless integer attribute"
    if properties.alignment.value ≤ 0 then
      throw "alignment must be a positive power of two"
    let alignment := properties.alignment.value.toNat
    if alignment &&& (alignment - 1) ≠ 0 then
      throw "alignment must be a positive power of two"
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
public def RegionPtr.getRegionKind (region : RegionPtr) (ctx : WfIRContext OpCode) : RegionKind :=
  match (region.get! ctx.raw).parent with
  | some parentOp =>
    let parent := parentOp.get! ctx.raw
    parent.opType.getRegionKind (parent.regions.idxOf region)
  | none => .SSACFG

/--
  Whether this region is exempt from the requirement that each of its blocks
  ends in a terminator.
-/
public def RegionPtr.hasNoTerminator (region : RegionPtr) (ctx : WfIRContext OpCode) : Bool :=
  match (region.get! ctx.raw).parent with
  | some parentOp =>
    let parent := parentOp.get! ctx.raw
    parent.opType.hasNoTerminator (parent.regions.idxOf region)
  | none => false

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
  let named (msg : String) : String :=
    match b.parent with
    | some region =>
      match (region.get! ctx.raw).parent with
      | some parentOp => s!"{String.fromUTF8! (parentOp.getOpType! ctx.raw).name}: {msg}"
      | none => msg
    | none => msg
  match b.lastOp with
  | none => throw (named "Expected the block to end in a terminator, but the block is empty")
  | some lastOp =>
    if !(lastOp.getOpType! ctx.raw).isTerminator then
      throw (named "Expected the last operation of a block to be a terminator")

/-- Check that a graph region contains at most one block. -/
private def WfIRContext.graphRegionsHaveAtMostOneBlock (ctx : WfIRContext OpCode) : Bool :=
  ctx.raw.regions.keys.all fun region =>
    if region.getRegionKind ctx = .Graph then
      let body := region.get! ctx.raw
      body.firstBlock = body.lastBlock
    else
      true

/--
  Check the module-wide invariants needed by LLVM global references: global
  names are unique and every `llvm.mlir.addressof` names a declared global.

  TODO: This is stricter than MLIR, which lets `llvm.mlir.addressof` name either
  an `llvm.mlir.global` or an `llvm.func`, so taking the address of a function
  (function pointers, vtables, globals initialized with a function address) is
  currently rejected.
-/
private def WfIRContext.verifyLLVMGlobalSymbols (ctx : WfIRContext OpCode) :
    Except String Unit := do
  let mut globals : Std.HashMap ByteArray OperationPtr := Std.HashMap.emptyWithCapacity
  for op in ctx.raw.operations.keys do
    if op.getOpType! ctx.raw = .llvm .mlir__global then
      let props := op.getProperties! ctx.raw Llvm.mlir__global
      let symbolName := "@".toUTF8 ++ props.sym_name.value
      if globals.contains symbolName then
        let displayName := String.fromUTF8? symbolName |>.getD "<non-UTF8 global symbol>"
        throw s!"llvm.mlir.global: duplicate global symbol '{displayName}'"
      globals := globals.insert symbolName op
  for op in ctx.raw.operations.keys do
    if op.getOpType! ctx.raw = .llvm .mlir__addressof then
      let props := op.getProperties! ctx.raw Llvm.mlir__addressof
      if !globals.contains props.global_name.value.toUTF8 then
        throw s!"llvm.mlir.addressof: symbol '{props.global_name.value}' does not name an llvm.mlir.global"

/--
  Check the whole-pattern invariants that MLIR verifies in
  `PatternOp::verifyRegions`: a `pdl.pattern` body holds only `pdl` operations,
  and contains at least one `pdl.operation`.
-/
private def WfIRContext.verifyPDLPatternBodies (ctx : WfIRContext OpCode) :
    Except String Unit := do
  let mut patternHasOperation : Std.HashMap OperationPtr Bool := Std.HashMap.emptyWithCapacity
  for op in ctx.raw.operations.keys do
    if op.getOpType! ctx.raw = .pdl .pattern then
      patternHasOperation := patternHasOperation.insert op false
  for op in ctx.raw.operations.keys do
    match op.getParentOp! ctx.raw with
    | some parent =>
      /- The body of a `pdl.pattern` and the body of the `pdl.rewrite` that
         terminates it both belong to the pattern. -/
      let parentType := parent.getOpType! ctx.raw
      if parentType = .pdl .pattern || parentType = .pdl .rewrite then
        let opType := op.getOpType! ctx.raw
        let .pdl pdlOp := opType
          | throw s!"pdl.pattern: expected only `pdl` operations within the pattern body, but got '{String.fromUTF8! opType.name}'"
        if pdlOp = .operation && parentType = .pdl .pattern then
          patternHasOperation := patternHasOperation.insert parent true
    | none => pure ()
  for (_, hasOperation) in patternHasOperation.toArray do
    if !hasOperation then
      throw "pdl.pattern: the pattern must contain at least one `pdl.operation`"

public section

/--
Verify the structural invariants of the IR context and the local invariants of all its operations.
-/
def WfIRContext.verify (ctx : WfIRContext OpCode) : Except String Unit := do
  if !ctx.successorsHaveSameParent then
    throw "Block successors must belong to the same region as their predecessor"
  if !ctx.graphRegionsHaveAtMostOneBlock then
    throw "Graph regions may contain at most one block"
  ctx.raw.forOpsDepM (fun op opIn => do
    let opType := op.getOpType ctx.raw opIn
    let opName := String.fromUTF8! opType.name
    Except.mapError
      (fun msg => if opName.isEmpty || msg.startsWith opName then msg else s!"{opName}: {msg}")
      (do
        op.verifyLocalInvariants ctx opIn
        if let .riscv _ := opType then
          op.verifyRISCVRegisterTypes ctx opIn
        match (op.get ctx.raw opIn).parent with
        | some _ => op.verifyTerminatorPosition ctx opIn
        | none => pure ()))
  ctx.raw.forBlocksDepM (fun block blockIn => do
    match (block.get ctx.raw blockIn).parent with
    | some region =>
      if !region.hasNoTerminator ctx then
        block.verifyTerminator ctx blockIn
    | none => pure ())
  ctx.verifyLLVMGlobalSymbols
  ctx.verifyPDLPatternBodies

/--
Assert that the IR context satisfies its structural and local invariants.
-/
def WfIRContext.Verified (ctx : WfIRContext OpCode) : Prop :=
  ctx.verify = .ok ()

/-- A verified context satisfies the same-parent successor check. -/
private theorem WfIRContext.Verified.successorsHaveSameParent
    {ctx : WfIRContext OpCode} (ctxVerified : ctx.Verified) :
    ctx.successorsHaveSameParent := by
  simp only [WfIRContext.Verified, WfIRContext.verify] at ctxVerified
  split at ctxVerified
  · trivial
  · grind

/-- Every successor of a block in a verified context belongs to the block's parent region. -/
@[grind →]
theorem WfIRContext.Verified.successor_parent
    {ctx : WfIRContext OpCode} (ctxVerified : ctx.Verified)
    {source : BlockPtr} (sourceIn : source.InBounds ctx.raw)
    (hsourceParent : (source.get! ctx.raw).parent = some region)
    (hsuccessor : successor ∈ source.getSuccessors! ctx.raw) :
    (successor.get! ctx.raw).parent = some region := by
  have hcheck := ctxVerified.successorsHaveSameParent
  have hsourceKeys : source ∈ ctx.raw.blocks.keys := by grind [source.inBounds_def]
  grind [Array.getElem_of_mem hsuccessor, (List.all_eq_true.mp hcheck) source hsourceKeys]

/-- A verified context satisfies the single-block graph-region check. -/
private theorem WfIRContext.Verified.graphRegionsHaveAtMostOneBlock
    {ctx : WfIRContext OpCode} (ctxVerified : ctx.Verified) :
    ctx.graphRegionsHaveAtMostOneBlock := by
  simp only [WfIRContext.Verified, WfIRContext.verify] at ctxVerified
  split at ctxVerified
  · trivial
  · split at ctxVerified
    · trivial
    · grind

/-- The first and last block of a graph region in a verified context are the same. -/
@[grind →]
theorem WfIRContext.Verified.graph_region_firstBlock_eq_lastBlock
    {ctx : WfIRContext OpCode} (ctxVerified : ctx.Verified)
    {region : RegionPtr} (regionIn : region.InBounds ctx.raw)
    (hregionKind : region.getRegionKind ctx = .Graph) :
    (region.get! ctx.raw).firstBlock = (region.get! ctx.raw).lastBlock := by
  have hcheck := ctxVerified.graphRegionsHaveAtMostOneBlock
  have hregionKeys : region ∈ ctx.raw.regions.keys := by grind [region.inBounds_def]
  have hregionCheck := (List.all_eq_true.mp hcheck) region hregionKeys
  grind

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
  Reduce a verified integer binary operation to a successful `verifyIntegerBinop` check.
  The hypothesis `armReduces` says the operation's local-invariant check is exactly the
  `verifyIntegerBinop` arm; it is discharged per operation by unfolding the dispatcher at the
  concrete opcode.
-/
private theorem OperationPtr.verifyIntegerBinop_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerBinop ctx opInBounds >>= fun _ => pure ())) :
    op.verifyIntegerBinop ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
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
      ⟨(op.getProperties! ctx.raw Arith.constant).value.type, (by grind)⟩ := by
  simp only [Verified, verifyLocalInvariants, Arith.verifyLocalInvariants,
    ← getOpType!_eq_getOpType, opType, ne_eq,
    bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, dite_not,
    ite_not] at opVerify
  simp only [TypeAttr.inj]
  grind

/-- A verified `llvm.mlir.constant` whose value attribute is an integer has an integer result type. -/
theorem OperationPtr.Verified.llvm_mlir__constant_resultType {op : OperationPtr} {opInBounds}
    {intAttr : IntegerAttr}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .mlir__constant)
    (hProp : (op.getProperties! ctx.raw Llvm.mlir__constant).value = .integer intAttr) :
    ∃ intTy : IntegerType, ((op.getResult 0).get! ctx.raw).type.val = .integerType intTy := by
  rw [Verified] at opVerify
  simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  simp only [verifyPlainOpCounts, hProp, ne_eq, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure] at opVerify
  cases hty : ((op.getResult 0).get! ctx.raw).type.val with
  | integerType intTy => exact ⟨intTy, rfl⟩
  | _ =>
    rw [hty] at opVerify
    split at opVerify <;> simp_all [reduceCtorEq]

/--
  The structural facts shared by every verified `llvm.icmp`: exactly 2 operands and 1 result, no
  regions or successors, an `i1` result, and the two operands share a single type. Unlike
  `IsVerifiedIntegerBinop`, the operands need not be integers (`llvm.icmp` also compares pointers),
  so only their mutual equality is recorded.
-/
def OperationPtr.IsVerifiedIcmp (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 2 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  (∃ i1ty : IntegerType,
    ((op.getResult 0).get! ctx.raw).type.val = .integerType i1ty ∧ i1ty.bitwidth = 1) ∧
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
    = ((op.getOperand! ctx.raw 1).getType! ctx.raw).val

/-- Structural facts extracted from a successful `verifyLLVMICmp` check. -/
private theorem OperationPtr.verifyLLVMICmp_eq_ok {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (h : op.verifyLLVMICmp ctx opInBounds = .ok ()) :
    op.IsVerifiedIcmp ctx := by
  simp only [IsVerifiedIcmp, verifyLLVMICmp, verifyPlainOpCounts, verifyOperandTypesMatch,
    TypeAttr.verifyIntegerOrPointerType, TypeAttr.verifyI1, ne_eq, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure] at h ⊢
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> grind

private theorem OperationPtr.verifyLLVMICmp_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyLLVMICmp ctx opInBounds >>= fun _ => pure ())) :
    op.verifyLLVMICmp ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifyLLVMICmp ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/-- Structural facts from the verifier for a verified `llvm.icmp`. -/
theorem OperationPtr.Verified.llvm_icmp {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .icmp) :
    op.IsVerifiedIcmp ctx :=
  op.verifyLLVMICmp_eq_ok <| op.verifyLLVMICmp_ok_of_Verified opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/--
  Every integer binary operation's `Verified.*` lemma: given that the operation is verified and
  has the given binary-operation opcode, it satisfies `IsVerifiedIntegerBinop`. Each is a thin
  wrapper that reduces `op.Verified` to a successful `verifyIntegerBinop` and applies the
  workhorse `verifyIntegerBinop_eq_ok`.
-/
private theorem OperationPtr.Verified.integerBinop {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerBinop ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedIntegerBinop ctx :=
  op.verifyIntegerBinop_eq_ok <| op.verifyIntegerBinop_ok_of_Verified opVerify armReduces
private theorem OperationPtr.verifySelectTypes_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifySelectTypes ctx opInBounds >>= fun _ => pure ())) :
    op.verifySelectTypes ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifySelectTypes ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

theorem OperationPtr.Verified.llvm_select {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .select) :
    op.IsVerifiedSelect ctx :=
  op.verifySelectTypes_eq_ok <| op.verifySelectTypes_ok_of_Verified opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/--
  Structural facts guaranteed by a successful `verifyLLVMShift` check. Unlike `IsVerifiedIntegerBinop`
  it does *not* pin the two operands to the same type: `verifyLLVMShift` only requires the shift
  amount (operand 1) to be an integer, and the result to match operand 0 (which may be an integer or
  a byte). The equality of the two operand widths is a *dynamic* fact recovered from a successful
  interpretation, not a static one.
-/
def OperationPtr.IsVerifiedLLVMShift (op : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 2 ∧
  ((op.getResult 0).get! ctx.raw).type.val = ((op.getOperand! ctx.raw 0).getType! ctx.raw).val ∧
  ∃ intType, ((op.getOperand! ctx.raw 1).getType! ctx.raw).val = .integerType intType

private theorem OperationPtr.verifyLLVMShift_eq_ok {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (h : op.verifyLLVMShift ctx opInBounds = .ok ()) :
    op.IsVerifiedLLVMShift ctx := by
  simp only [IsVerifiedLLVMShift] at ⊢
  simp [verifyLLVMShift, verifyPlainOpCounts, verifyResultTypeMatches,
    TypeAttr.verifyIntegerType, TypeAttr.verifyIntegerOrByteType, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure] at h
  grind [getNumOperands!_eq_getNumOperands, getNumResults!_eq_getNumResults]

private theorem OperationPtr.verifyLLVMShift_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyLLVMShift ctx opInBounds >>= fun _ => pure ())) :
    op.verifyLLVMShift ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifyLLVMShift ctx opInBounds with
  | ok u => rfl
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

private theorem OperationPtr.Verified.llvmShift {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyLLVMShift ctx opInBounds >>= fun _ => pure ())) :
    op.IsVerifiedLLVMShift ctx :=
  op.verifyLLVMShift_eq_ok <| op.verifyLLVMShift_ok_of_Verified opVerify armReduces

theorem OperationPtr.Verified.llvm_shl {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .shl) :
    op.IsVerifiedLLVMShift ctx := OperationPtr.Verified.llvmShift opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_lshr {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .lshr) :
    op.IsVerifiedLLVMShift ctx := OperationPtr.Verified.llvmShift opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_addi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .addi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_andi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .andi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_ceildivsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .ceildivsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_ceildivui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .ceildivui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_divsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .divsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_divui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .divui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_floordivsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .floordivsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_maxsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .maxsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_maxui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .maxui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_minsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .minsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_minui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .minui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_muli {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .muli) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_ori {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .ori) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_remsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .remsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_remui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .remui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_shli {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .shli) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_shrsi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .shrsi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_shrui {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .shrui) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_subi {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .subi) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.arith_xori {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .arith .xori) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, Arith.verifyLocalInvariants,
      ← getOpType!_eq_getOpType, opType]

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

theorem OperationPtr.Verified.llvm_intr__usub__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__usub__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__uadd__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__uadd__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__sadd__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__sadd__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__ssub__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__ssub__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__sshl__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__sshl__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

theorem OperationPtr.Verified.llvm_intr__ushl__sat {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__ushl__sat) :
    op.IsVerifiedIntegerBinop ctx := OperationPtr.Verified.integerBinop opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]

/--
  Reduce a verified integer unary operation to a successful `verifyIntegerUnop` check.
  The hypothesis `armReduces` says the operation's local-invariant check is exactly the
  `verifyIntegerUnop` arm; it is discharged per operation by unfolding the dispatcher at the
  concrete opcode.
-/
private theorem OperationPtr.verifyIntegerUnop_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerUnop ctx opInBounds >>= fun _ => pure ())) :
    ∃ ty, op.verifyIntegerUnop ctx opInBounds = .ok ty := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  cases hb : op.verifyIntegerUnop ctx opInBounds with
  | ok ty => exact ⟨ty, rfl⟩
  | error e => rw [hb] at opVerify; simp [bind, Except.bind] at opVerify

/-- Structural facts from the verifier for a verified `llvm.intr.bitreverse`. Its verifier arm is
    the shared `verifyIntegerUnop >>= pure` shape, so it reduces like `ctlz`/`cttz`/`ctpop`. -/
theorem OperationPtr.Verified.llvm_intr__bitreverse {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .intr__bitreverse) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty

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

/-- Structural facts from the verifier for a verified `llvm.intr.abs`. Its verifier arm is exactly
    the shared `verifyIntegerUnop >>= pure` shape (the `is_int_min_poison` property is not checked
    structurally), so it reduces like the `ctlz`/`cttz`/`ctpop` lemmas. -/
theorem OperationPtr.Verified.llvm_intr__abs {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__abs) :
    op.IsVerifiedIntegerUnop ctx := by
  obtain ⟨ty, hty⟩ := op.verifyIntegerUnop_ok_of_Verified opVerify <| by
    simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType]
  exact op.verifyIntegerUnop_eq_ok hty

/-- Structural facts from the verifier for a verified `llvm.intr.bswap`. Unlike the other unary
    intrinsics, `bswap`'s verifier arm performs an extra bitwidth check *after* the shared
    `verifyIntegerUnop`, so it is not exactly the `verifyIntegerUnop >>= pure` shape; we extract
    the successful `verifyIntegerUnop` by hand from the leading bind. -/
theorem OperationPtr.Verified.llvm_intr__bswap {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .llvm .intr__bswap) :
    op.IsVerifiedIntegerUnop ctx := by
  rw [Verified] at opVerify
  simp only [verifyLocalInvariants, ← getOpType!_eq_getOpType, opType] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  simp only [bind, Except.bind] at opVerify
  obtain ⟨ty, hty⟩ : ∃ ty, op.verifyIntegerUnop ctx opInBounds = .ok ty := by
    cases hb : op.verifyIntegerUnop ctx opInBounds with
    | ok ty => exact ⟨ty, rfl⟩
    | error e => rw [hb] at opVerify; simp at opVerify
  exact op.verifyIntegerUnop_eq_ok hty

/--
  Reduce a verified integer ternary operation to a successful `verifyIntegerTernop` check.
  `armReduces` says the operation's local-invariant check is exactly the `verifyIntegerTernop`
  arm; it is discharged per operation by unfolding the dispatcher at the concrete opcode.
-/
private theorem OperationPtr.verifyIntegerTernop_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerTernop ctx opInBounds >>= fun _ => pure ())) :
    op.verifyIntegerTernop ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
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
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerTernop ctx opInBounds >>= fun _ => pure ())) :
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
  Reduce a verified integer extension operation to a successful `verifyIntegerExtTypes` check.
  `armReduces` says the operation's local-invariant check is exactly the `verifyIntegerExtTypes`
  arm; it is discharged per operation by unfolding the dispatcher at the concrete opcode.
-/
private theorem OperationPtr.verifyIntegerExtTypes_ok_of_Verified {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds)
    (armReduces : op.verifyLocalInvariants ctx opInBounds
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerExtTypes ctx opInBounds >>= fun _ => pure ())) :
    op.verifyIntegerExtTypes ctx opInBounds = .ok () := by
  rw [Verified, armReduces] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
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
      = (op.checkIsNonNullIntegerType ctx opInBounds >>= fun _ =>
          op.verifyIntegerExtTypes ctx opInBounds >>= fun _ => pure ())) :
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
        ≤ (op.getProperties! ctx.raw Mod_Arith.constant).value.value ∧
    (op.getProperties! ctx.raw Mod_Arith.constant).value.value
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

/-- Structural facts guaranteed for a verified `func.func`: it has no operands, results, or
successors, and exactly one region (its body). -/
theorem OperationPtr.Verified.func_func {op : OperationPtr} {opInBounds}
    (opVerify : op.Verified ctx opInBounds) (opType : op.getOpType! ctx.raw = .func .func) :
    op.getNumOperands! ctx.raw = 0 ∧
    op.getNumResults! ctx.raw = 0 ∧
    op.getNumSuccessors! ctx.raw = 0 ∧
    op.getNumRegions! ctx.raw = 1 := by
  simp only [Verified, verifyLocalInvariants, ← getOpType!_eq_getOpType, opType, ne_eq,
    bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure,
    ite_not] at opVerify
  grind

end
end Veir
