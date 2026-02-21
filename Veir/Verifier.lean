module

public import Veir.IR.Basic
public import Veir.IR.Fields
import Veir.ForLean

namespace Veir

/--
  Verify local invariants of an operation.
  This typically includes checking that the number of operands, successors, results, and regions
  match the expected values for the given operation type.
  This also checks that the given types are in bounds.
-/
def OperationPtr.verifyLocalInvariants (op : OperationPtr) (ctx : IRContext) (opIn : op.InBounds ctx) : Except String PUnit :=
  match op.getOpType ctx opIn with
  | .builtin .unregistered =>
    pure ()
  /- ARITH -/
  | .arith .constant => do
    if op.getNumOperands ctx opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith .addi => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith .subi => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith .muli => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith .andi => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .builtin .module => do
    if op.getNumOperands ctx opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- FUNC -/
  | .func .func => do
    if op.getNumRegions ctx opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumOperands ctx opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .func .return => do
    if op.getNumResults ctx opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- TEST -/
  | .test .test => do
    pure ()
  /- LLVM -/
  | .llvm .constant => do
    if op.getNumOperands ctx opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .and => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .or => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .xor => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .sub => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .shl => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .lshr => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .ashr => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .mul => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .sdiv => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .udiv => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .srem => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .urem => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .icmp => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .select => do
    if op.getNumOperands ctx opIn ≠ 3 then
      throw "Expected 3 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .trunc => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .sext => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .zext => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm .return => do
    if op.getNumResults ctx opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- RISCV -/
  | .riscv .li => do
    if op.getNumOperands ctx opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .lui => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .auipc => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .addi => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .slti => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sltiu => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .andi => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .ori => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .xori => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .addiw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .slli => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .srli => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .srai => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sub => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sll => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .slt => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sltu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .xor => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .srl => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sra => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .or => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .and => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .slliw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .srliw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sraiw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .addw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .subw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sllw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .srlw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sraw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rem => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .remu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .remw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .remuw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mul => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mulh => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mulhu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mulhsu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .mulw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .div => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .divw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .divu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .divuw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .adduw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh1adduw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh2adduw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh3adduw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh1add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh2add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sh3add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .slliuw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .andn => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .orn => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .xnor => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .max => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .maxu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .min => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .minu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rol => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .ror => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rolw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rorw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sextb => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .sexth => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .zexth => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .clz => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .clzw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .ctz => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .ctzw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .roriw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .rori => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .bclr => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .bext => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .binv => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .bset => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .bclri => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .bexti => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .binvi => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .bseti => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .pack => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .packh => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv .packw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()

/--
  Verify that all operations in the IRContext satisfy their local invariants.
-/
public def IRContext.verify (ctx : IRContext) : Except String Unit := Id.run do
  ctx.forOpsDepM (fun op opIn => op.verifyLocalInvariants ctx opIn)

end Veir
