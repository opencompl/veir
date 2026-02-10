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
  | .builtin_unregistered => pure ()
  /- ARITH -/
  | .arith_constant => do
    if op.getNumOperands ctx opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith_addi => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith_subi => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith_muli => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .arith_andi => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .builtin_module => do
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
  | .func_func => do
    if op.getNumRegions ctx opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumOperands ctx opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .func_return => do
    if op.getNumResults ctx opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- TEST -/
  | .test_test => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- LLVM -/
  | .llvm_constant => do
    if op.getNumOperands ctx opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_and => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_or => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_xor => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_sub => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_shl => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_lshr => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_ashr => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_mul => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_sdiv => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_udiv => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_srem => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_urem => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_icmp => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_select => do
    if op.getNumOperands ctx opIn ≠ 3 then
      throw "Expected 3 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_trunc => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_sext => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_zext => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_return => do
    if op.getNumResults ctx opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  /- RISCV -/
  | .riscv_li => do
    if op.getNumOperands ctx opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_lui => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_auipc => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_addi => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_slti => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sltiu => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_andi => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_ori => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_xori => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_addiw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_slli => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_srli => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_srai => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sub => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sll => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_slt => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sltu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_xor => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_srl => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sra => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_or => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_and => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_slliw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_srliw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sraiw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_addw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_subw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sllw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_srlw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sraw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_rem => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_remu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_remw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_remuw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_mul => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_mulh => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_mulhu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_mulhsu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_mulw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_div => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_divw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_divu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_divuw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_adduw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sh1adduw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sh2adduw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sh3adduw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sh1add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sh2add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sh3add => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_slliuw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_andn => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_orn => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_xnor => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_max => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_maxu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_min => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_minu => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_rol => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_ror => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_rolw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_rorw => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sextb => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_sexth => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_zexth => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_clz => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_clzw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_ctz => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_ctzw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_roriw => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_rori => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_bclr => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_bext => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_binv => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_bset => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_bclri => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_bexti => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_binvi => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_bseti => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operand"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_pack => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_packh => do
    if op.getNumOperands ctx opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .riscv_packw => do
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
