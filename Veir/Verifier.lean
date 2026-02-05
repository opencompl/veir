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
      throw "Expected 1 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_sext => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operands"
    if op.getNumResults ctx opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .llvm_zext => do
    if op.getNumOperands ctx opIn ≠ 1 then
      throw "Expected 1 operands"
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
