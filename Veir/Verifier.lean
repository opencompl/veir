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

/--
  Verify that all operations in the IRContext satisfy their local invariants.
-/
public def IRContext.verify (ctx : IRContext) : Except String Unit := Id.run do
  ctx.forOpsDepM (fun op opIn => op.verifyLocalInvariants ctx opIn)

end Veir
