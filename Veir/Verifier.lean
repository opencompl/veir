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
def OperationPtr.verifyLocalInvariants (op : OperationPtr) (ctx : IRContext) (inBounds : op.InBounds ctx) : Bool :=
  match op.getOpType ctx inBounds with
  | .unregistered => true
  | OpCode.arith.constant =>
    op.getNumOperands! ctx = 0 &&
    op.getNumResults! ctx = 1 &&
    op.getNumRegions! ctx = 0 &&
    op.getNumSuccessors! ctx = 0
  | OpCode.arith.addi =>
    op.getNumOperands! ctx = 2 &&
    op.getNumResults! ctx = 1 &&
    op.getNumRegions! ctx = 0 &&
    op.getNumSuccessors! ctx = 0
  | OpCode.arith.subi =>
    op.getNumOperands! ctx = 2 &&
    op.getNumResults! ctx = 1 &&
    op.getNumRegions! ctx = 0 &&
    op.getNumSuccessors! ctx = 0
  | OpCode.arith.muli =>
    op.getNumOperands! ctx = 2 &&
    op.getNumResults! ctx = 1 &&
    op.getNumRegions! ctx = 0 &&
    op.getNumSuccessors! ctx = 0
  | OpCode.arith.andi =>
    op.getNumOperands! ctx = 2 &&
    op.getNumResults! ctx = 1 &&
    op.getNumRegions! ctx = 0 &&
    op.getNumSuccessors! ctx = 0
  | OpCode.builtin.module =>
    op.getNumOperands! ctx = 0 &&
    op.getNumResults! ctx = 0 &&
    op.getNumRegions! ctx = 1 &&
    op.getNumSuccessors! ctx = 0
  | OpCode.test.test =>
    op.getNumOperands! ctx = 1 &&
    op.getNumResults! ctx = 1 &&
    op.getNumRegions! ctx = 0 &&
    op.getNumSuccessors! ctx = 0

deriving instance BEq for Veir.BlockOperand
deriving instance ReflBEq for Veir.BlockOperand
deriving instance LawfulBEq for Veir.BlockOperand
deriving instance BEq for Veir.OpOperand
deriving instance ReflBEq for Veir.OpOperand
deriving instance LawfulBEq for Veir.OpOperand
deriving instance BEq for Veir.ValueImpl
deriving instance ReflBEq for Veir.ValueImpl
deriving instance LawfulBEq for Veir.ValueImpl
deriving instance BEq for Veir.OpResult
deriving instance ReflBEq for Veir.OpResult
deriving instance LawfulBEq for Veir.OpResult
deriving instance BEq for Veir.Operation
deriving instance ReflBEq for Veir.Operation
deriving instance LawfulBEq for Veir.Operation

/--
  Verify that all operations in the IRContext satisfy their local invariants.
-/
def IRContext.verify (ctx : IRContext) (inBounds : ctx.FieldsInBounds) : Bool := Id.run do
  ctx.operations.allD (fun opPtr op hInMap =>
    opPtr.verifyLocalInvariants ctx (by unfold OperationPtr.InBounds; grind [OperationPtr.InBounds])
  )

end Veir
