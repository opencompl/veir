import Veir.GlobalOpInfo

open Veir

/-! Helpers to navigate parsed IR in unit tests. -/

/-- The first operation in the body of `op`. -/
def Veir.OperationPtr.body! (op : OperationPtr) (ctx : IRContext OpCode) : OperationPtr :=
  (((op.getRegion! ctx 0).getFirstBlock! ctx).get!.getFirstOp! ctx).get!

/-- The operation following `op` in its block. -/
def Veir.OperationPtr.next! (op : OperationPtr) (ctx : IRContext OpCode) : OperationPtr :=
  (op.getNextOp! ctx).get!
