module

public import Veir.Pass

public section

namespace Veir

/-!
  Shared helpers for the RISC-V instruction-selection lowering patterns.
-/

/--
  Create a detached `unrealized_conversion_cast : (typeof v) -> !riscv.reg`,
  returning the updated context and the register-typed cast operation. The
  caller is responsible for inserting the returned operation.
-/
def castToRegLocal (ctx : WfIRContext OpCode) (v : ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast
      #[RegisterType.mk] #[v] #[] #[] () none

/--
  Create a detached `unrealized_conversion_cast` from `reg` back to `op`'s
  result type, returning the updated context and the cast operation. The target
  type is read from `op`, so this is type-agnostic (it also handles non-`i64`
  results, e.g. the `!llvm.ptr` produced by `getelementptr`). The caller is
  responsible for inserting the returned operation and replacing `op`'s result
  with its result.
-/
def replaceWithRegLocal (ctx : WfIRContext OpCode) (op : OperationPtr) (reg : ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  let type := ((op.getResult 0).get! ctx.raw).type
  WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast
      #[type] #[reg] #[] #[] () none

/-- Immediate properties holding `value` as a 64-bit immediate. -/
def mkRISCVImm (value : Int) : RISCVImmediateProperties :=
  RISCVImmediateProperties.mk (BitVec.ofInt 64 value)

/-- Create a detached register-result `dst` op with immediate `value`. -/
def createRISCVImmLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (operands : Array ValuePtr) (value : Int) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx dst #[RegisterType.mk] operands #[] #[]
      (cast h.symm (mkRISCVImm value)) none

/-- Create a detached register-result `dst` op without properties. -/
def createRISCVUnitLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = Unit) (operands : Array ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx dst #[RegisterType.mk] operands #[] #[]
      (cast h.symm ()) none

end Veir
