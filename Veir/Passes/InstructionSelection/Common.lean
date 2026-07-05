import Veir.Pass
import Veir.PatternRewriter.Basic

namespace Veir

/-!
  Shared helpers for the RISC-V instruction-selection lowering patterns.
-/

/--
  Insert `unrealized_conversion_cast : (typeof v) -> !riscv.reg` before `op`,
  returning the updated rewriter and the register-typed result value.
-/
def castToReg (rewriter : PatternRewriter OpCode) (op : OperationPtr) (v : ValuePtr) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, castOp) ← rewriter.createOp! (.builtin .unrealized_conversion_cast)
      #[RegisterType.mk] #[v] #[] #[] () (some $ .before op)
  return (rewriter, castOp.getResult 0)

/--
  Cast the register value `reg` back to `op`'s result type and replace `op` with
  the cast. The target type is read from `op`, so this is type-agnostic (it also
  handles non-`i64` results, e.g. the `!llvm.ptr` produced by `getelementptr`).
-/
def replaceWithReg (rewriter : PatternRewriter OpCode) (op : OperationPtr) (reg : ValuePtr) :
    Option (PatternRewriter OpCode) := do
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let (rewriter, castOp) ← rewriter.createOp! (.builtin .unrealized_conversion_cast)
      #[type] #[reg] #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op castOp

/--
  Local-rewrite variant of `castToReg`: create a detached
  `unrealized_conversion_cast : (typeof v) -> !riscv.reg`, returning the updated
  context and the register-typed cast operation. The caller is responsible for
  inserting the returned operation.
-/
def castToRegLocal (ctx : WfIRContext OpCode) (v : ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast)
      #[RegisterType.mk] #[v] #[] #[] () none

/--
  Local-rewrite variant of `replaceWithReg`: create a detached
  `unrealized_conversion_cast` from `reg` back to `op`'s result type, returning
  the updated context and the cast operation. The caller is responsible for
  inserting the returned operation and replacing `op`'s result with its result.
-/
def replaceWithRegLocal (ctx : WfIRContext OpCode) (op : OperationPtr) (reg : ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  let type := ((op.getResult 0).get! ctx.raw).type
  WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast)
      #[type] #[reg] #[] #[] () none

end Veir
