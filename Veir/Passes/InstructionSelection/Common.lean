import Veir.Pass
import Veir.PatternRewriter.Basic

namespace Veir

/-!
  Shared helpers for the RISC-V instruction-selection lowering patterns.
-/

set_option warn.sorry false in
/--
  Insert `unrealized_conversion_cast : (typeof v) -> !riscv.reg` before `op`,
  returning the updated rewriter and the register-typed result value.
-/
def castToReg (rewriter : PatternRewriter OpCode) (op : OperationPtr) (v : ValuePtr) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast)
      #[RegisterType.mk] #[v] #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  return (rewriter, castOp.getResult 0)

set_option warn.sorry false in
/--
  Cast the register value `reg` back to `op`'s result type and replace `op` with
  the cast. The target type is read from `op`, so this is type-agnostic (it also
  handles non-`i64` results, e.g. the `!llvm.ptr` produced by `getelementptr`).
-/
def replaceWithReg (rewriter : PatternRewriter OpCode) (op : OperationPtr) (reg : ValuePtr) :
    Option (PatternRewriter OpCode) := do
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast)
      #[type] #[reg] #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

end Veir
