import Veir.Pass
import Veir.PatternRewriter.Basic

namespace Veir

/-!
  Shared helpers for the RISC-V instruction-selection lowering patterns.

  Every per-op lowering is bracketed by the same boilerplate: a width check on
  the operands/result, and the `unrealized_conversion_cast` plumbing that moves
  values in and out of `!riscv.reg`. These helpers factor that out.
-/

/-- Every value in `vals` must have type `i64`. -/
def allI64 (vals : Array ValuePtr) (ctx : IRContext OpCode) : Bool :=
  vals.all fun v =>
    match (v.getType! ctx).val with
    | .integerType t => t.bitwidth == 64
    | _ => false

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
