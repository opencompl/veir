import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.RISCVMatching

namespace Veir.RISCV

/-!
  This file replicates LLVM's pre- and post-legalization GlobalISel combines.
-/

/-! # Lowering Patterns -/

set_option warn.sorry false in
/-- riscv.add x 0 -> x -/
def right_identity_zero_add (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchAdd op rewriter.ctx | return rewriter
  let some cst := matchLi rhs rewriter.ctx | return rewriter
  if cst.value.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) lhs sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/--
  riscv.add x (riscv.li imm) -> riscv.addi x imm
  riscv.add (riscv.li imm) x -> riscv.addi x imm
  But only when `imm` fits into a signed 12-bit immediate field.
-/
def fold_add_li_to_addi (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchAdd op rewriter.ctx | return rewriter
  let some (reg, imm) :=
      (Prod.mk lhs <$> matchLi rhs rewriter.ctx) <|>
      (Prod.mk rhs <$> matchLi lhs rewriter.ctx)
    | return rewriter
  if imm.value.value < -2048 || imm.value.value > 2047 then return rewriter
  let (rewriter, addiOp) ← rewriter.createOp (.riscv .addi) #[RegisterType.mk] #[reg]
      #[] #[] imm (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op addiOp sorry sorry sorry sorry sorry

/-! # Pass implementation -/

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[right_identity_zero_add, fold_add_li_to_addi]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
