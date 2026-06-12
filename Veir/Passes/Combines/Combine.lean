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
  riscv.OP x (riscv.li imm) -> riscv.OPi x imm
  riscv.OP (riscv.li imm) x -> riscv.OPi x imm
  Only when `imm` fits into a signed 12-bit immediate field.
  Covers: add→addi, or→ori, and→andi, xor→xori, addw→addiw.
-/
def fold_binop_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchRiscvBinop src op rewriter.ctx | return rewriter
  let some (reg, imm) :=
      (Prod.mk lhs <$> matchLi rhs rewriter.ctx) <|>
      (Prod.mk rhs <$> matchLi lhs rewriter.ctx)
    | return rewriter
  if imm.value.value < -2048 || imm.value.value > 2047 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.riscv dst) #[RegisterType.mk] #[reg]
      #[] #[] (cast h.symm imm) (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

def fold_add_li_to_addi   := fold_binop_li .add  .addi  rfl
def fold_or_li_to_ori     := fold_binop_li .or   .ori   rfl
def fold_and_li_to_andi   := fold_binop_li .and  .andi  rfl
def fold_xor_li_to_xori   := fold_binop_li .xor  .xori  rfl
def fold_addw_li_to_addiw := fold_binop_li .addw .addiw rfl

/-! # Pass implementation -/

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[right_identity_zero_add,
      fold_add_li_to_addi, fold_or_li_to_ori, fold_and_li_to_andi,
      fold_xor_li_to_xori, fold_addw_li_to_addiw]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
