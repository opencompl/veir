import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

/-!
  RISC-V GlobalISel-style combines.

  The immediate-selection rewrites that used to live here (folding a materialized
  constant into the immediate form of a RISC-V op) are now performed during
  instruction selection in `isel-sdag-riscv64`, matching the LLVM op directly —
  mirroring LLVM's `PatGprImm` TableGen patterns. What remains here are algebraic
  simplifications over already-selected RISC-V ops. New RISC-V combines can be
  added to the pattern list in `Combine.impl`.
-/

set_option warn.sorry false in
/-- riscv.add x 0 -> x -/
def right_identity_zero_add (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.riscv .add) 2 | return rewriter
  let lhs := operands[0]!
  let some liOp := getDefiningOp operands[1]! rewriter.ctx | return rewriter
  let some (_, cst) := matchOp liOp rewriter.ctx (.riscv .li) 0 | return rewriter
  if cst.value.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) lhs sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- `riscv.srli 63 (riscv.srai _ x) -> riscv.srli 63 x` (RV64): an arithmetic right
    shift never changes the top bit (bit 63), so a subsequent logical shift by 63
    (which keeps only that bit) doesn't care what the `srai`'s own shift amount was.
    Mirrors LLVM's generic (division-agnostic) `DAGCombiner::visitSRL` rule
    `fold (srl (sra X, Y), 31) -> (srl X, 31)` (there `31` is `OpSizeInBits - 1`,
    i.e. `63` at `i64`). This -- not a `k = 1` special case in the `sdiv` lowering
    itself -- is what shortens `sdiv x, 2`'s codegen relative to the general
    `sdiv x, 2^k` sequence: the correction shift's amount `W - k` only happens to
    coincide with `W - 1` when `k = 1`.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L11628-L11633 -/
def srl_sra_signbit (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, outerImm) := matchOp op rewriter.ctx (.riscv .srli) 1 | return rewriter
  if outerImm.value.value ≠ 63 then return rewriter
  let some sraOp := getDefiningOp operands[0]! rewriter.ctx | return rewriter
  let some (sraOperands, _) := matchOp sraOp rewriter.ctx (.riscv .srai) 1 | return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.riscv .srli) #[RegisterType.mk] #[sraOperands[0]!]
      #[] #[] outerImm (some $ .before op) sorry (by simp) (by simp) sorry
  let rewriter := rewriter.replaceValue (op.getResult 0) (newOp.getResult 0) sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- `i32` analogue of `srl_sra_signbit`: `riscv.srliw 31 (riscv.sraiw _ x) ->
    riscv.srliw 31 x`. -/
def srlw_sraw_signbit (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, outerImm) := matchOp op rewriter.ctx (.riscv .srliw) 1 | return rewriter
  if outerImm.value.value ≠ 31 then return rewriter
  let some sraOp := getDefiningOp operands[0]! rewriter.ctx | return rewriter
  let some (sraOperands, _) := matchOp sraOp rewriter.ctx (.riscv .sraiw) 1 | return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.riscv .srliw) #[RegisterType.mk] #[sraOperands[0]!]
      #[] #[] outerImm (some $ .before op) sorry (by simp) (by simp) sorry
  let rewriter := rewriter.replaceValue (op.getResult 0) (newOp.getResult 0) sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let patterns : Array (RewritePattern OpCode) :=
    #[right_identity_zero_add, srl_sra_signbit, srlw_sraw_signbit]
  let pattern := RewritePattern.GreedyRewritePattern patterns
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
