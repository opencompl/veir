import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

set_option warn.sorry false in
/-- `srlDst (width - 1) (sraDst _ x) -> srlDst (width - 1) x`, where `(srlDst,
    sraDst)` is `(riscv.srli, riscv.srai)` at `width = 64` and `(riscv.srliw,
    riscv.sraiw)` at `width = 32`: an arithmetic right shift never changes the top
    bit, so a subsequent logical shift by `width - 1` (which keeps only that bit)
    doesn't care what the `sra`'s own shift amount was. Mirrors LLVM's generic
    (division-agnostic) `DAGCombiner::visitSRL` rule
    `fold (srl (sra X, Y), 31) -> (srl X, 31)` (there `31` is `OpSizeInBits - 1`,
    i.e. `63` at `i64`). This -- not a `k = 1` special case in the `sdiv` lowering
    itself -- is what shortens `sdiv x, 2`'s codegen relative to the general
    `sdiv x, 2^k` sequence: the correction shift's amount `W - k` only happens to
    coincide with `W - 1` when `k = 1`.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L11628-L11633 -/
def srl_sra_signbitGen (srlDst : Riscv) (hSrl : Riscv.propertiesOf srlDst = RISCVImmediateProperties)
    (sraDst : Riscv) (width : Nat) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, outerImm) := matchOp op rewriter.ctx (.riscv srlDst) 1 | return rewriter
  if (cast hSrl outerImm : RISCVImmediateProperties).value.value ≠ (width : Int) - 1 then
    return rewriter
  let some sraOp := getDefiningOp operands[0]! rewriter.ctx | return rewriter
  let some (sraOperands, _) := matchOp sraOp rewriter.ctx (.riscv sraDst) 1 | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.riscv srlDst) #[RegisterType.mk] #[sraOperands[0]!]
      #[] #[] outerImm (some $ .before op)
  let rewriter := rewriter.replaceValue (op.getResult 0) (newOp.getResult 0) sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

def srl_sra_signbit := srl_sra_signbitGen .srli rfl .srai 64

/-- `i32` analogue of `srl_sra_signbit`: `riscv.srliw 31 (riscv.sraiw _ x) ->
    riscv.srliw 31 x`. -/
def srlw_sraw_signbit := srl_sra_signbitGen .srliw rfl .sraiw 32

set_option warn.sorry false in
/-- Drop `riscv.srli 63 (riscv.slli 63 X)` when `X` is defined by a comparison
    op that's already guaranteed to produce exactly 0 or 1 (bits 63:1 clear).
    `slli 63` isolates bit 0 of `X` into bit 63, and `srli 63` moves it back
    down to bit 0 -- for such an `X` that round trip is the identity, so both
    shifts (and the `X` they wrap) can be replaced by `X` itself. We don't need
    `X`'s properties here (unlike `srl_sra_signbitGen`, which reads the inner
    op's shift amount), so no `propertiesOf`/`cast` dance is needed to support
    a generic inner opcode.

    LLVM: the comparison ops all produce a `ZeroOrOneBooleanContent` boolean
    (declared in the `RISCVTargetLowering` constructor), so the generic
    DAGCombiner folds the `(srl (shl X, XLen-1), XLen-1)` round trip away through
    known/demanded bits -- there is no RISC-V-specific peephole for it.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVISelLowering.cpp#L919 -/
private def drop_slli_srli_boolGen (boolDst : Riscv) (arity : Nat)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, outerImm) := matchOp op rewriter.ctx (.riscv .srli) 1 | return rewriter
  if outerImm.value.value ≠ 63 then return rewriter
  let some slliOp := getDefiningOp operands[0]! rewriter.ctx | return rewriter
  let some (slliOperands, innerImm) := matchOp slliOp rewriter.ctx (.riscv .slli) 1 | return rewriter
  if innerImm.value.value ≠ 63 then return rewriter
  let some boolOp := getDefiningOp slliOperands[0]! rewriter.ctx | return rewriter
  let some (_, _) := matchOp boolOp rewriter.ctx (.riscv boolDst) arity | return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) slliOperands[0]! sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-- `riscv.slt` produces exactly 0 or 1. -/
def drop_slli_srli_slt := drop_slli_srli_boolGen .slt 2

/-- `riscv.sltu` produces exactly 0 or 1. -/
def drop_slli_srli_sltu := drop_slli_srli_boolGen .sltu 2

/-- `riscv.slti` produces exactly 0 or 1. -/
def drop_slli_srli_slti := drop_slli_srli_boolGen .slti 1

/-- `riscv.sltiu` produces exactly 0 or 1. -/
def drop_slli_srli_sltiu := drop_slli_srli_boolGen .sltiu 1

/-- `riscv.seqz` produces exactly 0 or 1. -/
def drop_slli_srli_seqz := drop_slli_srli_boolGen .seqz 1

/-- `riscv.snez` produces exactly 0 or 1. -/
def drop_slli_srli_snez := drop_slli_srli_boolGen .snez 1

/-- `riscv.sltz` produces exactly 0 or 1. -/
def drop_slli_srli_sltz := drop_slli_srli_boolGen .sltz 1

/-- `riscv.sgtz` produces exactly 0 or 1. -/
def drop_slli_srli_sgtz := drop_slli_srli_boolGen .sgtz 1
