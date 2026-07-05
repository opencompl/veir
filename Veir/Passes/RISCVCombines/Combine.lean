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

private def stripDefiningZextw (val : ValuePtr) (ctx : IRContext OpCode) : ValuePtr × Bool :=
  match getDefiningOp val ctx with
  | none => (val, false)
  | some defOp =>
    match matchOp defOp ctx (.riscv .zextw) 1 with
    | none => (val, false)
    | some (operands, _) => (operands[0]!, true)

set_option warn.sorry false in
/-- Drop `riscv.zextw` operands feeding a binary op whose semantics use only
    operand bits 31:0. For these consumers, the high 32 bits of each source are
    ignored, so zero-extending the source first is redundant. -/
private def drop_zextw_binary_low_word (dst : Riscv) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (operands, props) := matchOp op rewriter.ctx (.riscv dst) 2 | return rewriter
  let (lhs, lhsChanged) := stripDefiningZextw operands[0]! rewriter.ctx
  let (rhs, rhsChanged) := stripDefiningZextw operands[1]! rewriter.ctx
  if !lhsChanged && !rhsChanged then return rewriter
  let (rewriter, newOp) := rewriter.createOp! (.riscv dst) #[RegisterType.mk] #[lhs, rhs]
      #[] #[] props (some $ .before op)
  let rewriter := rewriter.replaceValue (op.getResult 0) (newOp.getResult 0) sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Drop a `riscv.zextw` operand feeding a unary immediate op whose semantics use
    only operand bits 31:0. -/
private def drop_zextw_unary_imm_low_word (dst : Riscv) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (operands, props) := matchOp op rewriter.ctx (.riscv dst) 1 | return rewriter
  let (src, changed) := stripDefiningZextw operands[0]! rewriter.ctx
  if !changed then return rewriter
  let (rewriter, newOp) := rewriter.createOp! (.riscv dst) #[RegisterType.mk] #[src]
      #[] #[] props (some $ .before op)
  let rewriter := rewriter.replaceValue (op.getResult 0) (newOp.getResult 0) sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-- `riscv.addw (riscv.zextw x), y -> riscv.addw x, y`, and symmetrically for
    the right operand. `addw` reads only the low 32 bits of each source. -/
def drop_zextw_addw := drop_zextw_binary_low_word .addw

/-- `riscv.addiw (riscv.zextw x), imm -> riscv.addiw x, imm`. -/
def drop_zextw_addiw := drop_zextw_unary_imm_low_word .addiw

/-- `riscv.roriw (riscv.zextw x), imm -> riscv.roriw x, imm`. -/
def drop_zextw_roriw := drop_zextw_unary_imm_low_word .roriw

/-- `riscv.srliw (riscv.zextw x), imm -> riscv.srliw x, imm`. -/
def drop_zextw_srliw := drop_zextw_unary_imm_low_word .srliw

set_option warn.sorry false in
/-- riscv.li 0 -> rv64.get_register (x0)

    Every consumer of a materialized zero uses it as a source register, and on
    RV64 the hard-wired zero register `x0` reads as 0 in any source position, so
    we can replace the result of a `riscv.li 0` with a reference to `x0` and drop
    the materialization. This removes the `li 0` wherever the constant is only fed
    into ops that can take `x0` directly (slt, sltu, branch-arg inits, ...).

    LLVM does this during isel: an `ISD::Constant` of 0 selects to a copy from
    the `X0` register rather than being materialized (commit d9906882fc61).
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVISelDAGToDAG.cpp#L1119-L1126 -/
def li_zero_to_x0 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (_, cst) := matchOp op rewriter.ctx (.riscv .li) 0 | return rewriter
  if cst.value.value ≠ 0 then return rewriter
  /- Nothing to do for a dead `li 0`; leave it for DCE and avoid creating a dead x0. -/
  if !op.hasUses! rewriter.ctx.raw then return rewriter
  let (rewriter, x0Op) ← rewriter.createOp! (.rv64 .get_register)
    #[(RegisterType.mk (some 0) : TypeAttr)] #[] #[] #[] () (some $ .before op)
  let rewriter := rewriter.replaceValue (op.getResult 0) (x0Op.getResult 0) sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let patterns : Array (RewritePattern OpCode) :=
    #[ right_identity_zero_add
     , srl_sra_signbit
     , srlw_sraw_signbit
     , drop_zextw_addw
     , drop_zextw_addiw
     , drop_zextw_roriw
     , drop_zextw_srliw
     , li_zero_to_x0
     ]
  let pattern := RewritePattern.GreedyRewritePattern patterns
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
