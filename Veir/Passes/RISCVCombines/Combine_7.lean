import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

set_option warn.sorry false in
/-- `riscv.<ext> (riscv.<ext> x) -> riscv.<ext> x` for an idempotent width
    extension `ext` (`zextw` or `sextw`): the inner op already establishes the
    high-bit pattern (bits 63:32 clear, or a copy of bit 31) that the outer one
    would, so the outer is redundant and its result forwards to the inner op.

    LLVM: `zext.w` is `add.uw rd, rs, x0` and `sext.w` is `addiw rd, rs, 0`;
    either way a redundant re-extension of an already-extended value is folded
    away generically (by `SimplifyDemandedBits`, or by sext.w removal --
    `hasAllNBitUsers` treats an outer `sext.w` as a low-32-bit user).
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L120 -/
private def drop_redundant_ext (ext : Riscv) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.riscv ext) 1 | return rewriter
  let outerSrc := operands[0]!
  let some innerOp := getDefiningOp outerSrc rewriter.ctx | return rewriter
  let some (_, _) := matchOp innerOp rewriter.ctx (.riscv ext) 1 | return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) outerSrc sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-- `riscv.zextw (riscv.zextw x) -> riscv.zextw x`. -/
def zextw_zextw := drop_redundant_ext .zextw

/-- `riscv.sextw (riscv.sextw x) -> riscv.sextw x`. -/
def sextw_sextw := drop_redundant_ext .sextw

/-- Byte- and half-word mirrors of `zextw_zextw`/`sextw_sextw`. Each extension is
    idempotent (`ext (ext x) = ext x`) regardless of width, since the inner op
    already establishes exactly the high-bit pattern the outer one would. -/
def zextb_zextb := drop_redundant_ext .zextb
def zexth_zexth := drop_redundant_ext .zexth
def sextb_sextb := drop_redundant_ext .sextb
def sexth_sexth := drop_redundant_ext .sexth

/-- If `val` is defined by a `riscv.<ext>` op (`ext` being `zextw`/`sextw`),
    return its source operand and `true`; otherwise `val` unchanged and `false`. -/
def stripDefiningExt (ext : Riscv) (val : ValuePtr) (ctx : IRContext OpCode) :
    ValuePtr × Bool :=
  match getDefiningOp val ctx with
  | none => (val, false)
  | some defOp =>
    match matchOp defOp ctx (.riscv ext) 1 with
    | none => (val, false)
    | some (operands, _) => (operands[0]!, true)

set_option warn.sorry false in
/-- Drop `riscv.<ext>` operands (`ext` = `zextw`/`sextw`) feeding a binary op
    whose semantics use only operand bits 31:0. For these consumers the high 32
    bits of each source are ignored, and both extensions leave bits 31:0
    unchanged, so extending the source first is redundant.

    LLVM enumerates exactly which consumers demand only operand bits 31:0 in
    `hasAllNBitUsers` (RISCVOptWInstrs.cpp); for such a consumer a feeding
    `zext.w`/`sext.w` is redundant and drops out via `SimplifyDemandedBits` /
    sext.w removal.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L120 -/
private def drop_ext_binary_low_word (ext dst : Riscv) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (operands, props) := matchOp op rewriter.ctx (.riscv dst) 2 | return rewriter
  let (lhs, lhsChanged) := stripDefiningExt ext operands[0]! rewriter.ctx
  let (rhs, rhsChanged) := stripDefiningExt ext operands[1]! rewriter.ctx
  if !lhsChanged && !rhsChanged then return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.riscv dst) #[RegisterType.mk] #[lhs, rhs]
      #[] #[] props (some $ .before op)
  let rewriter := rewriter.replaceValue (op.getResult 0) (newOp.getResult 0) sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Drop a `riscv.<ext>` operand feeding a unary immediate op whose semantics use
    only operand bits 31:0. Same reasoning (and same LLVM `hasAllNBitUsers`
    enumeration) as `drop_ext_binary_low_word`. -/
private def drop_ext_unary_imm_low_word (ext dst : Riscv) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (operands, props) := matchOp op rewriter.ctx (.riscv dst) 1 | return rewriter
  let (src, changed) := stripDefiningExt ext operands[0]! rewriter.ctx
  if !changed then return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.riscv dst) #[RegisterType.mk] #[src]
      #[] #[] props (some $ .before op)
  let rewriter := rewriter.replaceValue (op.getResult 0) (newOp.getResult 0) sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-- `riscv.addw (riscv.zextw x), y -> riscv.addw x, y`, and symmetrically for
    the right operand. `addw` reads only the low 32 bits of each source.
    LLVM: `ADDW` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L156 -/
def drop_zextw_addw := drop_ext_binary_low_word .zextw .addw

/-- `riscv.addiw (riscv.zextw x), imm -> riscv.addiw x, imm`.
    LLVM: `ADDIW` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L155 -/
def drop_zextw_addiw := drop_ext_unary_imm_low_word .zextw .addiw

/-- `riscv.roriw (riscv.zextw x), imm -> riscv.roriw x, imm`.
    LLVM: `RORIW` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L170 -/
def drop_zextw_roriw := drop_ext_unary_imm_low_word .zextw .roriw

/-- `riscv.srliw (riscv.zextw x), imm -> riscv.srliw x, imm`.
    LLVM: `SRLIW` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L165 -/
def drop_zextw_srliw := drop_ext_unary_imm_low_word .zextw .srliw

/-- `riscv.sextw (riscv.zextw x) -> riscv.sextw x`. `sextw` is `addiw 0`
    (`Data.RISCV.sextw`), so like `addiw` it reads only bits 31:0 of its operand.
    LLVM: `SEXT_W` lowers to `ADDIW rd, rs, 0`, matched by the `ADDIW` case of
    `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L155 -/
def drop_zextw_sextw := drop_ext_unary_imm_low_word .zextw .sextw

/-- Sext mirror of `drop_zextw_addw`: `riscv.addw (riscv.sextw x), y ->
    riscv.addw x, y`. `sextw` also leaves bits 31:0 unchanged, and `addw` reads
    only those bits. LLVM `RISCVOptWInstrs` is primarily the `sext.w` remover;
    this is its `ADDW` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L156 -/
def drop_sextw_addw := drop_ext_binary_low_word .sextw .addw

/-- Sext mirror of `drop_zextw_addiw`. LLVM: `ADDIW` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L155 -/
def drop_sextw_addiw := drop_ext_unary_imm_low_word .sextw .addiw

/-- Sext mirror of `drop_zextw_roriw`. LLVM: `RORIW` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L170 -/
def drop_sextw_roriw := drop_ext_unary_imm_low_word .sextw .roriw

/-- Sext mirror of `drop_zextw_srliw`. LLVM: `SRLIW` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L165 -/
def drop_sextw_srliw := drop_ext_unary_imm_low_word .sextw .srliw

/-- `riscv.zextw (riscv.sextw x) -> riscv.zextw x`. `zextw` keeps only bits 31:0,
    which `sextw` leaves unchanged, so the inner `sextw` is redundant. (The mirror
    of `drop_zextw_sextw`, with the roles of the two extensions swapped.)
    LLVM: `zext.w` is `and 0xffffffff`, a low-32-bit user of its operand.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L120 -/
def drop_sextw_zextw := drop_ext_unary_imm_low_word .sextw .zextw
