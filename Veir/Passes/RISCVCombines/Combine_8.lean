import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.RISCVCombines.Combine_7

namespace Veir.RISCV

set_option warn.sorry false in
/-- Drop a `riscv.<ext>` wrapping the result of a bitwise op (`and`/`or`/`xor`)
    when its operands already establish the extension's high-bit pattern (bits
    63:32 all clear for `zextw`; all equal to bit 31 for `sextw`). Bitwise ops act
    bit-by-bit, so if the operands carry that pattern then so does the result --
    the outer `<ext>` is redundant.

    How many operands must be guarded depends on the op. In general *both* must be
    (`oneOperandSuffices := false`): e.g. `zextw (or a b)` clears bits 63:32 only
    when both `a` and `b` do, since a set high bit OR-ed in from either side stays
    set; likewise `xor`, and every `sextw` case (whose no-op condition needs the
    high bits to *match bit 31*, not merely be zero, so one guarded operand can't
    force it). The exception is `and` under `zextw`: `and` clears a result bit
    whenever *either* operand clears it, so a single `zextw`-guarded operand
    already forces bits 63:32 of the `and` to zero -- hence `oneOperandSuffices`
    there. When only one operand is guarded we still keep the inner op (and its
    unguarded operand) untouched; only the outer `<ext>` is dropped.

    LLVM: `AND`/`OR`/`XOR` are the "lower word of output depends only on lower
    word of input" cases of `hasAllNBitUsers`, which recurse into their own
    users; combined with the known high bits of the operands this lets
    `SimplifyDemandedBits` / sext.w removal drop the outer extension.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L317-L321 -/
private def drop_ext_of_bitwise (ext dst : Riscv) (oneOperandSuffices : Bool)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.riscv ext) 1 | return rewriter
  let inner := operands[0]!
  let some innerOp := getDefiningOp inner rewriter.ctx | return rewriter
  let some (innerOperands, _) := matchOp innerOp rewriter.ctx (.riscv dst) 2 | return rewriter
  let (_, lhsGuarded) := stripDefiningExt ext innerOperands[0]! rewriter.ctx
  let (_, rhsGuarded) := stripDefiningExt ext innerOperands[1]! rewriter.ctx
  let guarded := if oneOperandSuffices then lhsGuarded || rhsGuarded else lhsGuarded && rhsGuarded
  if !guarded then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) inner sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-- `riscv.zextw (riscv.and a b) -> riscv.and a b` when *at least one* of `a`, `b`
    is `riscv.zextw`-guarded: `and` forces a result bit to zero whenever either
    operand's bit is zero, so one guarded operand already clears bits 63:32.
    LLVM: `AND` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L317 -/
def zextw_and := drop_ext_of_bitwise .zextw .and true

/-- `riscv.zextw (riscv.or (riscv.zextw a) (riscv.zextw b)) -> riscv.or (riscv.zextw a) (riscv.zextw b)`.
    LLVM: `OR` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L319 -/
def zextw_or := drop_ext_of_bitwise .zextw .or false

/-- `riscv.zextw (riscv.xor (riscv.zextw a) (riscv.zextw b)) -> riscv.xor (riscv.zextw a) (riscv.zextw b)`.
    LLVM: `XOR` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L321 -/
def zextw_xor := drop_ext_of_bitwise .zextw .xor false

/-- Sext mirror of `zextw_and`: `riscv.sextw (riscv.and (riscv.sextw a) (riscv.sextw b))
    -> riscv.and (riscv.sextw a) (riscv.sextw b)`. Both operands are required here
    (unlike `zextw_and`): `sextw`'s no-op condition is that bits 63:32 match bit
    31, which a single guarded operand can't force. LLVM: `AND` case of
    `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L317 -/
def sextw_and := drop_ext_of_bitwise .sextw .and false

/-- Sext mirror of `zextw_or`. LLVM: `OR` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L319 -/
def sextw_or := drop_ext_of_bitwise .sextw .or false

/-- Sext mirror of `zextw_xor`. LLVM: `XOR` case of `hasAllNBitUsers`.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L321 -/
def sextw_xor := drop_ext_of_bitwise .sextw .xor false

/-! Byte- and half-word mirrors of the `zextw`/`sextw` bitwise combines. The
    `drop_ext_of_bitwise` reasoning is width-agnostic: for any extension that
    forces the bits above its width to a fixed pattern (`zextb`/`zexth` clear bits
    63:8 / 63:16; `sextb`/`sexth` set them to bit 7 / bit 15), a bitwise op whose
    operands all carry that pattern produces a result that carries it too, so the
    outer extension is redundant. As with `zextw_and`, `and` under a
    *zero*-extension needs only one guarded operand; every other case needs both. -/
def zextb_and := drop_ext_of_bitwise .zextb .and true
def zextb_or := drop_ext_of_bitwise .zextb .or false
def zextb_xor := drop_ext_of_bitwise .zextb .xor false
def zexth_and := drop_ext_of_bitwise .zexth .and true
def zexth_or := drop_ext_of_bitwise .zexth .or false
def zexth_xor := drop_ext_of_bitwise .zexth .xor false
def sextb_and := drop_ext_of_bitwise .sextb .and false
def sextb_or := drop_ext_of_bitwise .sextb .or false
def sextb_xor := drop_ext_of_bitwise .sextb .xor false
def sexth_and := drop_ext_of_bitwise .sexth .and false
def sexth_or := drop_ext_of_bitwise .sexth .or false
def sexth_xor := drop_ext_of_bitwise .sexth .xor false
