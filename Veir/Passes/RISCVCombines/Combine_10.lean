import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.RISCVCombines.Combine_7

namespace Veir.RISCV

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

set_option warn.sorry false in
/-- `riscv.<ext>` (`zextw`/`sextw`) of the hard-wired zero register `x0` is a
    no-op: `x0` reads as 0 in any source position (see `li_zero_to_x0`), and 0 is
    both its own zero-extension and its own sign-extension.

    LLVM: `zext.w`/`sext.w` of a value known to be `0` (the `X0` register / an
    `ISD::Constant` 0) folds away via generic known-bits.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L759 -/
private def ext_x0 (ext : Riscv) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.riscv ext) 1 | return rewriter
  let src := operands[0]!
  let .registerType regType := (src.getType! rewriter.ctx.raw).val | return rewriter
  if regType.index ≠ some 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) src sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-- `riscv.zextw x0 -> x0`. -/
def zextw_x0 := ext_x0 .zextw

/-- `riscv.sextw x0 -> x0`. -/
def sextw_x0 := ext_x0 .sextw

/-- Byte- and half-word mirrors: every extension of `x0` (which reads as 0) is a
    no-op, since 0 is its own zero- and sign-extension at any width. -/
def zextb_x0 := ext_x0 .zextb
def zexth_x0 := ext_x0 .zexth
def sextb_x0 := ext_x0 .sextb
def sexth_x0 := ext_x0 .sexth

set_option warn.sorry false in
/-- `riscv.zextw (riscv.li v) -> riscv.li v` when `0 ≤ v < 2^32`: `li`'s
    materialized 64-bit value (`BitVec.ofInt 64 v`) already has bits 63:32
    clear in that range, so zero-extending it again is redundant.

    LLVM: `zext.w` is `(and X, 0xffffffff)` (isel pattern in RISCVInstrInfoZb.td);
    with `X` a constant whose bits 63:32 are already clear the mask folds away
    via generic constant folding / known-bits.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L759 -/
def zextw_li_low32 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.riscv .zextw) 1 | return rewriter
  let src := operands[0]!
  let some srcOp := getDefiningOp src rewriter.ctx | return rewriter
  let some (_, cst) := matchOp srcOp rewriter.ctx (.riscv .li) 0 | return rewriter
  if cst.value.value < 0 ∨ cst.value.value ≥ 4294967296 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) src sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- `riscv.sextw (riscv.li v) -> riscv.li v` when `-2^31 ≤ v < 2^31`: in that
    (signed 32-bit) range `li`'s materialized value (`BitVec.ofInt 64 v`) is
    already the sign-extension of its own low 32 bits, so `sextw` is redundant.
    Note the guard differs from `zextw_li_low32`'s unsigned `[0, 2^32)`: sign
    extension is a no-op exactly on the *signed* 32-bit range (which includes
    negative immediates, e.g. `li -1`).

    LLVM: constant folding / known-bits on `sext.w` of an already-sign-extended
    32-bit constant.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L120 -/
def sextw_li_low32 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.riscv .sextw) 1 | return rewriter
  let src := operands[0]!
  let some srcOp := getDefiningOp src rewriter.ctx | return rewriter
  let some (_, cst) := matchOp srcOp rewriter.ctx (.riscv .li) 0 | return rewriter
  if cst.value.value < -2147483648 ∨ cst.value.value ≥ 2147483648 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) src sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Byte- and half-word mirrors of `zextw_li_low32`/`sextw_li_low32`: a `riscv.<ext>`
    of a `riscv.li v` is redundant when `v`'s materialized value already carries
    the extension's high-bit pattern. For a zero-extension that is the *unsigned*
    range below `2^width` (bits above `width` clear); for a sign-extension the
    *signed* range `[-2^(width-1), 2^(width-1))` (bits above `width` all equal the
    sign bit). `ext`/`width` picks the op and its bit width. -/
private def ext_li_range (ext : Riscv) (lo hi : Int) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.riscv ext) 1 | return rewriter
  let src := operands[0]!
  let some srcOp := getDefiningOp src rewriter.ctx | return rewriter
  let some (_, cst) := matchOp srcOp rewriter.ctx (.riscv .li) 0 | return rewriter
  if cst.value.value < lo ∨ cst.value.value ≥ hi then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) src sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-- `riscv.zextb (riscv.li v) -> riscv.li v` when `0 ≤ v < 2^8`. -/
def zextb_li_low8 := ext_li_range .zextb 0 256

/-- `riscv.zexth (riscv.li v) -> riscv.li v` when `0 ≤ v < 2^16`. -/
def zexth_li_low16 := ext_li_range .zexth 0 65536

/-- `riscv.sextb (riscv.li v) -> riscv.li v` when `-2^7 ≤ v < 2^7`. -/
def sextb_li_low8 := ext_li_range .sextb (-128) 128

/-- `riscv.sexth (riscv.li v) -> riscv.li v` when `-2^15 ≤ v < 2^15`. -/
def sexth_li_low16 := ext_li_range .sexth (-32768) 32768
