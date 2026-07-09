import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.RISCVCombines.Combine_7

namespace Veir.RISCV

/-- Match a `riscv.<store>` (`sw`/`sh`/`sb`), returning `(addr, val, properties)`.
    These stores have no results, so they can't go through `matchOp` (which
    requires exactly one). -/
private def matchRiscvStore (store : Riscv) (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (.riscv store)) := do
  guard (op.getOpType! ctx = .riscv store)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx (.riscv store)
  return (operands[0]!, operands[1]!, properties)

set_option warn.sorry false in
/-- Drop a `riscv.<ext>` from the value operand of a `riscv.<store>` whose width
    matches the extension's: a word store (`sw`) writes only bits 31:0, a halfword
    store (`sh`) only bits 15:0, and a byte store (`sb`) only bits 7:0 (see the
    store cases of `Interpreter.Basic.exec`, which keep just the low 4/2/1 bytes).
    An extension of the matching width leaves exactly those bits unchanged -- it
    only rewrites higher bits -- so extending the stored value first is redundant.
    The address operand is left untouched: it needs the full 64 bits.

    LLVM: the `SW`/`SH`/`SB` cases of `hasAllNBitUsers` demand only the low 32/16/8
    bits of the store's value operand (operand index 0), and nothing of the address.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L304-L311 -/
private def drop_ext_store (ext store : Riscv) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (addr, val, props) := matchRiscvStore store op rewriter.ctx | return rewriter
  let (val, changed) := stripDefiningExt ext val rewriter.ctx
  if !changed then return rewriter
  let (rewriter, _newOp) ← rewriter.createOp! (.riscv store) #[] #[addr, val]
      #[] #[] props (some $ .before op)
  rewriter.eraseOp op sorry sorry sorry

/-- `riscv.sw addr, (riscv.zextw val) -> riscv.sw addr, val`. -/
def drop_zextw_sw := drop_ext_store .zextw .sw

/-- `riscv.sw addr, (riscv.sextw val) -> riscv.sw addr, val`. -/
def drop_sextw_sw := drop_ext_store .sextw .sw

/-- Halfword- and byte-store mirrors of `drop_zextw_sw`/`drop_sextw_sw`: `sh` writes
    only bits 15:0 (matched by `zexth`/`sexth`) and `sb` only bits 7:0 (matched by
    `zextb`/`sextb`). -/
def drop_zexth_sh := drop_ext_store .zexth .sh
def drop_sexth_sh := drop_ext_store .sexth .sh
def drop_zextb_sb := drop_ext_store .zextb .sb
def drop_sextb_sb := drop_ext_store .sextb .sb
