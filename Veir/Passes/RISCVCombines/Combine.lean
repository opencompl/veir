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

/-- If `val` is defined by a `riscv.<ext>` op (`ext` being `zextw`/`sextw`),
    return its source operand and `true`; otherwise `val` unchanged and `false`. -/
private def stripDefiningExt (ext : Riscv) (val : ValuePtr) (ctx : IRContext OpCode) :
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

/-- Match `riscv.sw addr, val`, returning `(addr, val, properties)`. `riscv.sw`
    has no results, so it can't go through `matchOp` (which requires exactly
    one). -/
private def matchRiscvSw (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sw)) := do
  guard (op.getOpType! ctx = .riscv .sw)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx (.riscv .sw)
  return (operands[0]!, operands[1]!, properties)

set_option warn.sorry false in
/-- Drop a `riscv.<ext>` (`zextw`/`sextw`) from the value operand of `riscv.sw`. A
    word store only writes bits 31:0 of its source register (see the `.sw` case of
    `Interpreter.Basic.exec`, which stores just the low 4 bytes), and neither
    extension changes those bits -- they only rewrite bits 63:32 -- so extending
    the stored value first is redundant. The address operand is left untouched: it
    needs the full 64 bits.

    LLVM: the `SW` case of `hasAllNBitUsers` demands only the low 32 bits of the
    store's value operand (operand index 0), and nothing of the address.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L304-L311 -/
private def drop_ext_sw (ext : Riscv) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (addr, val, props) := matchRiscvSw op rewriter.ctx | return rewriter
  let (val, changed) := stripDefiningExt ext val rewriter.ctx
  if !changed then return rewriter
  let (rewriter, _newOp) ← rewriter.createOp! (.riscv .sw) #[] #[addr, val]
      #[] #[] props (some $ .before op)
  rewriter.eraseOp op sorry sorry sorry

/-- `riscv.sw addr, (riscv.zextw val) -> riscv.sw addr, val`. -/
def drop_zextw_sw := drop_ext_sw .zextw

/-- `riscv.sw addr, (riscv.sextw val) -> riscv.sw addr, val`. -/
def drop_sextw_sw := drop_ext_sw .sextw

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

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let patterns : Array (RewritePattern OpCode) :=
    #[ right_identity_zero_add
     , srl_sra_signbit
     , srlw_sraw_signbit
     , drop_slli_srli_slt
     , drop_slli_srli_sltu
     , drop_slli_srli_slti
     , drop_slli_srli_sltiu
     , drop_slli_srli_seqz
     , drop_slli_srli_snez
     , drop_slli_srli_sltz
     , drop_slli_srli_sgtz
     , zextw_zextw
     , drop_zextw_addw
     , drop_zextw_addiw
     , drop_zextw_roriw
     , drop_zextw_srliw
     , drop_zextw_sextw
     , zextw_and
     , zextw_or
     , zextw_xor
     , drop_zextw_sw
     , zextw_x0
     , zextw_li_low32
     , sextw_sextw
     , drop_sextw_addw
     , drop_sextw_addiw
     , drop_sextw_roriw
     , drop_sextw_srliw
     , drop_sextw_zextw
     , sextw_and
     , sextw_or
     , sextw_xor
     , drop_sextw_sw
     , sextw_x0
     , sextw_li_low32
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
