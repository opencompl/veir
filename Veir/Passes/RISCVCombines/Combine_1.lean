import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

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

/-! ### select_same_val :  (c ? x : x) → x -/

set_option warn.sorry false in
def select_same_val_self (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (_c, tval, fval) := matchSelect op rewriter.ctx | return rewriter
  if tval != fval then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) tval sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ### select_constant_cmp :  (1 ? x : y) → x ,  (0 ? x : y) → y -/

set_option warn.sorry false in
def select_constant_cmp_true (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tval, _fval) := matchSelect op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal cond rewriter.ctx | return rewriter
  if cst.value ≠ 1 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) tval sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def select_constant_cmp_false (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, _tval, fval) := matchSelect op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal cond rewriter.ctx | return rewriter
  if cst.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) fval sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ### hoist_logic_op_with_same_opcode_hands-/

-- (sext X) & (sext Y) → sext (X & Y)
set_option warn.sorry false in
def AndSextSext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchSext dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, yp) := matchSext dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (sext X) | (sext Y) → sext (X | Y)
set_option warn.sorry false in
def OrSextSext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchSext dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, yp) := matchSext dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] oprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (sext X) ^ (sext Y) → sext (X ^ Y)
set_option warn.sorry false in
def XorSextSext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchSext dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, yp) := matchSext dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (zext X) & (zext Y) → zext (X & Y)
set_option warn.sorry false in
def AndZextZext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchZext dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, yp) := matchZext dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (zext X) | (zext Y) → zext (X | Y)
-- The created `zext` drops `nneg`: `X | Y` can have its msb set because of `X` alone, so
-- keeping `Y`'s `nneg` would poison a result the source computes fine. See `OrZextZext`
-- in `LLVMProofs.lean`.
set_option warn.sorry false in
def OrZextZext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchZext dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, _yp) := matchZext dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] oprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] { nneg := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (zext X) ^ (zext Y) → zext (X ^ Y)
-- The created `zext` drops `nneg`, for the same reason as `OrZextZext`.
set_option warn.sorry false in
def XorZextZext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchZext dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, _yp) := matchZext dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] { nneg := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (trunc X) & (trunc Y) → trunc (X & Y)
-- The created `trunc` drops `nsw` (the bits `X & Y` discards need not agree with its sign
-- bit even when `Y`'s do) but may keep `nuw`, since those bits are a subset of `Y`'s.
set_option warn.sorry false in
def AndTruncTrunc (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchTrunc dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, yp) := matchTrunc dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .trunc) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] { nsw := false, nuw := yp.nuw } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (trunc X) | (trunc Y) → trunc (X | Y)
-- The created `trunc` drops both `nsw` and `nuw` (the discarded high bits of `X | Y` can
-- come from `X` alone), and the created `or` drops `disjoint` (`X` and `Y` may overlap
-- only in bits the truncation discards).
set_option warn.sorry false in
def OrTruncTrunc (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchTrunc dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, _yp) := matchTrunc dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .trunc) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (trunc X) ^ (trunc Y) → trunc (X ^ Y)
-- The created `trunc` drops both `nsw` and `nuw`, as in `OrTruncTrunc`.
set_option warn.sorry false in
def XorTruncTrunc (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchTrunc dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, _yp) := matchTrunc dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .trunc) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry
