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
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sext) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0)]
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
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sext) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0)]
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
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sext) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0)]
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
  let (rewriter, newOp) ← rewriter.createOp (.llvm .zext) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (zext X) | (zext Y) → zext (X | Y)
set_option warn.sorry false in
def OrZextZext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchZext dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, yp) := matchZext dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] oprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .zext) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (zext X) ^ (zext Y) → zext (X ^ Y)
set_option warn.sorry false in
def XorZextZext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchZext dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, yp) := matchZext dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .zext) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (trunc X) & (trunc Y) → trunc (X & Y)
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
  let (rewriter, newOp) ← rewriter.createOp (.llvm .trunc) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (trunc X) | (trunc Y) → trunc (X | Y)
set_option warn.sorry false in
def OrTruncTrunc (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchTrunc dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, yp) := matchTrunc dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] oprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .trunc) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (trunc X) ^ (trunc Y) → trunc (X ^ Y)
set_option warn.sorry false in
def XorTruncTrunc (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _xp) := matchTrunc dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, yp) := matchTrunc dY rewriter.ctx | return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .trunc) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X << Z) & (Y << Z) → (X & Y) << Z
set_option warn.sorry false in
def AndShlShl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchShl dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchShl dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .shl) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X << Z) | (Y << Z) → (X | Y) << Z
set_option warn.sorry false in
def OrShlShl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchShl dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchShl dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] oprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .shl) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X << Z) ^ (Y << Z) → (X ^ Y) << Z
set_option warn.sorry false in
def XorShlShl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchShl dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchShl dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .shl) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) & (Y >> Z) → (X & Y) >> Z   (logical)
set_option warn.sorry false in
def AndLshrLshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchLshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchLshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) | (Y >> Z) → (X | Y) >> Z   (logical)
set_option warn.sorry false in
def OrLshrLshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchLshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchLshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] oprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z   (logical)
set_option warn.sorry false in
def XorLshrLshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchLshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchLshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) & (Y >> Z) → (X & Y) >> Z   (arithmetic)
set_option warn.sorry false in
def AndAshrAshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchAshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchAshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .ashr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) | (Y >> Z) → (X | Y) >> Z   (arithmetic)
set_option warn.sorry false in
def OrAshrAshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchAshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchAshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] oprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .ashr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z   (arithmetic)
set_option warn.sorry false in
def XorAshrAshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchAshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, p1) := matchAshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .ashr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X & Z) & (Y & Z) → (X & Y) & Z
set_option warn.sorry false in
def AndAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _) := matchAnd op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _) := matchAnd dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _) := matchAnd dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X & Z) | (Y & Z) → (X | Y) & Z
set_option warn.sorry false in
def OrAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _) := matchAnd dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _) := matchAnd dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] oprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X & Z) ^ (Y & Z) → (X ^ Y) & Z
set_option warn.sorry false in
def XorAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _) := matchAnd dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _) := matchAnd dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### sub_add_reg -/

-- (x + y) - y → x
set_option warn.sorry false in
def sub_add_reg_x_add_y_sub_y (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (s0, s1, _sp) := matchSub op rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp s0 rewriter.ctx | return rewriter
  let some (x, y, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  if y != s1 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) x sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

-- (x + y) - x → y
set_option warn.sorry false in
def sub_add_reg_x_add_y_sub_x (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (s0, s1, _sp) := matchSub op rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp s0 rewriter.ctx | return rewriter
  let some (x, y, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  if x != s1 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) y sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

-- x - (y + x) → 0 - y
set_option warn.sorry false in
def sub_add_reg_x_sub_y_add_x (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (s0, s1, sp) := matchSub op rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp s1 rewriter.ctx | return rewriter
  let some (y, x, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  if x != s0 then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[s0.getType! rewriter.ctx.raw] #[(c0.getResult 0), y]
    #[] #[] sp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- x - (x + y) → 0 - y
set_option warn.sorry false in
def sub_add_reg_x_sub_x_add_y (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (s0, s1, sp) := matchSub op rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp s1 rewriter.ctx | return rewriter
  let some (x, y, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  if x != s0 then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[s0.getType! rewriter.ctx.raw] #[(c0.getResult 0), y]
    #[] #[] sp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### xor_of_and_with_same_reg :  (xor (and x, y), y) → (and (not x), y) -/

set_option warn.sorry false in
def xor_of_and_with_same_reg (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (andVal, yval, _xp) := matchXor op rewriter.ctx | return rewriter
  let some dA := getDefiningOp andVal rewriter.ctx | return rewriter
  let some (x, y2, _) := matchAnd dA rewriter.ctx | return rewriter
  if y2 != yval then return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let m1 := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) xty))
  let (rewriter, c1) ← rewriter.createOp (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] m1 (some $ .before op) sorry sorry sorry sorry
  let (rewriter, notx) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, (c1.getResult 0)]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .and) #[x.getType! rewriter.ctx.raw] #[(notx.getResult 0), yval]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry


def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let patterns : Array (RewritePattern OpCode) := #[right_identity_zero_add,
    select_same_val_self, select_constant_cmp_true, select_constant_cmp_false,
    AndSextSext, OrSextSext, XorSextSext,
    AndZextZext, OrZextZext, XorZextZext,
    AndTruncTrunc, OrTruncTrunc, XorTruncTrunc,
    AndShlShl, OrShlShl, XorShlShl,
    AndLshrLshr, OrLshrLshr, XorLshrLshr,
    AndAshrAshr, OrAshrAshr, XorAshrAshr,
    AndAndAnd, OrAndAnd, XorAndAnd,
    sub_add_reg_x_add_y_sub_y, sub_add_reg_x_add_y_sub_x,
    sub_add_reg_x_sub_y_add_x, sub_add_reg_x_sub_x_add_y,
    xor_of_and_with_same_reg]
  let pattern := RewritePattern.GreedyRewritePattern patterns
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
