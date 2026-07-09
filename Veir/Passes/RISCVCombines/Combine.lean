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

/-- `select c, x, x -> x`, as a `LocalRewritePattern`: no operations are created, `op`'s
    result is simply replaced by `tval`. The integer-type and bitwidth guards are what the
    correctness proof needs to reach `Data.LLVM.Int.select`; they narrow the rewrite to
    `i32`/`i64` integer selects. See `select_same_val_self_local_preservesSemantics`. -/
def select_same_val_self_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (_c, tval, fval) := matchSelect op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  if tval != fval then return (ctx, none)
  some (ctx, some (#[], #[tval]))

def select_same_val_self (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_same_val_self_local rewriter op opInBounds

/-! ### select_constant_cmp :  (1 ? x : y) → x ,  (0 ? x : y) → y -/

def select_constant_cmp_true_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tval, _fval) := matchSelect op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some cst := matchConstantIntVal cond ctx | return (ctx, none)
  if cst.value ≠ 1 then return (ctx, none)
  some (ctx, some (#[], #[tval]))

def select_constant_cmp_true (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_constant_cmp_true_local rewriter op opInBounds

def select_constant_cmp_false_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, _tval, fval) := matchSelect op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some cst := matchConstantIntVal cond ctx | return (ctx, none)
  if cst.value ≠ 0 then return (ctx, none)
  some (ctx, some (#[], #[fval]))

def select_constant_cmp_false (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_constant_cmp_false_local rewriter op opInBounds

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

-- (X << Z) & (Y << Z) → (X & Y) << Z
-- The created `shl` drops `nsw` (`X & Y` can have a sign-changing bit pattern where `Y`
-- does not) but may keep `nuw`, since the bits it shifts out are a subset of `Y`'s.
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
    #[] #[] { nsw := false, nuw := p1.nuw } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X << Z) | (Y << Z) → (X | Y) << Z
-- The created `shl` drops `nsw` and `nuw` (the bits `X | Y` shifts out can come from `X`
-- alone), and the created `or` drops `disjoint` (`X` and `Y` may overlap only in bits
-- that both shifts discard).
set_option warn.sorry false in
def OrShlShl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchShl dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchShl dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .shl) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X << Z) ^ (Y << Z) → (X ^ Y) << Z
-- The created `shl` drops `nsw` and `nuw`, as in `OrShlShl`.
set_option warn.sorry false in
def XorShlShl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchShl dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchShl dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .shl) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
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
-- The created `lshr` drops `exact` (the low bits `X | Y` discards can be nonzero because
-- of `X` alone), and the created `or` drops `disjoint` (`X` and `Y` may overlap only in
-- the discarded low bits).
set_option warn.sorry false in
def OrLshrLshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchLshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchLshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { exact := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z   (logical)
-- The created `lshr` drops `exact`, as in `OrLshrLshr`.
set_option warn.sorry false in
def XorLshrLshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchLshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchLshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { exact := false } (some $ .before op) sorry sorry sorry sorry
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
-- The created `ashr` drops `exact` and the created `or` drops `disjoint`, as in
-- `OrLshrLshr`.
set_option warn.sorry false in
def OrAshrAshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchAshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchAshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .ashr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { exact := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z   (arithmetic)
-- The created `ashr` drops `exact`, as in `XorLshrLshr`.
set_option warn.sorry false in
def XorAshrAshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, xprops) := matchXor op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _p0) := matchAshr dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _p1) := matchAshr dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .xor) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] xprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .ashr) #[x.getType! rewriter.ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] { exact := false } (some $ .before op) sorry sorry sorry sorry
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
-- The created `or` drops `disjoint`: `X` and `Y` may overlap only in bits that `Z` masks
-- off, so `(X & Z)` and `(Y & Z)` can be disjoint while `X` and `Y` are not.
set_option warn.sorry false in
def OrAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dX := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, z0, _) := matchAnd dX rewriter.ctx | return rewriter
  let some dY := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, z1, _) := matchAnd dY rewriter.ctx | return rewriter
  if z0 != z1 then return rewriter
  let (rewriter, inner) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
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
def sub_add_reg_x_add_y_sub_y_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (s0, s1, _sp) := matchSub op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some dAdd := getDefiningOp s0 ctx | return (ctx, none)
  let some (x, y, _ap) := matchAdd dAdd ctx | return (ctx, none)
  if y != s1 then return (ctx, none)
  some (ctx, some (#[], #[x]))

def sub_add_reg_x_add_y_sub_y (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_add_reg_x_add_y_sub_y_local rewriter op opInBounds

-- (x + y) - x → y
def sub_add_reg_x_add_y_sub_x_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (s0, s1, _sp) := matchSub op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some dAdd := getDefiningOp s0 ctx | return (ctx, none)
  let some (x, y, _ap) := matchAdd dAdd ctx | return (ctx, none)
  if x != s1 then return (ctx, none)
  some (ctx, some (#[], #[y]))

def sub_add_reg_x_add_y_sub_x (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_add_reg_x_add_y_sub_x_local rewriter op opInBounds

-- x - (y + x) → 0 - y
-- The created `sub` drops the matched `sub`'s `nsw`/`nuw`: `0 - y` has a different
-- overflow condition than `x - (y + x)` (e.g. `x = -1`, `y = 1` unsigned-overflows only
-- the former). See `sub_add_reg_x_sub_y_add_x` in `LLVMProofs.lean`.
set_option warn.sorry false in
def sub_add_reg_x_sub_y_add_x (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (s0, s1, _sp) := matchSub op rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp s1 rewriter.ctx | return rewriter
  let some (y, x, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  if x != s0 then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[s0.getType! rewriter.ctx.raw] #[(c0.getResult 0), y]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- x - (x + y) → 0 - y
-- The created `sub` drops `nsw`/`nuw`, as in `sub_add_reg_x_sub_y_add_x`.
set_option warn.sorry false in
def sub_add_reg_x_sub_x_add_y (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (s0, s1, _sp) := matchSub op rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp s1 rewriter.ctx | return rewriter
  let some (x, y, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  if x != s0 then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[s0.getType! rewriter.ctx.raw] #[(c0.getResult 0), y]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
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

/-! ### select_to_iminmax  (ported to LLVM min/max intrinsics — see assumption (D))

  (icmp pred X Y) ? X : Y → {u,s}{max,min} X Y
-/

/-- The shared shape of the eight `select_to_iminmax` combines: match
    `(icmp pred X Y) ? X : Y` and emit the corresponding LLVM min/max intrinsic `dst`.

    The `.integerType`/bitwidth guards are what the correctness proof needs to reach the
    `veir_bv_decide` data lemmas, so the rewrite is restricted to `i32`/`i64`. Its shared
    correctness proof is `selectToIMinMaxLocal_preservesSemantics`. -/
def selectToIMinMaxLocal (pred : Data.LLVM.IntPred) (dst : Llvm)
    (dprops : propertiesOf (.llvm dst))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some dI := getDefiningOp cond ctx | return (ctx, none)
  let some (il, ir, ip) := matchIcmp dI ctx | return (ctx, none)
  if ip.predicate != pred then return (ctx, none)
  if il != tv then return (ctx, none)
  if ir != fv then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm dst)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[tv, fv] #[] #[] dprops none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

-- ugt → umax
def select_to_iminmax_ugt (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (selectToIMinMaxLocal .ugt .intr__umax ()) rewriter op opInBounds

-- uge → umax
def select_to_iminmax_uge (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (selectToIMinMaxLocal .uge .intr__umax ()) rewriter op opInBounds

-- sgt → smax
def select_to_iminmax_sgt (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (selectToIMinMaxLocal .sgt .intr__smax ()) rewriter op opInBounds

-- sge → smax
def select_to_iminmax_sge (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (selectToIMinMaxLocal .sge .intr__smax ()) rewriter op opInBounds

-- ult → umin
def select_to_iminmax_ult (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (selectToIMinMaxLocal .ult .intr__umin ()) rewriter op opInBounds

-- ule → umin
def select_to_iminmax_ule (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (selectToIMinMaxLocal .ule .intr__umin ()) rewriter op opInBounds

-- slt → smin
def select_to_iminmax_slt (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (selectToIMinMaxLocal .slt .intr__smin ()) rewriter op opInBounds

-- sle → smin
def select_to_iminmax_sle (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (selectToIMinMaxLocal .sle .intr__smin ()) rewriter op opInBounds

-- ugt → umax

-- uge → umax

-- sgt → smax

-- sge → smax.

-- ult → umin

-- ule → umin

-- slt → smin

-- sle → smin

/-! ### cast_of_cast_combines -/

-- trunc (zext x) where trunc result type = x's type → x
def trunc_of_zext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, _tp) := matchTrunc op ctx | return (ctx, none)
  let some dZ := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _zp) := matchZext dZ ctx | return (ctx, none)
  if (op.getResult 0 : ValuePtr).getType! ctx.raw != x.getType! ctx.raw then return (ctx, none)
  let .integerType xt := (x.getType! ctx.raw).val | return (ctx, none)
  let .integerType zt := (v0.getType! ctx.raw).val | return (ctx, none)
  if xt.bitwidth ≠ 32 ∨ zt.bitwidth ≠ 64 then return (ctx, none)
  some (ctx, some (#[], #[x]))

def trunc_of_zext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite trunc_of_zext_local rewriter op opInBounds

/-! ### select_of_{zext,truncate} : cast(select c,t,f) → select c, cast t, cast f -/

set_option warn.sorry false in
def select_of_zext_rw (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, zp) := matchZext op rewriter.ctx | return rewriter
  let some dS := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (cond, tv, fv) := matchSelect dS rewriter.ctx | return rewriter
  let outTy := (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw
  let (rewriter, zt) ← rewriter.createOp (.llvm .zext) #[outTy] #[tv]
    #[] #[] zp (some $ .before op) sorry sorry sorry sorry
  let (rewriter, zf) ← rewriter.createOp (.llvm .zext) #[outTy] #[fv]
    #[] #[] zp (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .select) #[outTy] #[cond, (zt.getResult 0), (zf.getResult 0)]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def select_of_truncate_rw (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, tp) := matchTrunc op rewriter.ctx | return rewriter
  let some dS := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (cond, tv, fv) := matchSelect dS rewriter.ctx | return rewriter
  let outTy := (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw
  let (rewriter, tt) ← rewriter.createOp (.llvm .trunc) #[outTy] #[tv]
    #[] #[] tp (some $ .before op) sorry sorry sorry sorry
  let (rewriter, tf) ← rewriter.createOp (.llvm .trunc) #[outTy] #[fv]
    #[] #[] tp (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .select) #[outTy] #[cond, (tt.getResult 0), (tf.getResult 0)]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### matchMulOBy2 :  (mul x, 2) → (add x, x)   (overflow flags threaded via props)
-/

/-- `x * 2 -> x + x`, as a `LocalRewritePattern`. Unlike the value-replacement combines
    above, this one creates an operation, so its proof additionally replays that operation
    forward in the target state (via `interpretOp_llvm_binaryInt_forward`). See
    `mulo_by_2_unsigned_signed_local_preservesSemantics`. -/
def mulo_by_2_unsigned_signed_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, cval, mp) := matchMul op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some cst := matchConstantIntVal cval ctx | return (ctx, none)
  if cst.value ≠ 2 then return (ctx, none)
  let (ctx, addOp) ← WfRewriter.createOp! ctx (.llvm .add) #[x.getType! ctx.raw] #[x, x]
    #[] #[] mp none
  some (ctx, some (#[addOp], #[addOp.getResult 0]))

def mulo_by_2_unsigned_signed (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mulo_by_2_unsigned_signed_local rewriter op opInBounds

/-! ### add_shift :  A + shl(0 - B, C) → A - shl(B, C) -/

-- The created `shl` drops the matched `shl`'s `nsw`/`nuw` (it now shifts `B` rather than
-- `0 - B`, which overflows differently), and the created `sub` drops the inner `sub`'s
-- `nsw`/`nuw` (those described `0 - B`, not `A - shl(B, C)`). See `add_shift` in
-- `LLVMProofs.lean`.
set_option warn.sorry false in
def add_shift (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (a, shlNeg, _ap) := matchAdd op rewriter.ctx | return rewriter
  let some dShl := getDefiningOp shlNeg rewriter.ctx | return rewriter
  let some (negB, c, _shp) := matchShl dShl rewriter.ctx | return rewriter
  let some dSub := getDefiningOp negB rewriter.ctx | return rewriter
  let some (zeroV, b, _subp) := matchSub dSub rewriter.ctx | return rewriter
  let some zc := matchConstantIntVal zeroV rewriter.ctx | return rewriter
  if zc.value ≠ 0 then return rewriter
  let (rewriter, newShl) ← rewriter.createOp (.llvm .shl) #[b.getType! rewriter.ctx.raw] #[b, c]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (newShl.getResult 0)]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- A + shl(0 - B, C) → A - shl(B, C)   (add operands commuted)
-- The created `shl` and `sub` drop their flags, as in `add_shift`.
set_option warn.sorry false in
def add_shift_commute (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (shlNeg, a, _ap) := matchAdd op rewriter.ctx | return rewriter
  let some dShl := getDefiningOp shlNeg rewriter.ctx | return rewriter
  let some (negB, c, _shp) := matchShl dShl rewriter.ctx | return rewriter
  let some dSub := getDefiningOp negB rewriter.ctx | return rewriter
  let some (zeroV, b, _subp) := matchSub dSub rewriter.ctx | return rewriter
  let some zc := matchConstantIntVal zeroV rewriter.ctx | return rewriter
  if zc.value ≠ 0 then return rewriter
  let (rewriter, newShl) ← rewriter.createOp (.llvm .shl) #[b.getType! rewriter.ctx.raw] #[b, c]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (newShl.getResult 0)]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### redundant_binop_in_equality

  ((X op Y) cmp X) → (Y cmp 0)  for op ∈ {+, -, ^}, cmp ∈ {==, !=}.
-/

set_option warn.sorry false in
def redundant_binop_in_equality_XPlusYEqX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhsV, xval, ip) := matchIcmp op rewriter.ctx | return rewriter
  let .eq := ip.predicate | return rewriter
  let some dAdd := getDefiningOp lhsV rewriter.ctx | return rewriter
  let some (x, y, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  if x != xval then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def redundant_binop_in_equality_XPlusYNeX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhsV, xval, ip) := matchIcmp op rewriter.ctx | return rewriter
  let .ne := ip.predicate | return rewriter
  let some dAdd := getDefiningOp lhsV rewriter.ctx | return rewriter
  let some (x, y, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  if x != xval then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def redundant_binop_in_equality_XMinusYEqX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhsV, xval, ip) := matchIcmp op rewriter.ctx | return rewriter
  let .eq := ip.predicate | return rewriter
  let some dSub := getDefiningOp lhsV rewriter.ctx | return rewriter
  let some (x, y, _sp) := matchSub dSub rewriter.ctx | return rewriter
  if x != xval then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def redundant_binop_in_equality_XMinusYNeX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhsV, xval, ip) := matchIcmp op rewriter.ctx | return rewriter
  let .ne := ip.predicate | return rewriter
  let some dSub := getDefiningOp lhsV rewriter.ctx | return rewriter
  let some (x, y, _sp) := matchSub dSub rewriter.ctx | return rewriter
  if x != xval then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def redundant_binop_in_equality_XXorYEqX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhsV, xval, ip) := matchIcmp op rewriter.ctx | return rewriter
  let .eq := ip.predicate | return rewriter
  let some dXor := getDefiningOp lhsV rewriter.ctx | return rewriter
  let some (x, y, _xp) := matchXor dXor rewriter.ctx | return rewriter
  if x != xval then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def redundant_binop_in_equality_XXorYNeX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhsV, xval, ip) := matchIcmp op rewriter.ctx | return rewriter
  let .ne := ip.predicate | return rewriter
  let some dXor := getDefiningOp lhsV rewriter.ctx | return rewriter
  let some (x, y, _xp) := matchXor dXor rewriter.ctx | return rewriter
  if x != xval then return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### match_selects -/

-- select c, 1, 0 → zext c
set_option warn.sorry false in
def select_1_0 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some ct := matchConstantIntVal tv rewriter.ctx | return rewriter
  if ct.value ≠ 1 then return rewriter
  let some cf := matchConstantIntVal fv rewriter.ctx | return rewriter
  if cf.value ≠ 0 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[cond]
    #[] #[] { nneg := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- select c, -1, 0 → sext c
set_option warn.sorry false in
def select_neg1_0 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some ct := matchConstantIntVal tv rewriter.ctx | return rewriter
  if ct.value ≠ -1 then return rewriter
  let some cf := matchConstantIntVal fv rewriter.ctx | return rewriter
  if cf.value ≠ 0 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[cond]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- select c, 0, 1 → zext (not c)
set_option warn.sorry false in
def select_0_1 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some ct := matchConstantIntVal tv rewriter.ctx | return rewriter
  if ct.value ≠ 0 then return rewriter
  let some cf := matchConstantIntVal fv rewriter.ctx | return rewriter
  if cf.value ≠ 1 then return rewriter
  let .integerType cty := (cond.getType! rewriter.ctx.raw).val | return rewriter
  let m1 := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) cty))
  let (rewriter, c1) ← rewriter.createOp (.llvm .mlir__constant) #[cond.getType! rewriter.ctx.raw] #[]
    #[] #[] m1 (some $ .before op) sorry sorry sorry sorry
  let (rewriter, ncond) ← rewriter.createOp (.llvm .xor) #[cond.getType! rewriter.ctx.raw] #[cond, (c1.getResult 0)]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(ncond.getResult 0)]
    #[] #[] { nneg := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- select c, 0, -1 → sext (not c)
set_option warn.sorry false in
def select_0_neg1 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some ct := matchConstantIntVal tv rewriter.ctx | return rewriter
  if ct.value ≠ 0 then return rewriter
  let some cf := matchConstantIntVal fv rewriter.ctx | return rewriter
  if cf.value ≠ -1 then return rewriter
  let .integerType cty := (cond.getType! rewriter.ctx.raw).val | return rewriter
  let m1 := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) cty))
  let (rewriter, c1) ← rewriter.createOp (.llvm .mlir__constant) #[cond.getType! rewriter.ctx.raw] #[]
    #[] #[] m1 (some $ .before op) sorry sorry sorry sorry
  let (rewriter, ncond) ← rewriter.createOp (.llvm .xor) #[cond.getType! rewriter.ctx.raw] #[cond, (c1.getResult 0)]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(ncond.getResult 0)]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### not_cmp_fold :  (icmp pred X Y) ^ -1 → (icmp invPred X Y) -/

/-- The shared shape of the six `not_cmp_fold` combines: match `(icmp pred X Y) ^ -1`
    (`op` is the `xor _, -1`, reached with `matchNot`, whose operand is the `icmp`'s result)
    and emit the comparison with the inverted predicate `invPred`.

    The `.integerType`/bitwidth guard on the comparison operand type is what the correctness
    proof needs to reach the `veir_bv_decide` data lemmas, so the rewrite is restricted to
    `i32`/`i64` comparisons. Its shared correctness proof is
    `notCmpFoldLocal_preservesSemantics`. -/
def notCmpFoldLocal (pred invPred : Data.LLVM.IntPred)
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some icmpV := matchNot (op.getResult 0) ctx | return (ctx, none)
  let some dI := getDefiningOp icmpV ctx | return (ctx, none)
  let some (x, y, ip) := matchIcmp dI ctx | return (ctx, none)
  if ip.predicate != pred then return (ctx, none)
  let .integerType t := (x.getType! ctx.raw).val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y] #[] #[]
    (IcmpProperties.mk invPred) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def not_cmp_fold_eq (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (notCmpFoldLocal .eq .ne) rewriter op opInBounds

def not_cmp_fold_ne (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (notCmpFoldLocal .ne .eq) rewriter op opInBounds

def not_cmp_fold_ugt (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (notCmpFoldLocal .ugt .ule) rewriter op opInBounds

def not_cmp_fold_uge (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (notCmpFoldLocal .uge .ult) rewriter op opInBounds

def not_cmp_fold_sgt (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (notCmpFoldLocal .sgt .sle) rewriter op opInBounds

def not_cmp_fold_sge (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (notCmpFoldLocal .sge .slt) rewriter op opInBounds

/-! ### double_icmp_zero_combine -/

-- (X == 0 & Y == 0) → (X | Y) == 0
set_option warn.sorry false in
def double_icmp_zero_and_combine (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, _andprops) := matchAnd op rewriter.ctx | return rewriter
  let some dL := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, cx, ip0) := matchIcmp dL rewriter.ctx | return rewriter
  let .eq := ip0.predicate | return rewriter
  let some cxv := matchConstantIntVal cx rewriter.ctx | return rewriter
  if cxv.value ≠ 0 then return rewriter
  let some dR := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, cy, ip1) := matchIcmp dR rewriter.ctx | return rewriter
  let .eq := ip1.predicate | return rewriter
  let some cyv := matchConstantIntVal cy rewriter.ctx | return rewriter
  if cyv.value ≠ 0 then return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) xty))
  let (rewriter, orOp) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] { disjoint := false } (some $ .before op) sorry sorry sorry sorry
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(orOp.getResult 0), (c0.getResult 0)]
    #[] #[] ip0 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- (X != 0 | Y != 0) → (X | Y) != 0
set_option warn.sorry false in
def double_icmp_zero_or_combine (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, v1, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dL := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, cx, ip0) := matchIcmp dL rewriter.ctx | return rewriter
  let .ne := ip0.predicate | return rewriter
  let some cxv := matchConstantIntVal cx rewriter.ctx | return rewriter
  if cxv.value ≠ 0 then return rewriter
  let some dR := getDefiningOp v1 rewriter.ctx | return rewriter
  let some (y, cy, ip1) := matchIcmp dR rewriter.ctx | return rewriter
  let .ne := ip1.predicate | return rewriter
  let some cyv := matchConstantIntVal cy rewriter.ctx | return rewriter
  if cyv.value ≠ 0 then return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) xty))
  let (rewriter, orOp) ← rewriter.createOp (.llvm .or) #[x.getType! rewriter.ctx.raw] #[x, y]
    #[] #[] oprops (some $ .before op) sorry sorry sorry sorry
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(orOp.getResult 0), (c0.getResult 0)]
    #[] #[] ip0 (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### NotAPlusNegOne :  (not (add X, -1)) → (sub 0, X) -/

set_option warn.sorry false in
def NotAPlusNegOne_rw (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some addVal := matchNot (op.getResult 0) rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp addVal rewriter.ctx | return rewriter
  let some (x, cm1, ap) := matchAdd dAdd rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal cm1 rewriter.ctx | return rewriter
  if cst.value ≠ -1 then return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) xty))
  let (rewriter, c0) ← rewriter.createOp (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[x.getType! rewriter.ctx.raw] #[(c0.getResult 0), x]
    #[] #[] ap (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### sub_one_from_sub :  (A - B) - 1 → add (xor B, -1), A -/

-- The created `add` drops the matched `sub`'s `nsw`/`nuw`: `(~B) + A` has a different
-- overflow condition than `(A - B) - 1` (e.g. `A = 5`, `B = 3` unsigned-overflows only
-- the former). See `sub_one_from_sub_rw` in `LLVMProofs.lean`.
set_option warn.sorry false in
def sub_one_from_sub_rw (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (subVal, c1v, _sp) := matchSub op rewriter.ctx | return rewriter
  let some cst1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  if cst1.value ≠ 1 then return rewriter
  let some dSub := getDefiningOp subVal rewriter.ctx | return rewriter
  let some (x, y, _sp2) := matchSub dSub rewriter.ctx | return rewriter
  let .integerType yty := (y.getType! rewriter.ctx.raw).val | return rewriter
  let m1 := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) yty))
  let (rewriter, cm1) ← rewriter.createOp (.llvm .mlir__constant) #[y.getType! rewriter.ctx.raw] #[]
    #[] #[] m1 (some $ .before op) sorry sorry sorry sorry
  let (rewriter, xorOp) ← rewriter.createOp (.llvm .xor) #[y.getType! rewriter.ctx.raw] #[y, (cm1.getResult 0)]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(xorOp.getResult 0), x]
    #[] #[] { nsw := false, nuw := false } (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

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

/-- Byte- and half-word mirrors of `zextw_zextw`/`sextw_sextw`. Each extension is
    idempotent (`ext (ext x) = ext x`) regardless of width, since the inner op
    already establishes exactly the high-bit pattern the outer one would. -/
def zextb_zextb := drop_redundant_ext .zextb
def zexth_zexth := drop_redundant_ext .zexth
def sextb_sextb := drop_redundant_ext .sextb
def sexth_sexth := drop_redundant_ext .sexth

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
     , zextb_zextb
     , zexth_zexth
     , sextb_sextb
     , sexth_sexth
     , zextb_and
     , zextb_or
     , zextb_xor
     , zexth_and
     , zexth_or
     , zexth_xor
     , sextb_and
     , sextb_or
     , sextb_xor
     , sexth_and
     , sexth_or
     , sexth_xor
     , drop_zexth_sh
     , drop_sexth_sh
     , drop_zextb_sb
     , drop_sextb_sb
     , zextb_x0
     , zexth_x0
     , sextb_x0
     , sexth_x0
     , zextb_li_low8
     , zexth_li_low16
     , sextb_li_low8
     , sexth_li_low16
     , li_zero_to_x0
     , select_same_val_self
     , select_constant_cmp_true
     , select_constant_cmp_false
     , AndSextSext
     , OrSextSext
     , XorSextSext
     , AndZextZext
     , OrZextZext
     , XorZextZext
     , AndTruncTrunc
     , OrTruncTrunc
     , XorTruncTrunc
     , AndShlShl
     , OrShlShl
     , XorShlShl
     , AndLshrLshr
     , OrLshrLshr
     , XorLshrLshr
     , AndAshrAshr
     , OrAshrAshr
     , XorAshrAshr
     , AndAndAnd
     , OrAndAnd
     , XorAndAnd
     , sub_add_reg_x_add_y_sub_y
     , sub_add_reg_x_add_y_sub_x
     , sub_add_reg_x_sub_y_add_x
     , sub_add_reg_x_sub_x_add_y
     , xor_of_and_with_same_reg
     , select_to_iminmax_ugt
     , select_to_iminmax_uge
     , select_to_iminmax_sgt
     , select_to_iminmax_sge
     , select_to_iminmax_ult
     , select_to_iminmax_ule
     , select_to_iminmax_slt
     , select_to_iminmax_sle
     , trunc_of_zext
     , select_of_zext_rw
     , select_of_truncate_rw
     , mulo_by_2_unsigned_signed
     , add_shift
     , add_shift_commute
     , redundant_binop_in_equality_XPlusYEqX
     , redundant_binop_in_equality_XPlusYNeX
     , redundant_binop_in_equality_XMinusYEqX
     , redundant_binop_in_equality_XMinusYNeX
     , redundant_binop_in_equality_XXorYEqX
     , redundant_binop_in_equality_XXorYNeX
     , select_1_0
     , select_neg1_0
     , select_0_1
     , select_0_neg1
     , not_cmp_fold_eq
     , not_cmp_fold_ne
     , not_cmp_fold_ugt
     , not_cmp_fold_uge
     , not_cmp_fold_sgt
     , not_cmp_fold_sge
     , double_icmp_zero_and_combine
     , double_icmp_zero_or_combine
     , NotAPlusNegOne_rw
     , sub_one_from_sub_rw
     ]
  let pattern := RewritePattern.GreedyRewritePattern patterns
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
