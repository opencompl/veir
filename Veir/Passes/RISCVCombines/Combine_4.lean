import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

/-! ### cast_of_cast_combines -/

-- trunc (zext x) where trunc result type = x's type → x
set_option warn.sorry false in
def trunc_of_zext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, _tp) := matchTrunc op rewriter.ctx | return rewriter
  let some dZ := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _zp) := matchZext dZ rewriter.ctx | return rewriter
  if (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw != x.getType! rewriter.ctx.raw then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) x sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

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

set_option warn.sorry false in
def mulo_by_2_unsigned_signed (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, cval, mp) := matchMul op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal cval rewriter.ctx | return rewriter
  if cst.value ≠ 2 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[x.getType! rewriter.ctx.raw] #[x, x]
    #[] #[] mp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

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
