import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

/-! ### select_not :  select (not c), x, y → select c, y, x -/

set_option warn.sorry false in
def select_not (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some dC := getDefiningOp cond rewriter.ctx | return rewriter
  let some (c, m1v, _) := matchXor dC rewriter.ctx | return rewriter
  let some m1 := matchConstantIntVal m1v rewriter.ctx | return rewriter
  if m1.value ≠ -1 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .select) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[c, fv, tv]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### commute_int_constant_to_rhs :  (C op x) → (x op C)   (move constant to the right) -/

set_option warn.sorry false in
def commute_const_add (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, props) := matchAdd op rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal lhs rewriter.ctx | return rewriter
  if (matchConstantIntVal rhs rewriter.ctx).isSome then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[rhs, lhs]
    #[] #[] props (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def commute_const_mul (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, props) := matchMul op rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal lhs rewriter.ctx | return rewriter
  if (matchConstantIntVal rhs rewriter.ctx).isSome then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .mul) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[rhs, lhs]
    #[] #[] props (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def commute_const_and (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchAnd op rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal lhs rewriter.ctx | return rewriter
  if (matchConstantIntVal rhs rewriter.ctx).isSome then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .and) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[rhs, lhs]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def commute_const_or (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, props) := matchOr op rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal lhs rewriter.ctx | return rewriter
  if (matchConstantIntVal rhs rewriter.ctx).isSome then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .or) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[rhs, lhs]
    #[] #[] props (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def commute_const_xor (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchXor op rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal lhs rewriter.ctx | return rewriter
  if (matchConstantIntVal rhs rewriter.ctx).isSome then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .xor) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[rhs, lhs]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### simplify_neg_minmax :  0 - (minmax a, (0 - a)) → oppositeMinMax a, (0 - a)

  Completes the smin/umin input cases of LLVM's `simplify_neg_minmax` (rule #184);
  the smax/umax input cases are handled by `SubSmaxSub` / `SubUmaxSub`. Mirrors
  `getInverseGMinMaxOpcode`: smin → smax, umin → umax. -/

set_option warn.sorry false in
def SubSminSub (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zeroOuter, minV, sprops) := matchSub op rewriter.ctx | return rewriter
  let some _ := matchConstantZero zeroOuter rewriter.ctx | return rewriter
  let some dMin := getDefiningOp minV rewriter.ctx | return rewriter
  let some (a, subV) := matchSmin dMin rewriter.ctx | return rewriter
  let some dSub := getDefiningOp subV rewriter.ctx | return rewriter
  let some (zeroInner, a2, _) := matchSub dSub rewriter.ctx | return rewriter
  let some _ := matchConstantZero zeroInner rewriter.ctx | return rewriter
  if a2 != a then return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 aty))
  let (rewriter, c0) ← rewriter.createOp! (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op)
  let (rewriter, sub1) ← rewriter.createOp! (.llvm .sub) #[a.getType! rewriter.ctx.raw] #[(c0.getResult 0), a]
    #[] #[] sprops (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .intr__smax) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (sub1.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def SubUminSub (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zeroOuter, minV, sprops) := matchSub op rewriter.ctx | return rewriter
  let some _ := matchConstantZero zeroOuter rewriter.ctx | return rewriter
  let some dMin := getDefiningOp minV rewriter.ctx | return rewriter
  let some (a, subV) := matchUmin dMin rewriter.ctx | return rewriter
  let some dSub := getDefiningOp subV rewriter.ctx | return rewriter
  let some (zeroInner, a2, _) := matchSub dSub rewriter.ctx | return rewriter
  let some _ := matchConstantZero zeroInner rewriter.ctx | return rewriter
  if a2 != a then return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 aty))
  let (rewriter, c0) ← rewriter.createOp! (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] z (some $ .before op)
  let (rewriter, sub1) ← rewriter.createOp! (.llvm .sub) #[a.getType! rewriter.ctx.raw] #[(c0.getResult 0), a]
    #[] #[] sprops (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .intr__umax) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (sub1.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp
