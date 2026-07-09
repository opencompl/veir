import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

/-! ### SubSmaxSub / SubUmaxSub

  `(sub 0, (max X, (sub 0, X)))` → `(min X, (sub 0, X))`, where `(max, min)` is
  `(smax, smin)` in the signed case and `(umax, umin)` in the unsigned case.

  Matching LLVM's `SubSmaxSub` / `SubUmaxSub` GICombineRules, the inner
  `sub 0, X` is rebuilt so the min can consume it directly. -/

set_option warn.sorry false in
def SubSmaxSub (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zeroOuter, maxV, sprops) := matchSub op rewriter.ctx | return rewriter
  let some _ := matchConstantZero zeroOuter rewriter.ctx | return rewriter
  let some dMax := getDefiningOp maxV rewriter.ctx | return rewriter
  let some (a, subV) := matchSmax dMax rewriter.ctx | return rewriter
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
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .intr__smin) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (sub1.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def SubUmaxSub (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zeroOuter, maxV, sprops) := matchSub op rewriter.ctx | return rewriter
  let some _ := matchConstantZero zeroOuter rewriter.ctx | return rewriter
  let some dMax := getDefiningOp maxV rewriter.ctx | return rewriter
  let some (a, subV) := matchUmax dMax rewriter.ctx | return rewriter
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
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .intr__umin) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (sub1.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### narrow_binop :  trunc (binop X, C) → binop (trunc X, trunc C)

  A binop matched on a constant second operand is narrowed by pushing the outer
  `trunc` onto each operand and redoing the binop at the trunc's width. The outer
  trunc's own `nsw`/`nuw` flags are reused for the operand truncations. -/

-- trunc (add X, C) → add (trunc X, trunc C)
set_option warn.sorry false in
def narrow_binop_add (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, tp) := matchTrunc op rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, cst, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal cst rewriter.ctx | return rewriter
  let outTy := (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw
  let (rewriter, tx) ← rewriter.createOp! (.llvm .trunc) #[outTy] #[x]
    #[] #[] tp (some $ .before op)
  let (rewriter, tc) ← rewriter.createOp! (.llvm .trunc) #[outTy] #[cst]
    #[] #[] tp (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .add) #[outTy] #[(tx.getResult 0), (tc.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) (some $ .before op)
  return rewriter.replaceOp! op newOp

-- trunc (sub X, C) → sub (trunc X, trunc C)
set_option warn.sorry false in
def narrow_binop_sub (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, tp) := matchTrunc op rewriter.ctx | return rewriter
  let some dSub := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, cst, _sp) := matchSub dSub rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal cst rewriter.ctx | return rewriter
  let outTy := (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw
  let (rewriter, tx) ← rewriter.createOp! (.llvm .trunc) #[outTy] #[x]
    #[] #[] tp (some $ .before op)
  let (rewriter, tc) ← rewriter.createOp! (.llvm .trunc) #[outTy] #[cst]
    #[] #[] tp (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .sub) #[outTy] #[(tx.getResult 0), (tc.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) (some $ .before op)
  return rewriter.replaceOp! op newOp

-- trunc (mul X, C) → mul (trunc X, trunc C)
set_option warn.sorry false in
def narrow_binop_mul (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, tp) := matchTrunc op rewriter.ctx | return rewriter
  let some dMul := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, cst, _mp) := matchMul dMul rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal cst rewriter.ctx | return rewriter
  let outTy := (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw
  let (rewriter, tx) ← rewriter.createOp! (.llvm .trunc) #[outTy] #[x]
    #[] #[] tp (some $ .before op)
  let (rewriter, tc) ← rewriter.createOp! (.llvm .trunc) #[outTy] #[cst]
    #[] #[] tp (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .mul) #[outTy] #[(tx.getResult 0), (tc.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### truncate_of_sext :  trunc (sext x) where trunc result type = x's type → x -/

set_option warn.sorry false in
def truncate_of_sext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, _tp) := matchTrunc op rewriter.ctx | return rewriter
  let some dS := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _sp) := matchSext dS rewriter.ctx | return rewriter
  if (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw != x.getType! rewriter.ctx.raw then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) x sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ### zext_of_zext :  zext (zext x) → zext x -/

set_option warn.sorry false in
def zext_of_zext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, zp) := matchZext op rewriter.ctx | return rewriter
  let some dZ := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _) := matchZext dZ rewriter.ctx | return rewriter
  let outTy := (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw
  let (rewriter, newOp) ← rewriter.createOp (.llvm .zext) #[outTy] #[x]
    #[] #[] zp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### sext_of_sext :  sext (sext x) → sext x -/

set_option warn.sorry false in
def sext_of_sext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (v0, sp) := matchSext op rewriter.ctx | return rewriter
  let some dS := getDefiningOp v0 rewriter.ctx | return rewriter
  let some (x, _) := matchSext dS rewriter.ctx | return rewriter
  let outTy := (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sext) #[outTy] #[x]
    #[] #[] sp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### sub_to_add :  (sub x, C) → (add x, -C)   (C constant) -/

set_option warn.sorry false in
def sub_to_add (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, cval, _sp) := matchSub op rewriter.ctx | return rewriter
  let some c := matchConstantIntVal cval rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let negC := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-c.value) xty))
  let (rewriter, cn) ← rewriter.createOp (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] negC (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, (cn.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### sub_of_mul_const :  (sub a, (mul x, C)) → (add a, (mul x, -C))   (C constant) -/

set_option warn.sorry false in
def sub_of_mul_const (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (a, mulV, _sp) := matchSub op rewriter.ctx | return rewriter
  let some dMul := getDefiningOp mulV rewriter.ctx | return rewriter
  let some (x, cval, mp) := matchMul dMul rewriter.ctx | return rewriter
  let some c := matchConstantIntVal cval rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let negC := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-c.value) xty))
  let (rewriter, cn) ← rewriter.createOp (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] negC (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newMul) ← rewriter.createOp (.llvm .mul) #[x.getType! rewriter.ctx.raw] #[x, (cn.getResult 0)]
    #[] #[] mp (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (newMul.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry
