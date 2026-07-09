import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

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

-- ugt → umax
set_option warn.sorry false in
def select_to_iminmax_ugt (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some dI := getDefiningOp cond rewriter.ctx | return rewriter
  let some (il, ir, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .ugt := ip.predicate | return rewriter
  if il != tv then return rewriter
  if ir != fv then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .intr__umax) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[tv, fv]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- uge → umax
set_option warn.sorry false in
def select_to_iminmax_uge (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some dI := getDefiningOp cond rewriter.ctx | return rewriter
  let some (il, ir, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .uge := ip.predicate | return rewriter
  if il != tv then return rewriter
  if ir != fv then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .intr__umax) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[tv, fv]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- sgt → smax
set_option warn.sorry false in
def select_to_iminmax_sgt (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some dI := getDefiningOp cond rewriter.ctx | return rewriter
  let some (il, ir, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .sgt := ip.predicate | return rewriter
  if il != tv then return rewriter
  if ir != fv then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .intr__smax) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[tv, fv]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- sge → smax.
set_option warn.sorry false in
def select_to_iminmax_sge (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some dI := getDefiningOp cond rewriter.ctx | return rewriter
  let some (il, ir, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .sge := ip.predicate | return rewriter
  if il != tv then return rewriter
  if ir != fv then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .intr__smax) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[tv, fv]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- ult → umin
set_option warn.sorry false in
def select_to_iminmax_ult (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some dI := getDefiningOp cond rewriter.ctx | return rewriter
  let some (il, ir, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .ult := ip.predicate | return rewriter
  if il != tv then return rewriter
  if ir != fv then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .intr__umin) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[tv, fv]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- ule → umin
set_option warn.sorry false in
def select_to_iminmax_ule (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some dI := getDefiningOp cond rewriter.ctx | return rewriter
  let some (il, ir, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .ule := ip.predicate | return rewriter
  if il != tv then return rewriter
  if ir != fv then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .intr__umin) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[tv, fv]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- slt → smin
set_option warn.sorry false in
def select_to_iminmax_slt (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some dI := getDefiningOp cond rewriter.ctx | return rewriter
  let some (il, ir, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .slt := ip.predicate | return rewriter
  if il != tv then return rewriter
  if ir != fv then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .intr__smin) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[tv, fv]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

-- sle → smin
set_option warn.sorry false in
def select_to_iminmax_sle (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tv, fv) := matchSelect op rewriter.ctx | return rewriter
  let some dI := getDefiningOp cond rewriter.ctx | return rewriter
  let some (il, ir, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .sle := ip.predicate | return rewriter
  if il != tv then return rewriter
  if ir != fv then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .intr__smin) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[tv, fv]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry
