import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

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

set_option warn.sorry false in
def not_cmp_fold_eq (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some icmpV := matchNot (op.getResult 0) rewriter.ctx | return rewriter
  let some dI := getDefiningOp icmpV rewriter.ctx | return rewriter
  let some (x, y, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .eq := ip.predicate | return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .ne) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def not_cmp_fold_ne (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some icmpV := matchNot (op.getResult 0) rewriter.ctx | return rewriter
  let some dI := getDefiningOp icmpV rewriter.ctx | return rewriter
  let some (x, y, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .ne := ip.predicate | return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .eq) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def not_cmp_fold_ugt (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some icmpV := matchNot (op.getResult 0) rewriter.ctx | return rewriter
  let some dI := getDefiningOp icmpV rewriter.ctx | return rewriter
  let some (x, y, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .ugt := ip.predicate | return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .ule) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def not_cmp_fold_uge (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some icmpV := matchNot (op.getResult 0) rewriter.ctx | return rewriter
  let some dI := getDefiningOp icmpV rewriter.ctx | return rewriter
  let some (x, y, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .uge := ip.predicate | return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .ult) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def not_cmp_fold_sgt (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some icmpV := matchNot (op.getResult 0) rewriter.ctx | return rewriter
  let some dI := getDefiningOp icmpV rewriter.ctx | return rewriter
  let some (x, y, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .sgt := ip.predicate | return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .sle) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
def not_cmp_fold_sge (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some icmpV := matchNot (op.getResult 0) rewriter.ctx | return rewriter
  let some dI := getDefiningOp icmpV rewriter.ctx | return rewriter
  let some (x, y, ip) := matchIcmp dI rewriter.ctx | return rewriter
  let .sge := ip.predicate | return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .slt) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

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
