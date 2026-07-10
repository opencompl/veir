import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.RISCVCombines.MIRCombinesVeir

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

/--
  If `v` is a `ValuePtr` defined by an integer constant whose value is a positive
  power of two, return its base-2 logarithm `k` (so that `v = 2^k`). Otherwise
  `none`. Total: `k` is computed by a bounded recursion counting trailing zeros. -/
def isConstantPowerOfTwo (v : ValuePtr) (ctx : IRContext OpCode) : Option Nat := do
  let attr ← matchConstantIntVal v ctx
  guard (attr.value > 0)
  let n : Nat := attr.value.toNat
  guard (n &&& (n - 1) = 0)
  -- `n` is a power of two; count trailing zeros to recover `k`.
  let rec log2Aux (m : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 => if m ≤ 1 then 0 else 1 + log2Aux (m / 2) fuel
  return log2Aux n n

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

/-- Adapter dropping a binary matcher's properties, for use as a `match?` argument to the
    property-agnostic combinators (`redundantBinopInEqualityLocal`, `hoistAndAndLocal`, …). -/
def matchBinopNoProps {llvmOp : Llvm}
    (m : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × propertiesOf (.llvm llvmOp)))
    (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (x, y, _) ← m op ctx
  some (x, y)

/-! ### hoist_logic_op_with_same_opcode_hands-/

/-- The shared shape of `AndSextSext`/`OrSextSext`/`XorSextSext`: match `(sext X) outer (sext Y)`
    (`outer ∈ {and, or, xor}` via `match?`, both operands defining `sext`s) and emit
    `sext (X outer Y)`, inner op `dst`/`dprops`. `i32 → i64`. Its shared correctness proof is
    `hoistSextLocal_preservesSemantics`. -/
def hoistSextLocal
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr))
    (dst : Llvm) (dprops : propertiesOf (.llvm dst)) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1) := match? op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchSext dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, _yp) := matchSext dY ctx | return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  if xty.bitwidth ≠ 32 then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  if yty.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rty := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if rty.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm dst)
    #[x.getType! ctx.raw] #[x, y] #[] #[] dprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sext)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[inner.getResult 0] #[] #[] () none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndSextSext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (hoistSextLocal (matchBinopNoProps matchAnd) .and ())
    rewriter op opInBounds

def OrSextSext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (hoistSextLocal (matchBinopNoProps matchOr) .or { disjoint := false }) rewriter op opInBounds

def XorSextSext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (hoistSextLocal (matchBinopNoProps matchXor) .xor ())
    rewriter op opInBounds

/-- The shared shape of `AndZextZext`/`OrZextZext`/`XorZextZext`: match `(zext X) outer (zext Y)`
    where `outer ∈ {and, or, xor}` (via `match?`) and both operands are defining `zext`s, and emit
    `zext (X outer Y)`. The inner op is `dst`/`dprops`; the created `zext` keeps `nneg := nneg`
    (`and` reuses the second `zext`'s `nneg`; `or`/`xor` clear it, passing `nneg := false`). The
    narrow-width `{32}` and result-width `{64}` guards are what the correctness proof needs to reach
    the `veir_bv_decide` data lemmas. Its shared correctness proof is
    `hoistZextLocal_preservesSemantics`. -/
def hoistZextLocal
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr))
    (dst : Llvm) (dprops : propertiesOf (.llvm dst)) (useSndNneg : Bool)
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1) := match? op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchZext dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchZext dY ctx | return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  if xty.bitwidth ≠ 32 then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  if yty.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rty := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if rty.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm dst)
    #[x.getType! ctx.raw] #[x, y] #[] #[] dprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .zext)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[inner.getResult 0] #[] #[]
    { nneg := if useSndNneg then yp.nneg else false } none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndZextZext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (hoistZextLocal (matchBinopNoProps matchAnd) .and () true)
    rewriter op opInBounds

def OrZextZext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (hoistZextLocal (matchBinopNoProps matchOr) .or { disjoint := false } false) rewriter op opInBounds

def XorZextZext (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (hoistZextLocal (matchBinopNoProps matchXor) .xor () false)
    rewriter op opInBounds

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
/-- The shared shape of `AndAndAnd`/`OrAndAnd`/`XorAndAnd`: match `(X & Z) outer (Y & Z)` where
    `outer ∈ {and, or, xor}` (matched by `match?`) and both operands are the result of a defining
    `and _ Z` sharing the second operand `Z`, and emit `and (X outer Y) Z` where the inner op is
    `dst` (`and`/`or`-with-`disjoint`-cleared/`xor`). The `.integerType`/bitwidth guard keeps the
    rewrite to `i32`/`i64`. Its shared correctness proof is `hoistAndAndLocal_preservesSemantics`. -/
def hoistAndAndLocal
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr))
    (dst : Llvm) (dprops : propertiesOf (.llvm dst)) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1) := match? op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _) := matchAnd dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, _) := matchAnd dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  if xty.bitwidth ≠ 64 ∧ xty.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm dst)
    #[x.getType! ctx.raw] #[x, y] #[] #[] dprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and)
    #[x.getType! ctx.raw] #[inner.getResult 0, z0] #[] #[] () none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (hoistAndAndLocal (matchBinopNoProps matchAnd) .and ())
    rewriter op opInBounds

-- (X & Z) | (Y & Z) → (X | Y) & Z
-- The created `or` drops `disjoint`: `X` and `Y` may overlap only in bits that `Z` masks off.
def OrAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (hoistAndAndLocal (matchBinopNoProps matchOr) .or { disjoint := false }) rewriter op opInBounds

-- (X & Z) ^ (Y & Z) → (X ^ Y) & Z
def XorAndAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (hoistAndAndLocal (matchBinopNoProps matchXor) .xor ())
    rewriter op opInBounds

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

/-- The shared shape of the two `x - (add ..) → 0 - y` combines: match `sub x s1` where `s1` is a
    defining `add` one of whose operands is `x` (the matched `sub`'s left operand), and emit
    `0 - y` for the *other* add operand `y`. `keepFirst` selects which add operand is `y`: for
    `x - (y + x)` (`keepFirst := true`) the second add operand must be `x` and `y` is the first;
    for `x - (x + y)` (`keepFirst := false`) the first must be `x` and `y` is the second.

    The `.integerType`/bitwidth guard is what the correctness proof needs to reach the
    `veir_bv_decide` data lemmas, so the rewrite is restricted to `i32`/`i64`. The created `sub`
    clears `nsw`/`nuw`, since `0 - y` has a different overflow condition than the matched `sub`
    (see `sub_add_reg_x_sub_y_add_x`/`_x_add_y` in `LLVMProofs.lean`). Its shared correctness proof
    is `subAddRegNegLocal_preservesSemantics`. -/
def subAddRegNegLocal (keepFirst : Bool) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (s0, s1, _sp) := matchSub op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some dAdd := getDefiningOp s1 ctx | return (ctx, none)
  let some (a0, a1, _ap) := matchAdd dAdd ctx | return (ctx, none)
  let (y, other) := if keepFirst then (a0, a1) else (a1, a0)
  if other != s0 then return (ctx, none)
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[] #[] #[]
    (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 t))) none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[c0.getResult 0, y] #[] #[]
    { nsw := false, nuw := false } none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

-- x - (y + x) → 0 - y
def sub_add_reg_x_sub_y_add_x (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (subAddRegNegLocal true) rewriter op opInBounds

-- x - (x + y) → 0 - y
def sub_add_reg_x_sub_x_add_y (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (subAddRegNegLocal false) rewriter op opInBounds

/-! ### xor_of_and_with_same_reg :  (xor (and x, y), y) → (and (not x), y) -/

/-- `(x & y) ^ y → (~x) & y`, as a `LocalRewritePattern`. `op` is the `xor`, whose first operand
    is the result of a defining `and x y` sharing the second operand `y`. It creates a
    `constant -1`, an `xor x (-1)` (i.e. `~x`), and an `and (~x) y`. The `.integerType`/bitwidth
    guard keeps the rewrite to `i32`/`i64`. See `xor_of_and_with_same_reg_local_preservesSemantics`. -/
def xor_of_and_with_same_reg_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (andVal, yval, _xp) := matchXor op ctx | return (ctx, none)
  let some dA := getDefiningOp andVal ctx | return (ctx, none)
  let some (x, y2, _) := matchAnd dA ctx | return (ctx, none)
  if y2 != yval then return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  if xty.bitwidth ≠ 64 ∧ xty.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, c1) ← WfRewriter.createOp! ctx (.llvm .mlir__constant)
    #[x.getType! ctx.raw] #[] #[] #[]
    (LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) xty))) none
  let (ctx, notx) ← WfRewriter.createOp! ctx (.llvm .xor)
    #[x.getType! ctx.raw] #[x, c1.getResult 0] #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and)
    #[x.getType! ctx.raw] #[notx.getResult 0, yval] #[] #[] () none
  some (ctx, some (#[c1, notx, newOp], #[newOp.getResult 0]))

def xor_of_and_with_same_reg (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite xor_of_and_with_same_reg_local rewriter op opInBounds

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
/-- `zext (select c t f) → select c (zext t) (zext f)`, as a `LocalRewritePattern`. `op` is the
    `zext`, whose operand is a defining `select c t f`. It creates two `zext`s (of `t` and `f`,
    both carrying the matched `zext`'s properties `zp`) and a `select` over them. The narrow-`{32}`
    (operand) / result-`{64}` width guards keep the rewrite to `i32 → i64`. See
    `select_of_zext_local_preservesSemantics`. -/
def select_of_zext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, zp) := matchZext op ctx | return (ctx, none)
  let some dS := getDefiningOp v0 ctx | return (ctx, none)
  let some (cond, tv, fv) := matchSelect dS ctx | return (ctx, none)
  let .integerType tvty := (tv.getType! ctx.raw).val | return (ctx, none)
  if tvty.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rty := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if rty.bitwidth ≠ 64 then return (ctx, none)
  let outTy := (op.getResult 0 : ValuePtr).getType! ctx.raw
  let (ctx, zt) ← WfRewriter.createOp! ctx (.llvm .zext) #[outTy] #[tv] #[] #[] zp none
  let (ctx, zf) ← WfRewriter.createOp! ctx (.llvm .zext) #[outTy] #[fv] #[] #[] zp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .select)
    #[outTy] #[cond, zt.getResult 0, zf.getResult 0] #[] #[] () none
  some (ctx, some (#[zt, zf, newOp], #[newOp.getResult 0]))

def select_of_zext_rw (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_of_zext_local rewriter op opInBounds

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

/-- The shared shape of the six `redundant_binop_in_equality` combines: match
    `icmp (binop X Y) X pred` with `pred ∈ {eq, ne}`, where the left comparison operand is the
    result of a defining `binop` (`add`/`sub`/`xor`, matched by `match?`) whose first operand is
    the right comparison operand `X`, and emit `icmp Y 0 pred`. The `binop`'s flags are dropped.

    The `.integerType`/bitwidth guard on the comparison-operand type is what the correctness proof
    needs to reach the `veir_bv_decide` data lemmas, so the rewrite is restricted to `i32`/`i64`.
    Its shared correctness proof is `redundantBinopInEqualityLocal_preservesSemantics`. -/
def redundantBinopInEqualityLocal
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr))
    (pred : Data.LLVM.IntPred) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhsV, xval, ip) := matchIcmp op ctx | return (ctx, none)
  if ip.predicate != pred then return (ctx, none)
  let some dBinop := getDefiningOp lhsV ctx | return (ctx, none)
  let some (x, y) := match? dBinop ctx | return (ctx, none)
  if x != xval then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  if yty.bitwidth ≠ 64 ∧ yty.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant)
    #[y.getType! ctx.raw] #[] #[] #[]
    (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 yty))) none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[y, c0.getResult 0] #[] #[]
    (IcmpProperties.mk pred) none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def redundant_binop_in_equality_XPlusYEqX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (redundantBinopInEqualityLocal (matchBinopNoProps matchAdd) .eq) rewriter op opInBounds

def redundant_binop_in_equality_XPlusYNeX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (redundantBinopInEqualityLocal (matchBinopNoProps matchAdd) .ne) rewriter op opInBounds

def redundant_binop_in_equality_XMinusYEqX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (redundantBinopInEqualityLocal (matchBinopNoProps matchSub) .eq) rewriter op opInBounds

def redundant_binop_in_equality_XMinusYNeX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (redundantBinopInEqualityLocal (matchBinopNoProps matchSub) .ne) rewriter op opInBounds

def redundant_binop_in_equality_XXorYEqX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (redundantBinopInEqualityLocal (matchBinopNoProps matchXor) .eq) rewriter op opInBounds

def redundant_binop_in_equality_XXorYNeX (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (redundantBinopInEqualityLocal (matchBinopNoProps matchXor) .ne) rewriter op opInBounds

/-! ### match_selects -/

/-- The shared shape of the two `select {c, 1, 0}`/`{c, -1, 0}` combines: match
    `select c C1 0` where the true arm `C1` is the constant `tvVal` (`1` for `zext`, `-1`
    for `sext`), and emit the extension `dst` of the `i1` condition `c`.

    The `.integerType`/bitwidth guard on the result type is what the correctness proof needs to
    reach the `veir_bv_decide` data lemmas, so the rewrite is restricted to `i32`/`i64` results.
    Its shared correctness proof is `matchSelectExtLocal_preservesSemantics`. -/
def matchSelectExtLocal (tvVal : Int) (dst : Llvm) (dprops : propertiesOf (.llvm dst))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some ct := matchConstantIntVal tv ctx | return (ctx, none)
  if ct.value ≠ tvVal then return (ctx, none)
  let some cf := matchConstantIntVal fv ctx | return (ctx, none)
  if cf.value ≠ 0 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm dst)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[cond] #[] #[] dprops none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

-- select c, 1, 0 → zext c
def select_1_0 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (matchSelectExtLocal 1 .zext { nneg := false })
    rewriter op opInBounds

-- select c, -1, 0 → sext c
def select_neg1_0 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (matchSelectExtLocal (-1) .sext ()) rewriter op opInBounds

/-- The shared shape of the two `select {c, 0, 1}`/`{c, 0, -1}` combines: match `select c 0 C1`
    where the false arm `C1` is `fvVal` (`1` for `zext`, `-1` for `sext`), and emit the extension
    `dst` of `~c` (`xor c (-1)`, i.e. `not c`). It creates a `constant -1` (`i1`), an `xor c (-1)`
    (`i1`), and the extension to the result width.

    The `.integerType`/bitwidth guard on the *result* type keeps the rewrite to `i32`/`i64`. Its
    shared correctness proof is `matchSelectNotExtLocal_preservesSemantics`. -/
def matchSelectNotExtLocal (fvVal : Int) (dst : Llvm) (dprops : propertiesOf (.llvm dst))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let .integerType rt := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if rt.bitwidth ≠ 64 ∧ rt.bitwidth ≠ 32 then return (ctx, none)
  let some ct := matchConstantIntVal tv ctx | return (ctx, none)
  if ct.value ≠ 0 then return (ctx, none)
  let some cf := matchConstantIntVal fv ctx | return (ctx, none)
  if cf.value ≠ fvVal then return (ctx, none)
  let .integerType cty := (cond.getType! ctx.raw).val | return (ctx, none)
  let (ctx, c1) ← WfRewriter.createOp! ctx (.llvm .mlir__constant)
    #[cond.getType! ctx.raw] #[] #[] #[]
    (LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) cty))) none
  let (ctx, ncond) ← WfRewriter.createOp! ctx (.llvm .xor)
    #[cond.getType! ctx.raw] #[cond, c1.getResult 0] #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm dst)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[ncond.getResult 0] #[] #[] dprops none
  some (ctx, some (#[c1, ncond, newOp], #[newOp.getResult 0]))

-- select c, 0, 1 → zext (not c)
def select_0_1 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (matchSelectNotExtLocal 1 .zext { nneg := false })
    rewriter op opInBounds

-- select c, 0, -1 → sext (not c)
def select_0_neg1 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (matchSelectNotExtLocal (-1) .sext ()) rewriter op opInBounds

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

/-- The shared shape of the two `double_icmp_zero` combines: match `(icmp X 0 pred) outer
    (icmp Y 0 pred)` where `outer ∈ {and, or}` (matched by `match?`) and both operands are the
    result of a defining `icmp _ 0 pred` with `pred ∈ {eq, ne}`, and emit `icmp (X | Y) 0 pred`.
    The created `or` clears `disjoint` (the `or`-combine could reuse the matched flag, but the
    data lemma is generic over it, so `false` is sound and uniform).

    The `.integerType`/bitwidth guard on the comparison-operand type keeps the rewrite to
    `i32`/`i64`. Its shared correctness proof is `doubleIcmpZeroLocal_preservesSemantics`. -/
def doubleIcmpZeroLocal
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr))
    (pred : Data.LLVM.IntPred) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1) := match? op ctx | return (ctx, none)
  let some dL := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, cx, ip0) := matchIcmp dL ctx | return (ctx, none)
  if ip0.predicate != pred then return (ctx, none)
  let some cxv := matchConstantIntVal cx ctx | return (ctx, none)
  if cxv.value ≠ 0 then return (ctx, none)
  let some dR := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, cy, ip1) := matchIcmp dR ctx | return (ctx, none)
  if ip1.predicate != pred then return (ctx, none)
  let some cyv := matchConstantIntVal cy ctx | return (ctx, none)
  if cyv.value ≠ 0 then return (ctx, none)
  if y.getType! ctx.raw != x.getType! ctx.raw then return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  if xty.bitwidth ≠ 64 ∧ xty.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, orOp) ← WfRewriter.createOp! ctx (.llvm .or)
    #[x.getType! ctx.raw] #[x, y] #[] #[] { disjoint := false } none
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant)
    #[x.getType! ctx.raw] #[] #[] #[]
    (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 xty))) none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp)
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[orOp.getResult 0, c0.getResult 0] #[] #[]
    (IcmpProperties.mk pred) none
  some (ctx, some (#[orOp, c0, newOp], #[newOp.getResult 0]))

def double_icmp_zero_and_combine (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (doubleIcmpZeroLocal (matchBinopNoProps matchAnd) .eq) rewriter op opInBounds

def double_icmp_zero_or_combine (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite
    (doubleIcmpZeroLocal (matchBinopNoProps matchOr) .ne) rewriter op opInBounds

/-! ### NotAPlusNegOne :  (not (add X, -1)) → (sub 0, X) -/

/-- `not (add X (-1)) → 0 - X`, as a `LocalRewritePattern`. `op` is the `xor _, -1` (matched with
    `matchNot` on its own result), whose non-constant operand is the result of a defining
    `add X (-1)`. It creates a `constant 0` and a `sub 0 X` carrying the `add`'s flags. The
    `.integerType`/bitwidth guard keeps the rewrite to `i32`/`i64`. See
    `NotAPlusNegOne_local_preservesSemantics`. -/
def NotAPlusNegOne_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some addVal := matchNot (op.getResult 0) ctx | return (ctx, none)
  let some dAdd := getDefiningOp addVal ctx | return (ctx, none)
  let some (x, cm1, ap) := matchAdd dAdd ctx | return (ctx, none)
  let some cst := matchConstantIntVal cm1 ctx | return (ctx, none)
  if cst.value ≠ -1 then return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  if xty.bitwidth ≠ 64 ∧ xty.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant)
    #[x.getType! ctx.raw] #[] #[] #[]
    (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 xty))) none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub)
    #[x.getType! ctx.raw] #[c0.getResult 0, x] #[] #[] ap none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def NotAPlusNegOne_rw (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite NotAPlusNegOne_local rewriter op opInBounds

/-! ### sub_one_from_sub :  (A - B) - 1 → add (xor B, -1), A -/

-- The created `add` drops the matched `sub`'s `nsw`/`nuw`: `(~B) + A` has a different
-- overflow condition than `(A - B) - 1` (e.g. `A = 5`, `B = 3` unsigned-overflows only
-- the former). See `sub_one_from_sub_rw` in `LLVMProofs.lean`.
/-- `(A - B) - 1 → (~B) + A`, as a `LocalRewritePattern`. `op` is the outer `sub`, whose second
    operand is the constant `1` and whose first operand is the result of a defining `sub A B`. It
    creates a `constant -1`, an `xor B (-1)` (`~B`), and an `add (~B) A` with cleared flags. The
    `.integerType`/bitwidth guard keeps the rewrite to `i32`/`i64`. See
    `sub_one_from_sub_local_preservesSemantics`. -/
def sub_one_from_sub_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (subVal, c1v, _sp) := matchSub op ctx | return (ctx, none)
  let some cst1 := matchConstantIntVal c1v ctx | return (ctx, none)
  if cst1.value ≠ 1 then return (ctx, none)
  let some dSub := getDefiningOp subVal ctx | return (ctx, none)
  let some (x, y, _sp2) := matchSub dSub ctx | return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  if yty.bitwidth ≠ 64 ∧ yty.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, cm1) ← WfRewriter.createOp! ctx (.llvm .mlir__constant)
    #[y.getType! ctx.raw] #[] #[] #[]
    (LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) yty))) none
  let (ctx, xorOp) ← WfRewriter.createOp! ctx (.llvm .xor)
    #[y.getType! ctx.raw] #[y, cm1.getResult 0] #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add)
    #[y.getType! ctx.raw] #[xorOp.getResult 0, x] #[] #[] { nsw := false, nuw := false } none
  some (ctx, some (#[cm1, xorOp, newOp], #[newOp.getResult 0]))

def sub_one_from_sub_rw (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_one_from_sub_local rewriter op opInBounds

/-! ### APlusC1MinusC2 :  (A + C1) - C2 → A + (C1 - C2)   (C1, C2 constants) -/

set_option warn.sorry false in
def APlusC1MinusC2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (addVal, c2v, _sp) := matchSub op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp addVal rewriter.ctx | return rewriter
  let some (a, c1v, ap) := matchAdd dAdd rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value - c2.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (cf.getResult 0)]
    #[] #[] ap (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### C2MinusAPlusC1 :  C2 - (A + C1) → (C2 - C1) - A   (C1, C2 constants) -/

set_option warn.sorry false in
def C2MinusAPlusC1 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (c2v, addVal, sp) := matchSub op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp addVal rewriter.ctx | return rewriter
  let some (a, c1v, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c2.value - c1.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(cf.getResult 0), a]
    #[] #[] sp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### AMinusC1MinusC2 :  (A - C1) - C2 → A - (C1 + C2)   (C1, C2 constants) -/

set_option warn.sorry false in
def AMinusC1MinusC2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (subVal, c2v, sp) := matchSub op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dSub := getDefiningOp subVal rewriter.ctx | return rewriter
  let some (a, c1v, _sp2) := matchSub dSub rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value + c2.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (cf.getResult 0)]
    #[] #[] sp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### C1MinusAMinusC2 :  (C1 - A) - C2 → (C1 - C2) - A   (C1, C2 constants) -/

set_option warn.sorry false in
def C1MinusAMinusC2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (subVal, c2v, sp) := matchSub op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dSub := getDefiningOp subVal rewriter.ctx | return rewriter
  let some (c1v, a, _sp2) := matchSub dSub rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value - c2.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(cf.getResult 0), a]
    #[] #[] sp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### AMinusC1PlusC2 :  (A - C1) + C2 → A + (C2 - C1)   (C1, C2 constants) -/

set_option warn.sorry false in
def AMinusC1PlusC2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (subVal, c2v, ap) := matchAdd op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dSub := getDefiningOp subVal rewriter.ctx | return rewriter
  let some (a, c1v, _sp) := matchSub dSub rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c2.value - c1.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (cf.getResult 0)]
    #[] #[] ap (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### or_and_xor_to_xor_or :  (X & Y) | ~Y  →  X | ~Y -/
set_option warn.sorry false in
def or_and_xor_to_xor_or (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (andV, notV, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dAnd := getDefiningOp andV rewriter.ctx | return rewriter
  let some (x, y, _aprops) := matchAnd dAnd rewriter.ctx | return rewriter
  let some dNot := getDefiningOp notV rewriter.ctx | return rewriter
  let some (y1, m1v, _xprops) := matchXor dNot rewriter.ctx | return rewriter
  if y1 != y then return rewriter
  let some cst := matchConstantIntVal m1v rewriter.ctx | return rewriter
  if cst.value ≠ -1 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .or) #[andV.getType! rewriter.ctx.raw] #[x, notV]
    #[] #[] oprops (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### and_xor_or_to_xor_and :  (X | Y) & ~Y  →  X & ~Y -/
set_option warn.sorry false in
def and_xor_or_to_xor_and (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (orV, notV, _aprops) := matchAnd op rewriter.ctx | return rewriter
  let some dOr := getDefiningOp orV rewriter.ctx | return rewriter
  let some (x, y, _oprops) := matchOr dOr rewriter.ctx | return rewriter
  let some dNot := getDefiningOp notV rewriter.ctx | return rewriter
  let some (y1, m1v, _xprops) := matchXor dNot rewriter.ctx | return rewriter
  if y1 != y then return rewriter
  let some cst := matchConstantIntVal m1v rewriter.ctx | return rewriter
  if cst.value ≠ -1 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .and) #[orV.getType! rewriter.ctx.raw] #[x, notV]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### combine_or_of_and :  or (and x, y), x  →  x -/

-- or (and x, y), x  →  x   (the `and` is the left OR operand)
set_option warn.sorry false in
def combine_or_of_and_l (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (andV, x, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dAnd := getDefiningOp andV rewriter.ctx | return rewriter
  let some (a0, a1, _aprops) := matchAnd dAnd rewriter.ctx | return rewriter
  if a0 != x && a1 != x then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) x sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

-- or x, (and x, y)  →  x   (the `and` is the right OR operand)
set_option warn.sorry false in
def combine_or_of_and_r (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, andV, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dAnd := getDefiningOp andV rewriter.ctx | return rewriter
  let some (a0, a1, _aprops) := matchAnd dAnd rewriter.ctx | return rewriter
  if a0 != x && a1 != x then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) x sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ### AMinusBMinusC :  A - (B - C)  →  A + (C - B) -/
set_option warn.sorry false in
def AMinusBMinusC (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (A, sub1, sprops) := matchSub op rewriter.ctx | return rewriter
  let some dSub := getDefiningOp sub1 rewriter.ctx | return rewriter
  let some (B, C, _sprops1) := matchSub dSub rewriter.ctx | return rewriter
  let (rewriter, cMinusB) ← rewriter.createOp! (.llvm .sub) #[sub1.getType! rewriter.ctx.raw] #[C, B]
    #[] #[] sprops (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .add) #[A.getType! rewriter.ctx.raw] #[A, (cMinusB.getResult 0)]
    #[] #[] sprops (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### binop_left_to_zero :  (0 op x)  →  0   for op ∈ {shl, lshr, ashr, mul} -/

set_option warn.sorry false in
def shl_left_to_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zero, _rhs, _props) := matchShl op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal zero rewriter.ctx | return rewriter
  if cst.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) zero sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def lshr_left_to_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zero, _rhs, _props) := matchLshr op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal zero rewriter.ctx | return rewriter
  if cst.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) zero sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def ashr_left_to_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zero, _rhs, _props) := matchAshr op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal zero rewriter.ctx | return rewriter
  if cst.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) zero sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def mul_left_to_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zero, _rhs, _props) := matchMul op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal zero rewriter.ctx | return rewriter
  if cst.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) zero sorry sorry sorry
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

/-! ### lshr_of_trunc_of_lshr :  (lshr (trunc (lshr x, C1)), C2) → trunc (lshr x, (C1 + C2))

  C1, C2 constants. The two logical right shifts compose at x's full width, then a
  single trunc narrows to the result type. -/

set_option warn.sorry false in
def lshr_of_trunc_of_lshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (truncV, c2v, _) := matchLshr op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dTrunc := getDefiningOp truncV rewriter.ctx | return rewriter
  let some (innerLshrV, _) := matchTrunc dTrunc rewriter.ctx | return rewriter
  let some dInner := getDefiningOp innerLshrV rewriter.ctx | return rewriter
  let some (x, c1v, ip) := matchLshr dInner rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value + c2.value) xty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newLshr) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[x, (cf.getResult 0)]
    #[] #[] ip (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .trunc) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(newLshr.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### funnel_shift_{right,left}_zero :  fshr x, y, 0 → y ,  fshl x, y, 0 → x -/

set_option warn.sorry false in
def funnel_shift_right_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (_x, y, amt) := matchFshr op rewriter.ctx | return rewriter
  let some c := matchConstantIntVal amt rewriter.ctx | return rewriter
  if c.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) y sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def funnel_shift_left_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, _y, amt) := matchFshl op rewriter.ctx | return rewriter
  let some c := matchConstantIntVal amt rewriter.ctx | return rewriter
  if c.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) x sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ### canonicalize_icmp :  (icmp pred C, x) → (icmp swappedPred x, C)

  Moves a constant left operand of an icmp to the right, flipping the predicate to
  its swapped form. Mirrors LLVM's `matchCanonicalizeICmp`: fires only when the LHS
  is a constant and the RHS is not (so it does not oscillate). -/

set_option warn.sorry false in
def canonicalize_icmp (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, ip) := matchIcmp op rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal lhs rewriter.ctx | return rewriter
  if (matchConstantIntVal rhs rewriter.ctx).isSome then return rewriter
  let swapped : Data.LLVM.IntPred := match ip.predicate with
    | .slt => .sgt | .sgt => .slt | .sle => .sge | .sge => .sle
    | .ult => .ugt | .ugt => .ult | .ule => .uge | .uge => .ule
    | p => p
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[rhs, lhs]
    #[] #[] (IcmpProperties.mk swapped) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### bitreverse_shl / bitreverse_lshr

  `bitreverse(shl(bitreverse x), y) → lshr x, y` and the mirror
  `bitreverse(lshr(bitreverse x), y) → shl x, y`. Reversing, shifting one way,
  and reversing again is equivalent to a single shift the other way. -/

set_option warn.sorry false in
def bitreverse_shl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some rev := matchBitreverse op rewriter.ctx | return rewriter
  let some dShl := getDefiningOp rev rewriter.ctx | return rewriter
  let some (inner, y, _) := matchShl dShl rewriter.ctx | return rewriter
  let some dInner := getDefiningOp inner rewriter.ctx | return rewriter
  let some x := matchBitreverse dInner rewriter.ctx | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .lshr) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (ExactProperties.mk false) (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def bitreverse_lshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some rev := matchBitreverse op rewriter.ctx | return rewriter
  let some dLshr := getDefiningOp rev rewriter.ctx | return rewriter
  let some (inner, y, _) := matchLshr dLshr rewriter.ctx | return rewriter
  let some dInner := getDefiningOp inner rewriter.ctx | return rewriter
  let some x := matchBitreverse dInner rewriter.ctx | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .shl) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (NswNuwProperties.mk false false) (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### udiv_by_pow2 / mul_to_shl / urem_pow2_to_mask

  Strength reductions against a power-of-two constant:
    `udiv x, 2^k → lshr x, k`,  `mul x, 2^k → shl x, k`,
    `urem x, 2^k → and x, (2^k − 1)`. -/

set_option warn.sorry false in
def udiv_by_pow2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, yv, _) := matchUdiv op rewriter.ctx | return rewriter
  let some k := isConstantPowerOfTwo yv rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let kConst := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (k : Int) xty))
  let (rewriter, ck) ← rewriter.createOp! (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] kConst (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .lshr) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, (ck.getResult 0)]
    #[] #[] (ExactProperties.mk false) (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def mul_to_shl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, yv, mp) := matchMul op rewriter.ctx | return rewriter
  let some k := isConstantPowerOfTwo yv rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let kConst := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (k : Int) xty))
  let (rewriter, ck) ← rewriter.createOp! (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] kConst (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .shl) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, (ck.getResult 0)]
    #[] #[] mp (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def urem_pow2_to_mask (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, yv, _) := matchUrem op rewriter.ctx | return rewriter
  let some k := isConstantPowerOfTwo yv rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let mask : Int := (2 ^ k : Int) - 1
  let maskConst := LLVMConstantProperties.mk (.integer (IntegerAttr.mk mask xty))
  let (rewriter, cm) ← rewriter.createOp! (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] maskConst (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .and) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, (cm.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### funnel_shift_overshift :  fshl/fshr x, y, C → fshl/fshr x, y, (C % bw)   (C ≥ bw)

  A funnel shift amount is taken modulo the bit-width, so an over-large constant
  amount is reduced to its residue. -/

set_option warn.sorry false in
def funnel_shift_overshift_l (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, y, amt) := matchFshl op rewriter.ctx | return rewriter
  let some c := matchConstantIntVal amt rewriter.ctx | return rewriter
  let .integerType aty := (amt.getType! rewriter.ctx.raw).val | return rewriter
  let bw : Int := (aty.bitwidth : Int)
  if c.value < bw then return rewriter
  let newAmt := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c.value % bw) aty))
  let (rewriter, cn) ← rewriter.createOp! (.llvm .mlir__constant) #[amt.getType! rewriter.ctx.raw] #[]
    #[] #[] newAmt (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .intr__fshl) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y, (cn.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def funnel_shift_overshift_r (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, y, amt) := matchFshr op rewriter.ctx | return rewriter
  let some c := matchConstantIntVal amt rewriter.ctx | return rewriter
  let .integerType aty := (amt.getType! rewriter.ctx.raw).val | return rewriter
  let bw : Int := (aty.bitwidth : Int)
  if c.value < bw then return rewriter
  let newAmt := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c.value % bw) aty))
  let (rewriter, cn) ← rewriter.createOp! (.llvm .mlir__constant) #[amt.getType! rewriter.ctx.raw] #[]
    #[] #[] newAmt (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .intr__fshr) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y, (cn.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### funnel_shift_or_shift_to_funnel_shift_{left,right}

  `(fshl x, z, y) | (shl x, y) → fshl x, z, y` and the mirror
  `(fshr z, x, y) | (lshr x, y) → fshr z, x, y`. The plain shift is subsumed by
  the funnel shift that already produces the wanted bits, so the OR collapses to
  the existing funnel-shift value. G_OR is commutative: both operand orders are
  handled. -/

set_option warn.sorry false in
def funnel_shift_or_shift_to_funnel_shift_left (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (o0, o1, _) := matchOr op rewriter.ctx | return rewriter
  -- Try (fshl = o0, shl = o1) then (fshl = o1, shl = o0).
  let tryOrder (fshlV shlV : ValuePtr) : Option ValuePtr := do
    let some dFshl := getDefiningOp fshlV rewriter.ctx | none
    let some (fx, _fz, fy) := matchFshl dFshl rewriter.ctx | none
    let some dShl := getDefiningOp shlV rewriter.ctx | none
    let some (sx, sy, _) := matchShl dShl rewriter.ctx | none
    guard (fx = sx ∧ fy = sy)
    some fshlV
  let some keep := (tryOrder o0 o1).orElse (fun _ => tryOrder o1 o0) | return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) keep sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def funnel_shift_or_shift_to_funnel_shift_right (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (o0, o1, _) := matchOr op rewriter.ctx | return rewriter
  -- Try (fshr = o0, lshr = o1) then (fshr = o1, lshr = o0).
  let tryOrder (fshrV lshrV : ValuePtr) : Option ValuePtr := do
    let some dFshr := getDefiningOp fshrV rewriter.ctx | none
    let some (_fz, fx, fy) := matchFshr dFshr rewriter.ctx | none
    let some dLshr := getDefiningOp lshrV rewriter.ctx | none
    let some (sx, sy, _) := matchLshr dLshr rewriter.ctx | none
    guard (fx = sx ∧ fy = sy)
    some fshrV
  let some keep := (tryOrder o0 o1).orElse (fun _ => tryOrder o1 o0) | return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) keep sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ### constant_fold_binop :  binop(C1, C2) → C

  Both operands constant: evaluate the binop at compile time and materialize the
  single result constant. Division/remainder by zero is left un-folded. -/

set_option warn.sorry false in
def constant_fold_binop (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let opType := op.getOpType! rewriter.ctx.raw
  let operands := op.getOperands! rewriter.ctx.raw
  if operands.size ≠ 2 then return rewriter
  let some c1 := matchConstantIntVal operands[0]! rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal operands[1]! rewriter.ctx | return rewriter
  let a := c1.value
  let b := c2.value
  -- Only opcodes whose result is well-defined over unbounded `Int` (no fixed-width
  -- wrapping / signedness ambiguity) are folded. The bitwise ops (`and/or/xor`),
  -- the shifts, and the div/rem family need width-dependent semantics and are
  -- deliberately omitted here.
  let folded : Option Int := match opType with
    | .llvm .add => some (a + b)
    | .llvm .sub => some (a - b)
    | .llvm .mul => some (a * b)
    | .llvm .intr__smin => some (min a b)
    | .llvm .intr__smax => some (max a b)
    | _ => none
  let some result := folded | return rewriter
  let .integerType rty := ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val | return rewriter
  let foldedProps := LLVMConstantProperties.mk (.integer (IntegerAttr.mk result rty))
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .mlir__constant) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[]
    #[] #[] foldedProps (some $ .before op)
  return rewriter.replaceOp! op newOp

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
     , APlusC1MinusC2
     , C2MinusAPlusC1
     , AMinusC1MinusC2
     , C1MinusAMinusC2
     , AMinusC1PlusC2
     , or_and_xor_to_xor_or
     , and_xor_or_to_xor_and
     , combine_or_of_and_l
     , combine_or_of_and_r
     , AMinusBMinusC
     , shl_left_to_zero
     , lshr_left_to_zero
     , ashr_left_to_zero
     , mul_left_to_zero
     , SubSmaxSub
     , SubUmaxSub
     , narrow_binop_add
     , narrow_binop_sub
     , narrow_binop_mul
     , truncate_of_sext
     , zext_of_zext
     , sext_of_sext
     , sub_to_add
     , sub_of_mul_const
     , select_not
     , commute_const_add
     , commute_const_mul
     , commute_const_and
     , commute_const_or
     , commute_const_xor
     , SubSminSub
     , SubUminSub
     , lshr_of_trunc_of_lshr
     , funnel_shift_right_zero
     , funnel_shift_left_zero
     , canonicalize_icmp
     , bitreverse_shl
     , bitreverse_lshr
     , udiv_by_pow2
     , mul_to_shl
     , urem_pow2_to_mask
     , funnel_shift_overshift_l
     , funnel_shift_overshift_r
     , funnel_shift_or_shift_to_funnel_shift_left
     , funnel_shift_or_shift_to_funnel_shift_right
     , constant_fold_binop
     ,
     ] ++ mir_pattern_combines
  let pattern := RewritePattern.GreedyRewritePattern patterns
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
