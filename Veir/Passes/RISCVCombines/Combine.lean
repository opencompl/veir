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

/-- riscv.add x 0 -> x -/
def right_identity_zero_add_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, _) := matchOp op ctx (.riscv .add) 2 | return (ctx, none)
  let lhs := operands[0]!
  let some liOp := getDefiningOp operands[1]! ctx | return (ctx, none)
  let some (_, cst) := matchOp liOp ctx (.riscv .li) 0 | return (ctx, none)
  if cst.value.value ≠ 0 then return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def right_identity_zero_add (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite right_identity_zero_add_local rewriter op opInBounds

/-! ### select_same_val :  (c ? x : x) → x -/

def select_same_val_self_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (_c, tval, fval) := matchSelect op ctx | return (ctx, none)
  if tval != fval then return (ctx, none)
  some (ctx, some (#[], #[tval]))

def select_same_val_self (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_same_val_self_local rewriter op opInBounds

/-! ### select_constant_cmp :  (1 ? x : y) → x ,  (0 ? x : y) → y -/

def select_constant_cmp_true_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tval, _fval) := matchSelect op ctx | return (ctx, none)
  let some cst := matchConstantIntVal cond ctx | return (ctx, none)
  if cst.value ≠ 1 then return (ctx, none)
  some (ctx, some (#[], #[tval]))

def select_constant_cmp_true (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_constant_cmp_true_local rewriter op opInBounds

def select_constant_cmp_false_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, _tval, fval) := matchSelect op ctx | return (ctx, none)
  let some cst := matchConstantIntVal cond ctx | return (ctx, none)
  if cst.value ≠ 0 then return (ctx, none)
  some (ctx, some (#[], #[fval]))

def select_constant_cmp_false (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_constant_cmp_false_local rewriter op opInBounds

/-! ### hoist_logic_op_with_same_opcode_hands-/

-- (sext X) & (sext Y) → sext (X & Y)
def AndSextSext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, _) := matchAnd op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchSext dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchSext dY ctx | return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[x, y]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndSextSext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AndSextSext_local rewriter op opInBounds

-- (sext X) | (sext Y) → sext (X | Y)
def OrSextSext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, oprops) := matchOr op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchSext dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchSext dY ctx | return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .or) #[x.getType! ctx.raw] #[x, y]
    #[] #[] oprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def OrSextSext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite OrSextSext_local rewriter op opInBounds

-- (sext X) ^ (sext Y) → sext (X ^ Y)
def XorSextSext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, xprops) := matchXor op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchSext dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchSext dY ctx | return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .xor) #[x.getType! ctx.raw] #[x, y]
    #[] #[] xprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def XorSextSext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite XorSextSext_local rewriter op opInBounds

-- (zext X) & (zext Y) → zext (X & Y)
def AndZextZext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, _) := matchAnd op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchZext dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchZext dY ctx | return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[x, y]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndZextZext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AndZextZext_local rewriter op opInBounds

-- (zext X) | (zext Y) → zext (X | Y)
def OrZextZext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, oprops) := matchOr op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchZext dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchZext dY ctx | return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .or) #[x.getType! ctx.raw] #[x, y]
    #[] #[] oprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def OrZextZext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite OrZextZext_local rewriter op opInBounds

-- (zext X) ^ (zext Y) → zext (X ^ Y)
def XorZextZext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, xprops) := matchXor op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchZext dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchZext dY ctx | return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .xor) #[x.getType! ctx.raw] #[x, y]
    #[] #[] xprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def XorZextZext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite XorZextZext_local rewriter op opInBounds

-- (trunc X) & (trunc Y) → trunc (X & Y)
def AndTruncTrunc_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, _) := matchAnd op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchTrunc dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchTrunc dY ctx | return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[x, y]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .trunc) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndTruncTrunc (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AndTruncTrunc_local rewriter op opInBounds

-- (trunc X) | (trunc Y) → trunc (X | Y)
def OrTruncTrunc_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, oprops) := matchOr op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchTrunc dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchTrunc dY ctx | return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .or) #[x.getType! ctx.raw] #[x, y]
    #[] #[] oprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .trunc) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def OrTruncTrunc (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite OrTruncTrunc_local rewriter op opInBounds

-- (trunc X) ^ (trunc Y) → trunc (X ^ Y)
def XorTruncTrunc_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, xprops) := matchXor op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _xp) := matchTrunc dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, yp) := matchTrunc dY ctx | return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .xor) #[x.getType! ctx.raw] #[x, y]
    #[] #[] xprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .trunc) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(inner.getResult 0)]
    #[] #[] yp none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def XorTruncTrunc (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite XorTruncTrunc_local rewriter op opInBounds

-- (X << Z) & (Y << Z) → (X & Y) << Z
def AndShlShl_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, _) := matchAnd op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _p0) := matchShl dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, p1) := matchShl dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[x, y]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .shl) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndShlShl (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AndShlShl_local rewriter op opInBounds

-- (X << Z) | (Y << Z) → (X | Y) << Z
def OrShlShl_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, oprops) := matchOr op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _p0) := matchShl dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, p1) := matchShl dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .or) #[x.getType! ctx.raw] #[x, y]
    #[] #[] oprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .shl) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def OrShlShl (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite OrShlShl_local rewriter op opInBounds

-- (X << Z) ^ (Y << Z) → (X ^ Y) << Z
def XorShlShl_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, xprops) := matchXor op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _p0) := matchShl dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, p1) := matchShl dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .xor) #[x.getType! ctx.raw] #[x, y]
    #[] #[] xprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .shl) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def XorShlShl (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite XorShlShl_local rewriter op opInBounds

-- (X >> Z) & (Y >> Z) → (X & Y) >> Z   (logical)
def AndLshrLshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, _) := matchAnd op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _p0) := matchLshr dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, p1) := matchLshr dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[x, y]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .lshr) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndLshrLshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AndLshrLshr_local rewriter op opInBounds

-- (X >> Z) | (Y >> Z) → (X | Y) >> Z   (logical)
def OrLshrLshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, oprops) := matchOr op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _p0) := matchLshr dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, p1) := matchLshr dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .or) #[x.getType! ctx.raw] #[x, y]
    #[] #[] oprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .lshr) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def OrLshrLshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite OrLshrLshr_local rewriter op opInBounds

-- (X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z   (logical)
def XorLshrLshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, xprops) := matchXor op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _p0) := matchLshr dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, p1) := matchLshr dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .xor) #[x.getType! ctx.raw] #[x, y]
    #[] #[] xprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .lshr) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def XorLshrLshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite XorLshrLshr_local rewriter op opInBounds

-- (X >> Z) & (Y >> Z) → (X & Y) >> Z   (arithmetic)
def AndAshrAshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, _) := matchAnd op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _p0) := matchAshr dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, p1) := matchAshr dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[x, y]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .ashr) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndAshrAshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AndAshrAshr_local rewriter op opInBounds

-- (X >> Z) | (Y >> Z) → (X | Y) >> Z   (arithmetic)
def OrAshrAshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, oprops) := matchOr op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _p0) := matchAshr dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, p1) := matchAshr dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .or) #[x.getType! ctx.raw] #[x, y]
    #[] #[] oprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .ashr) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def OrAshrAshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite OrAshrAshr_local rewriter op opInBounds

-- (X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z   (arithmetic)
def XorAshrAshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, xprops) := matchXor op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _p0) := matchAshr dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, p1) := matchAshr dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .xor) #[x.getType! ctx.raw] #[x, y]
    #[] #[] xprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .ashr) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] p1 none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def XorAshrAshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite XorAshrAshr_local rewriter op opInBounds

-- (X & Z) & (Y & Z) → (X & Y) & Z
def AndAndAnd_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, _) := matchAnd op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _) := matchAnd dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, _) := matchAnd dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[x, y]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] () none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def AndAndAnd (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AndAndAnd_local rewriter op opInBounds

-- (X & Z) | (Y & Z) → (X | Y) & Z
def OrAndAnd_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, oprops) := matchOr op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _) := matchAnd dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, _) := matchAnd dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .or) #[x.getType! ctx.raw] #[x, y]
    #[] #[] oprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] () none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def OrAndAnd (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite OrAndAnd_local rewriter op opInBounds

-- (X & Z) ^ (Y & Z) → (X ^ Y) & Z
def XorAndAnd_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, xprops) := matchXor op ctx | return (ctx, none)
  let some dX := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, z0, _) := matchAnd dX ctx | return (ctx, none)
  let some dY := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, z1, _) := matchAnd dY ctx | return (ctx, none)
  if z0 != z1 then return (ctx, none)
  let (ctx, inner) ← WfRewriter.createOp! ctx (.llvm .xor) #[x.getType! ctx.raw] #[x, y]
    #[] #[] xprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[(inner.getResult 0), z0]
    #[] #[] () none
  some (ctx, some (#[inner, newOp], #[newOp.getResult 0]))

def XorAndAnd (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite XorAndAnd_local rewriter op opInBounds

/-! ### sub_add_reg -/

-- (x + y) - y → x
def sub_add_reg_x_add_y_sub_y_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (s0, s1, _sp) := matchSub op ctx | return (ctx, none)
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
  let some dAdd := getDefiningOp s0 ctx | return (ctx, none)
  let some (x, y, _ap) := matchAdd dAdd ctx | return (ctx, none)
  if x != s1 then return (ctx, none)
  some (ctx, some (#[], #[y]))

def sub_add_reg_x_add_y_sub_x (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_add_reg_x_add_y_sub_x_local rewriter op opInBounds

-- x - (y + x) → 0 - y
def sub_add_reg_x_sub_y_add_x_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (s0, s1, sp) := matchSub op ctx | return (ctx, none)
  let some dAdd := getDefiningOp s1 ctx | return (ctx, none)
  let some (y, x, _ap) := matchAdd dAdd ctx | return (ctx, none)
  if x != s0 then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[y.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub) #[s0.getType! ctx.raw] #[(c0.getResult 0), y]
    #[] #[] sp none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def sub_add_reg_x_sub_y_add_x (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_add_reg_x_sub_y_add_x_local rewriter op opInBounds

-- x - (x + y) → 0 - y
def sub_add_reg_x_sub_x_add_y_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (s0, s1, sp) := matchSub op ctx | return (ctx, none)
  let some dAdd := getDefiningOp s1 ctx | return (ctx, none)
  let some (x, y, _ap) := matchAdd dAdd ctx | return (ctx, none)
  if x != s0 then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[y.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub) #[s0.getType! ctx.raw] #[(c0.getResult 0), y]
    #[] #[] sp none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def sub_add_reg_x_sub_x_add_y (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_add_reg_x_sub_x_add_y_local rewriter op opInBounds

/-! ### xor_of_and_with_same_reg :  (xor (and x, y), y) → (and (not x), y) -/

def xor_of_and_with_same_reg_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (andVal, yval, _xp) := matchXor op ctx | return (ctx, none)
  let some dA := getDefiningOp andVal ctx | return (ctx, none)
  let some (x, y2, _) := matchAnd dA ctx | return (ctx, none)
  if y2 != yval then return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let m1 := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) xty))
  let (ctx, c1) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] m1 none
  let (ctx, notx) ← WfRewriter.createOp! ctx (.llvm .xor) #[x.getType! ctx.raw] #[x, (c1.getResult 0)]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and) #[x.getType! ctx.raw] #[(notx.getResult 0), yval]
    #[] #[] () none
  some (ctx, some (#[c1, notx, newOp], #[newOp.getResult 0]))

def xor_of_and_with_same_reg (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite xor_of_and_with_same_reg_local rewriter op opInBounds

/-! ### select_to_iminmax  (ported to LLVM min/max intrinsics — see assumption (D))

  (icmp pred X Y) ? X : Y → {u,s}{max,min} X Y
-/

-- ugt → umax
def select_to_iminmax_ugt_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some dI := getDefiningOp cond ctx | return (ctx, none)
  let some (il, ir, ip) := matchIcmp dI ctx | return (ctx, none)
  let .ugt := ip.predicate | return (ctx, none)
  if il != tv then return (ctx, none)
  if ir != fv then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__umax) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[tv, fv]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_to_iminmax_ugt (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_to_iminmax_ugt_local rewriter op opInBounds

-- uge → umax
def select_to_iminmax_uge_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some dI := getDefiningOp cond ctx | return (ctx, none)
  let some (il, ir, ip) := matchIcmp dI ctx | return (ctx, none)
  let .uge := ip.predicate | return (ctx, none)
  if il != tv then return (ctx, none)
  if ir != fv then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__umax) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[tv, fv]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_to_iminmax_uge (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_to_iminmax_uge_local rewriter op opInBounds

-- sgt → smax
def select_to_iminmax_sgt_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some dI := getDefiningOp cond ctx | return (ctx, none)
  let some (il, ir, ip) := matchIcmp dI ctx | return (ctx, none)
  let .sgt := ip.predicate | return (ctx, none)
  if il != tv then return (ctx, none)
  if ir != fv then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__smax) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[tv, fv]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_to_iminmax_sgt (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_to_iminmax_sgt_local rewriter op opInBounds

-- sge → smax.
def select_to_iminmax_sge_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some dI := getDefiningOp cond ctx | return (ctx, none)
  let some (il, ir, ip) := matchIcmp dI ctx | return (ctx, none)
  let .sge := ip.predicate | return (ctx, none)
  if il != tv then return (ctx, none)
  if ir != fv then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__smax) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[tv, fv]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_to_iminmax_sge (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_to_iminmax_sge_local rewriter op opInBounds

-- ult → umin
def select_to_iminmax_ult_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some dI := getDefiningOp cond ctx | return (ctx, none)
  let some (il, ir, ip) := matchIcmp dI ctx | return (ctx, none)
  let .ult := ip.predicate | return (ctx, none)
  if il != tv then return (ctx, none)
  if ir != fv then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__umin) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[tv, fv]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_to_iminmax_ult (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_to_iminmax_ult_local rewriter op opInBounds

-- ule → umin
def select_to_iminmax_ule_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some dI := getDefiningOp cond ctx | return (ctx, none)
  let some (il, ir, ip) := matchIcmp dI ctx | return (ctx, none)
  let .ule := ip.predicate | return (ctx, none)
  if il != tv then return (ctx, none)
  if ir != fv then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__umin) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[tv, fv]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_to_iminmax_ule (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_to_iminmax_ule_local rewriter op opInBounds

-- slt → smin
def select_to_iminmax_slt_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some dI := getDefiningOp cond ctx | return (ctx, none)
  let some (il, ir, ip) := matchIcmp dI ctx | return (ctx, none)
  let .slt := ip.predicate | return (ctx, none)
  if il != tv then return (ctx, none)
  if ir != fv then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__smin) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[tv, fv]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_to_iminmax_slt (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_to_iminmax_slt_local rewriter op opInBounds

-- sle → smin
def select_to_iminmax_sle_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some dI := getDefiningOp cond ctx | return (ctx, none)
  let some (il, ir, ip) := matchIcmp dI ctx | return (ctx, none)
  let .sle := ip.predicate | return (ctx, none)
  if il != tv then return (ctx, none)
  if ir != fv then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__smin) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[tv, fv]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_to_iminmax_sle (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_to_iminmax_sle_local rewriter op opInBounds

/-! ### cast_of_cast_combines -/

-- trunc (zext x) where trunc result type = x's type → x
def trunc_of_zext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, _tp) := matchTrunc op ctx | return (ctx, none)
  let some dZ := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _zp) := matchZext dZ ctx | return (ctx, none)
  if (op.getResult 0 : ValuePtr).getType! ctx.raw != x.getType! ctx.raw then return (ctx, none)
  some (ctx, some (#[], #[x]))

def trunc_of_zext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite trunc_of_zext_local rewriter op opInBounds

/-! ### select_of_{zext,truncate} : cast(select c,t,f) → select c, cast t, cast f -/

def select_of_zext_rw_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, zp) := matchZext op ctx | return (ctx, none)
  let some dS := getDefiningOp v0 ctx | return (ctx, none)
  let some (cond, tv, fv) := matchSelect dS ctx | return (ctx, none)
  let outTy := (op.getResult 0 : ValuePtr).getType! ctx.raw
  let (ctx, zt) ← WfRewriter.createOp! ctx (.llvm .zext) #[outTy] #[tv]
    #[] #[] zp none
  let (ctx, zf) ← WfRewriter.createOp! ctx (.llvm .zext) #[outTy] #[fv]
    #[] #[] zp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .select) #[outTy] #[cond, (zt.getResult 0), (zf.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[zt, zf, newOp], #[newOp.getResult 0]))

def select_of_zext_rw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_of_zext_rw_local rewriter op opInBounds

def select_of_truncate_rw_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, tp) := matchTrunc op ctx | return (ctx, none)
  let some dS := getDefiningOp v0 ctx | return (ctx, none)
  let some (cond, tv, fv) := matchSelect dS ctx | return (ctx, none)
  let outTy := (op.getResult 0 : ValuePtr).getType! ctx.raw
  let (ctx, tt) ← WfRewriter.createOp! ctx (.llvm .trunc) #[outTy] #[tv]
    #[] #[] tp none
  let (ctx, tf) ← WfRewriter.createOp! ctx (.llvm .trunc) #[outTy] #[fv]
    #[] #[] tp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .select) #[outTy] #[cond, (tt.getResult 0), (tf.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[tt, tf, newOp], #[newOp.getResult 0]))

def select_of_truncate_rw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_of_truncate_rw_local rewriter op opInBounds

/-! ### matchMulOBy2 :  (mul x, 2) → (add x, x)   (overflow flags threaded via props)
-/

def mulo_by_2_unsigned_signed_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, cval, mp) := matchMul op ctx | return (ctx, none)
  let some cst := matchConstantIntVal cval ctx | return (ctx, none)
  if cst.value ≠ 2 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[x.getType! ctx.raw] #[x, x]
    #[] #[] mp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def mulo_by_2_unsigned_signed (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mulo_by_2_unsigned_signed_local rewriter op opInBounds

/-! ### add_shift :  A + shl(0 - B, C) → A - shl(B, C) -/

def add_shift_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, shlNeg, _ap) := matchAdd op ctx | return (ctx, none)
  let some dShl := getDefiningOp shlNeg ctx | return (ctx, none)
  let some (negB, c, shp) := matchShl dShl ctx | return (ctx, none)
  let some dSub := getDefiningOp negB ctx | return (ctx, none)
  let some (zeroV, b, subp) := matchSub dSub ctx | return (ctx, none)
  let some zc := matchConstantIntVal zeroV ctx | return (ctx, none)
  if zc.value ≠ 0 then return (ctx, none)
  let (ctx, newShl) ← WfRewriter.createOp! ctx (.llvm .shl) #[b.getType! ctx.raw] #[b, c]
    #[] #[] shp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (newShl.getResult 0)]
    #[] #[] subp none
  some (ctx, some (#[newShl, newOp], #[newOp.getResult 0]))

def add_shift (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite add_shift_local rewriter op opInBounds

-- A + shl(0 - B, C) → A - shl(B, C)   (add operands commuted)
def add_shift_commute_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (shlNeg, a, _ap) := matchAdd op ctx | return (ctx, none)
  let some dShl := getDefiningOp shlNeg ctx | return (ctx, none)
  let some (negB, c, shp) := matchShl dShl ctx | return (ctx, none)
  let some dSub := getDefiningOp negB ctx | return (ctx, none)
  let some (zeroV, b, subp) := matchSub dSub ctx | return (ctx, none)
  let some zc := matchConstantIntVal zeroV ctx | return (ctx, none)
  if zc.value ≠ 0 then return (ctx, none)
  let (ctx, newShl) ← WfRewriter.createOp! ctx (.llvm .shl) #[b.getType! ctx.raw] #[b, c]
    #[] #[] shp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (newShl.getResult 0)]
    #[] #[] subp none
  some (ctx, some (#[newShl, newOp], #[newOp.getResult 0]))

def add_shift_commute (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite add_shift_commute_local rewriter op opInBounds

/-! ### redundant_binop_in_equality

  ((X op Y) cmp X) → (Y cmp 0)  for op ∈ {+, -, ^}, cmp ∈ {==, !=}.
-/

def redundant_binop_in_equality_XPlusYEqX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhsV, xval, ip) := matchIcmp op ctx | return (ctx, none)
  let .eq := ip.predicate | return (ctx, none)
  let some dAdd := getDefiningOp lhsV ctx | return (ctx, none)
  let some (x, y, _ap) := matchAdd dAdd ctx | return (ctx, none)
  if x != xval then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[y.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def redundant_binop_in_equality_XPlusYEqX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite redundant_binop_in_equality_XPlusYEqX_local rewriter op opInBounds

def redundant_binop_in_equality_XPlusYNeX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhsV, xval, ip) := matchIcmp op ctx | return (ctx, none)
  let .ne := ip.predicate | return (ctx, none)
  let some dAdd := getDefiningOp lhsV ctx | return (ctx, none)
  let some (x, y, _ap) := matchAdd dAdd ctx | return (ctx, none)
  if x != xval then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[y.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def redundant_binop_in_equality_XPlusYNeX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite redundant_binop_in_equality_XPlusYNeX_local rewriter op opInBounds

def redundant_binop_in_equality_XMinusYEqX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhsV, xval, ip) := matchIcmp op ctx | return (ctx, none)
  let .eq := ip.predicate | return (ctx, none)
  let some dSub := getDefiningOp lhsV ctx | return (ctx, none)
  let some (x, y, _sp) := matchSub dSub ctx | return (ctx, none)
  if x != xval then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[y.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def redundant_binop_in_equality_XMinusYEqX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite redundant_binop_in_equality_XMinusYEqX_local rewriter op opInBounds

def redundant_binop_in_equality_XMinusYNeX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhsV, xval, ip) := matchIcmp op ctx | return (ctx, none)
  let .ne := ip.predicate | return (ctx, none)
  let some dSub := getDefiningOp lhsV ctx | return (ctx, none)
  let some (x, y, _sp) := matchSub dSub ctx | return (ctx, none)
  if x != xval then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[y.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def redundant_binop_in_equality_XMinusYNeX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite redundant_binop_in_equality_XMinusYNeX_local rewriter op opInBounds

def redundant_binop_in_equality_XXorYEqX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhsV, xval, ip) := matchIcmp op ctx | return (ctx, none)
  let .eq := ip.predicate | return (ctx, none)
  let some dXor := getDefiningOp lhsV ctx | return (ctx, none)
  let some (x, y, _xp) := matchXor dXor ctx | return (ctx, none)
  if x != xval then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[y.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def redundant_binop_in_equality_XXorYEqX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite redundant_binop_in_equality_XXorYEqX_local rewriter op opInBounds

def redundant_binop_in_equality_XXorYNeX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhsV, xval, ip) := matchIcmp op ctx | return (ctx, none)
  let .ne := ip.predicate | return (ctx, none)
  let some dXor := getDefiningOp lhsV ctx | return (ctx, none)
  let some (x, y, _xp) := matchXor dXor ctx | return (ctx, none)
  if x != xval then return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) yty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[y.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[y, (c0.getResult 0)]
    #[] #[] ip none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def redundant_binop_in_equality_XXorYNeX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite redundant_binop_in_equality_XXorYNeX_local rewriter op opInBounds

/-! ### match_selects -/

-- select c, 1, 0 → zext c
def select_1_0_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some ct := matchConstantIntVal tv ctx | return (ctx, none)
  if ct.value ≠ 1 then return (ctx, none)
  let some cf := matchConstantIntVal fv ctx | return (ctx, none)
  if cf.value ≠ 0 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[cond]
    #[] #[] { nneg := false } none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_1_0 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_1_0_local rewriter op opInBounds

-- select c, -1, 0 → sext c
def select_neg1_0_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some ct := matchConstantIntVal tv ctx | return (ctx, none)
  if ct.value ≠ -1 then return (ctx, none)
  let some cf := matchConstantIntVal fv ctx | return (ctx, none)
  if cf.value ≠ 0 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[cond]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_neg1_0 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_neg1_0_local rewriter op opInBounds

-- select c, 0, 1 → zext (not c)
def select_0_1_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some ct := matchConstantIntVal tv ctx | return (ctx, none)
  if ct.value ≠ 0 then return (ctx, none)
  let some cf := matchConstantIntVal fv ctx | return (ctx, none)
  if cf.value ≠ 1 then return (ctx, none)
  let .integerType cty := (cond.getType! ctx.raw).val | return (ctx, none)
  let m1 := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) cty))
  let (ctx, c1) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[cond.getType! ctx.raw] #[]
    #[] #[] m1 none
  let (ctx, ncond) ← WfRewriter.createOp! ctx (.llvm .xor) #[cond.getType! ctx.raw] #[cond, (c1.getResult 0)]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .zext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(ncond.getResult 0)]
    #[] #[] { nneg := false } none
  some (ctx, some (#[c1, ncond, newOp], #[newOp.getResult 0]))

def select_0_1 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_0_1_local rewriter op opInBounds

-- select c, 0, -1 → sext (not c)
def select_0_neg1_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some ct := matchConstantIntVal tv ctx | return (ctx, none)
  if ct.value ≠ 0 then return (ctx, none)
  let some cf := matchConstantIntVal fv ctx | return (ctx, none)
  if cf.value ≠ -1 then return (ctx, none)
  let .integerType cty := (cond.getType! ctx.raw).val | return (ctx, none)
  let m1 := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) cty))
  let (ctx, c1) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[cond.getType! ctx.raw] #[]
    #[] #[] m1 none
  let (ctx, ncond) ← WfRewriter.createOp! ctx (.llvm .xor) #[cond.getType! ctx.raw] #[cond, (c1.getResult 0)]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sext) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(ncond.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[c1, ncond, newOp], #[newOp.getResult 0]))

def select_0_neg1 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_0_neg1_local rewriter op opInBounds

/-! ### not_cmp_fold :  (icmp pred X Y) ^ -1 → (icmp invPred X Y) -/

def not_cmp_fold_eq_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some icmpV := matchNot (op.getResult 0) ctx | return (ctx, none)
  let some dI := getDefiningOp icmpV ctx | return (ctx, none)
  let some (x, y, ip) := matchIcmp dI ctx | return (ctx, none)
  let .eq := ip.predicate | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .ne) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def not_cmp_fold_eq (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite not_cmp_fold_eq_local rewriter op opInBounds

def not_cmp_fold_ne_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some icmpV := matchNot (op.getResult 0) ctx | return (ctx, none)
  let some dI := getDefiningOp icmpV ctx | return (ctx, none)
  let some (x, y, ip) := matchIcmp dI ctx | return (ctx, none)
  let .ne := ip.predicate | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .eq) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def not_cmp_fold_ne (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite not_cmp_fold_ne_local rewriter op opInBounds

def not_cmp_fold_ugt_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some icmpV := matchNot (op.getResult 0) ctx | return (ctx, none)
  let some dI := getDefiningOp icmpV ctx | return (ctx, none)
  let some (x, y, ip) := matchIcmp dI ctx | return (ctx, none)
  let .ugt := ip.predicate | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .ule) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def not_cmp_fold_ugt (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite not_cmp_fold_ugt_local rewriter op opInBounds

def not_cmp_fold_uge_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some icmpV := matchNot (op.getResult 0) ctx | return (ctx, none)
  let some dI := getDefiningOp icmpV ctx | return (ctx, none)
  let some (x, y, ip) := matchIcmp dI ctx | return (ctx, none)
  let .uge := ip.predicate | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .ult) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def not_cmp_fold_uge (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite not_cmp_fold_uge_local rewriter op opInBounds

def not_cmp_fold_sgt_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some icmpV := matchNot (op.getResult 0) ctx | return (ctx, none)
  let some dI := getDefiningOp icmpV ctx | return (ctx, none)
  let some (x, y, ip) := matchIcmp dI ctx | return (ctx, none)
  let .sgt := ip.predicate | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .sle) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def not_cmp_fold_sgt (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite not_cmp_fold_sgt_local rewriter op opInBounds

def not_cmp_fold_sge_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some icmpV := matchNot (op.getResult 0) ctx | return (ctx, none)
  let some dI := getDefiningOp icmpV ctx | return (ctx, none)
  let some (x, y, ip) := matchIcmp dI ctx | return (ctx, none)
  let .sge := ip.predicate | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y]
    #[] #[] (IcmpProperties.mk .slt) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def not_cmp_fold_sge (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite not_cmp_fold_sge_local rewriter op opInBounds

/-! ### double_icmp_zero_combine -/

-- (X == 0 & Y == 0) → (X | Y) == 0
def double_icmp_zero_and_combine_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, _andprops) := matchAnd op ctx | return (ctx, none)
  let some dL := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, cx, ip0) := matchIcmp dL ctx | return (ctx, none)
  let .eq := ip0.predicate | return (ctx, none)
  let some cxv := matchConstantIntVal cx ctx | return (ctx, none)
  if cxv.value ≠ 0 then return (ctx, none)
  let some dR := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, cy, ip1) := matchIcmp dR ctx | return (ctx, none)
  let .eq := ip1.predicate | return (ctx, none)
  let some cyv := matchConstantIntVal cy ctx | return (ctx, none)
  if cyv.value ≠ 0 then return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) xty))
  let (ctx, orOp) ← WfRewriter.createOp! ctx (.llvm .or) #[x.getType! ctx.raw] #[x, y]
    #[] #[] { disjoint := false } none
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(orOp.getResult 0), (c0.getResult 0)]
    #[] #[] ip0 none
  some (ctx, some (#[orOp, c0, newOp], #[newOp.getResult 0]))

def double_icmp_zero_and_combine (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite double_icmp_zero_and_combine_local rewriter op opInBounds

-- (X != 0 | Y != 0) → (X | Y) != 0
def double_icmp_zero_or_combine_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, v1, oprops) := matchOr op ctx | return (ctx, none)
  let some dL := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, cx, ip0) := matchIcmp dL ctx | return (ctx, none)
  let .ne := ip0.predicate | return (ctx, none)
  let some cxv := matchConstantIntVal cx ctx | return (ctx, none)
  if cxv.value ≠ 0 then return (ctx, none)
  let some dR := getDefiningOp v1 ctx | return (ctx, none)
  let some (y, cy, ip1) := matchIcmp dR ctx | return (ctx, none)
  let .ne := ip1.predicate | return (ctx, none)
  let some cyv := matchConstantIntVal cy ctx | return (ctx, none)
  if cyv.value ≠ 0 then return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) xty))
  let (ctx, orOp) ← WfRewriter.createOp! ctx (.llvm .or) #[x.getType! ctx.raw] #[x, y]
    #[] #[] oprops none
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(orOp.getResult 0), (c0.getResult 0)]
    #[] #[] ip0 none
  some (ctx, some (#[orOp, c0, newOp], #[newOp.getResult 0]))

def double_icmp_zero_or_combine (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite double_icmp_zero_or_combine_local rewriter op opInBounds

/-! ### NotAPlusNegOne :  (not (add X, -1)) → (sub 0, X) -/

def NotAPlusNegOne_rw_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some addVal := matchNot (op.getResult 0) ctx | return (ctx, none)
  let some dAdd := getDefiningOp addVal ctx | return (ctx, none)
  let some (x, cm1, ap) := matchAdd dAdd ctx | return (ctx, none)
  let some cst := matchConstantIntVal cm1 ctx | return (ctx, none)
  if cst.value ≠ -1 then return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (0) xty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub) #[x.getType! ctx.raw] #[(c0.getResult 0), x]
    #[] #[] ap none
  some (ctx, some (#[c0, newOp], #[newOp.getResult 0]))

def NotAPlusNegOne_rw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite NotAPlusNegOne_rw_local rewriter op opInBounds

/-! ### sub_one_from_sub :  (A - B) - 1 → add (xor B, -1), A -/

def sub_one_from_sub_rw_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (subVal, c1v, sp) := matchSub op ctx | return (ctx, none)
  let some cst1 := matchConstantIntVal c1v ctx | return (ctx, none)
  if cst1.value ≠ 1 then return (ctx, none)
  let some dSub := getDefiningOp subVal ctx | return (ctx, none)
  let some (x, y, _sp2) := matchSub dSub ctx | return (ctx, none)
  let .integerType yty := (y.getType! ctx.raw).val | return (ctx, none)
  let m1 := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-1) yty))
  let (ctx, cm1) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[y.getType! ctx.raw] #[]
    #[] #[] m1 none
  let (ctx, xorOp) ← WfRewriter.createOp! ctx (.llvm .xor) #[y.getType! ctx.raw] #[y, (cm1.getResult 0)]
    #[] #[] () none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(xorOp.getResult 0), x]
    #[] #[] sp none
  some (ctx, some (#[cm1, xorOp, newOp], #[newOp.getResult 0]))

def sub_one_from_sub_rw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_one_from_sub_rw_local rewriter op opInBounds

/-! ### APlusC1MinusC2 :  (A + C1) - C2 → A + (C1 - C2)   (C1, C2 constants) -/

def APlusC1MinusC2_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (addVal, c2v, _sp) := matchSub op ctx | return (ctx, none)
  let some c2 := matchConstantIntVal c2v ctx | return (ctx, none)
  let some dAdd := getDefiningOp addVal ctx | return (ctx, none)
  let some (a, c1v, ap) := matchAdd dAdd ctx | return (ctx, none)
  let some c1 := matchConstantIntVal c1v ctx | return (ctx, none)
  let .integerType aty := (a.getType! ctx.raw).val | return (ctx, none)
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value - c2.value) aty))
  let (ctx, cf) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[a.getType! ctx.raw] #[]
    #[] #[] folded none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (cf.getResult 0)]
    #[] #[] ap none
  some (ctx, some (#[cf, newOp], #[newOp.getResult 0]))

def APlusC1MinusC2 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite APlusC1MinusC2_local rewriter op opInBounds

/-! ### C2MinusAPlusC1 :  C2 - (A + C1) → (C2 - C1) - A   (C1, C2 constants) -/

def C2MinusAPlusC1_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (c2v, addVal, sp) := matchSub op ctx | return (ctx, none)
  let some c2 := matchConstantIntVal c2v ctx | return (ctx, none)
  let some dAdd := getDefiningOp addVal ctx | return (ctx, none)
  let some (a, c1v, _ap) := matchAdd dAdd ctx | return (ctx, none)
  let some c1 := matchConstantIntVal c1v ctx | return (ctx, none)
  let .integerType aty := (a.getType! ctx.raw).val | return (ctx, none)
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c2.value - c1.value) aty))
  let (ctx, cf) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[a.getType! ctx.raw] #[]
    #[] #[] folded none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(cf.getResult 0), a]
    #[] #[] sp none
  some (ctx, some (#[cf, newOp], #[newOp.getResult 0]))

def C2MinusAPlusC1 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite C2MinusAPlusC1_local rewriter op opInBounds

/-! ### AMinusC1MinusC2 :  (A - C1) - C2 → A - (C1 + C2)   (C1, C2 constants) -/

def AMinusC1MinusC2_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (subVal, c2v, sp) := matchSub op ctx | return (ctx, none)
  let some c2 := matchConstantIntVal c2v ctx | return (ctx, none)
  let some dSub := getDefiningOp subVal ctx | return (ctx, none)
  let some (a, c1v, _sp2) := matchSub dSub ctx | return (ctx, none)
  let some c1 := matchConstantIntVal c1v ctx | return (ctx, none)
  let .integerType aty := (a.getType! ctx.raw).val | return (ctx, none)
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value + c2.value) aty))
  let (ctx, cf) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[a.getType! ctx.raw] #[]
    #[] #[] folded none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (cf.getResult 0)]
    #[] #[] sp none
  some (ctx, some (#[cf, newOp], #[newOp.getResult 0]))

def AMinusC1MinusC2 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AMinusC1MinusC2_local rewriter op opInBounds

/-! ### C1MinusAMinusC2 :  (C1 - A) - C2 → (C1 - C2) - A   (C1, C2 constants) -/

def C1MinusAMinusC2_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (subVal, c2v, sp) := matchSub op ctx | return (ctx, none)
  let some c2 := matchConstantIntVal c2v ctx | return (ctx, none)
  let some dSub := getDefiningOp subVal ctx | return (ctx, none)
  let some (c1v, a, _sp2) := matchSub dSub ctx | return (ctx, none)
  let some c1 := matchConstantIntVal c1v ctx | return (ctx, none)
  let .integerType aty := (a.getType! ctx.raw).val | return (ctx, none)
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value - c2.value) aty))
  let (ctx, cf) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[a.getType! ctx.raw] #[]
    #[] #[] folded none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(cf.getResult 0), a]
    #[] #[] sp none
  some (ctx, some (#[cf, newOp], #[newOp.getResult 0]))

def C1MinusAMinusC2 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite C1MinusAMinusC2_local rewriter op opInBounds

/-! ### AMinusC1PlusC2 :  (A - C1) + C2 → A + (C2 - C1)   (C1, C2 constants) -/

def AMinusC1PlusC2_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (subVal, c2v, ap) := matchAdd op ctx | return (ctx, none)
  let some c2 := matchConstantIntVal c2v ctx | return (ctx, none)
  let some dSub := getDefiningOp subVal ctx | return (ctx, none)
  let some (a, c1v, _sp) := matchSub dSub ctx | return (ctx, none)
  let some c1 := matchConstantIntVal c1v ctx | return (ctx, none)
  let .integerType aty := (a.getType! ctx.raw).val | return (ctx, none)
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c2.value - c1.value) aty))
  let (ctx, cf) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[a.getType! ctx.raw] #[]
    #[] #[] folded none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (cf.getResult 0)]
    #[] #[] ap none
  some (ctx, some (#[cf, newOp], #[newOp.getResult 0]))

def AMinusC1PlusC2 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AMinusC1PlusC2_local rewriter op opInBounds

/-! ### or_and_xor_to_xor_or :  (X & Y) | ~Y  →  X | ~Y -/
def or_and_xor_to_xor_or_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (andV, notV, oprops) := matchOr op ctx | return (ctx, none)
  let some dAnd := getDefiningOp andV ctx | return (ctx, none)
  let some (x, y, _aprops) := matchAnd dAnd ctx | return (ctx, none)
  let some dNot := getDefiningOp notV ctx | return (ctx, none)
  let some (y1, m1v, _xprops) := matchXor dNot ctx | return (ctx, none)
  if y1 != y then return (ctx, none)
  let some cst := matchConstantIntVal m1v ctx | return (ctx, none)
  if cst.value ≠ -1 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .or) #[andV.getType! ctx.raw] #[x, notV]
    #[] #[] oprops none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def or_and_xor_to_xor_or (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite or_and_xor_to_xor_or_local rewriter op opInBounds

/-! ### and_xor_or_to_xor_and :  (X | Y) & ~Y  →  X & ~Y -/
def and_xor_or_to_xor_and_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (orV, notV, _aprops) := matchAnd op ctx | return (ctx, none)
  let some dOr := getDefiningOp orV ctx | return (ctx, none)
  let some (x, y, _oprops) := matchOr dOr ctx | return (ctx, none)
  let some dNot := getDefiningOp notV ctx | return (ctx, none)
  let some (y1, m1v, _xprops) := matchXor dNot ctx | return (ctx, none)
  if y1 != y then return (ctx, none)
  let some cst := matchConstantIntVal m1v ctx | return (ctx, none)
  if cst.value ≠ -1 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and) #[orV.getType! ctx.raw] #[x, notV]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def and_xor_or_to_xor_and (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite and_xor_or_to_xor_and_local rewriter op opInBounds

/-! ### combine_or_of_and :  or (and x, y), x  →  x -/

-- or (and x, y), x  →  x   (the `and` is the left OR operand)
def combine_or_of_and_l_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (andV, x, _oprops) := matchOr op ctx | return (ctx, none)
  let some dAnd := getDefiningOp andV ctx | return (ctx, none)
  let some (a0, a1, _aprops) := matchAnd dAnd ctx | return (ctx, none)
  if a0 != x && a1 != x then return (ctx, none)
  some (ctx, some (#[], #[x]))

def combine_or_of_and_l (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite combine_or_of_and_l_local rewriter op opInBounds

-- or x, (and x, y)  →  x   (the `and` is the right OR operand)
def combine_or_of_and_r_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, andV, _oprops) := matchOr op ctx | return (ctx, none)
  let some dAnd := getDefiningOp andV ctx | return (ctx, none)
  let some (a0, a1, _aprops) := matchAnd dAnd ctx | return (ctx, none)
  if a0 != x && a1 != x then return (ctx, none)
  some (ctx, some (#[], #[x]))

def combine_or_of_and_r (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite combine_or_of_and_r_local rewriter op opInBounds

/-! ### AMinusBMinusC :  A - (B - C)  →  A + (C - B) -/
def AMinusBMinusC_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (A, sub1, sprops) := matchSub op ctx | return (ctx, none)
  let some dSub := getDefiningOp sub1 ctx | return (ctx, none)
  let some (B, C, _sprops1) := matchSub dSub ctx | return (ctx, none)
  let (ctx, cMinusB) ← WfRewriter.createOp! ctx (.llvm .sub) #[sub1.getType! ctx.raw] #[C, B]
    #[] #[] sprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[A.getType! ctx.raw] #[A, (cMinusB.getResult 0)]
    #[] #[] sprops none
  some (ctx, some (#[cMinusB, newOp], #[newOp.getResult 0]))

def AMinusBMinusC (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite AMinusBMinusC_local rewriter op opInBounds

/-! ### binop_left_to_zero :  (0 op x)  →  0   for op ∈ {shl, lshr, ashr, mul} -/

def shl_left_to_zero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (zero, _rhs, _props) := matchShl op ctx | return (ctx, none)
  let some cst := matchConstantIntVal zero ctx | return (ctx, none)
  if cst.value ≠ 0 then return (ctx, none)
  some (ctx, some (#[], #[zero]))

def shl_left_to_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite shl_left_to_zero_local rewriter op opInBounds

def lshr_left_to_zero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (zero, _rhs, _props) := matchLshr op ctx | return (ctx, none)
  let some cst := matchConstantIntVal zero ctx | return (ctx, none)
  if cst.value ≠ 0 then return (ctx, none)
  some (ctx, some (#[], #[zero]))

def lshr_left_to_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite lshr_left_to_zero_local rewriter op opInBounds

def ashr_left_to_zero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (zero, _rhs, _props) := matchAshr op ctx | return (ctx, none)
  let some cst := matchConstantIntVal zero ctx | return (ctx, none)
  if cst.value ≠ 0 then return (ctx, none)
  some (ctx, some (#[], #[zero]))

def ashr_left_to_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite ashr_left_to_zero_local rewriter op opInBounds

def mul_left_to_zero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (zero, _rhs, _props) := matchMul op ctx | return (ctx, none)
  let some cst := matchConstantIntVal zero ctx | return (ctx, none)
  if cst.value ≠ 0 then return (ctx, none)
  some (ctx, some (#[], #[zero]))

def mul_left_to_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mul_left_to_zero_local rewriter op opInBounds

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
def srl_sra_signbitGen_local (srlDst : Riscv)
    (hSrl : Riscv.propertiesOf srlDst = RISCVImmediateProperties) (sraDst : Riscv) (width : Nat)
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, outerImm) := matchOp op ctx (.riscv srlDst) 1 | return (ctx, none)
  if (cast hSrl outerImm : RISCVImmediateProperties).value.value ≠ (width : Int) - 1 then
    return (ctx, none)
  let some sraOp := getDefiningOp operands[0]! ctx | return (ctx, none)
  let some (sraOperands, _) := matchOp sraOp ctx (.riscv sraDst) 1 | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv srlDst) #[RegisterType.mk] #[sraOperands[0]!]
      #[] #[] outerImm none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def srl_sra_signbitGen (srlDst : Riscv)
    (hSrl : Riscv.propertiesOf srlDst = RISCVImmediateProperties) (sraDst : Riscv) (width : Nat)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (srl_sra_signbitGen_local srlDst hSrl sraDst width) rewriter op
    opInBounds

def srl_sra_signbit := srl_sra_signbitGen .srli rfl .srai 64

/-- `i32` analogue of `srl_sra_signbit`: `riscv.srliw 31 (riscv.sraiw _ x) ->
    riscv.srliw 31 x`. -/
def srlw_sraw_signbit := srl_sra_signbitGen .srliw rfl .sraiw 32

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
private def drop_slli_srli_boolGen_local (boolDst : Riscv) (arity : Nat) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, outerImm) := matchOp op ctx (.riscv .srli) 1 | return (ctx, none)
  if outerImm.value.value ≠ 63 then return (ctx, none)
  let some slliOp := getDefiningOp operands[0]! ctx | return (ctx, none)
  let some (slliOperands, innerImm) := matchOp slliOp ctx (.riscv .slli) 1 | return (ctx, none)
  if innerImm.value.value ≠ 63 then return (ctx, none)
  let some boolOp := getDefiningOp slliOperands[0]! ctx | return (ctx, none)
  let some (_, _) := matchOp boolOp ctx (.riscv boolDst) arity | return (ctx, none)
  some (ctx, some (#[], #[slliOperands[0]!]))

private def drop_slli_srli_boolGen (boolDst : Riscv) (arity : Nat) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (drop_slli_srli_boolGen_local boolDst arity) rewriter op opInBounds

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

/-- `riscv.<ext> (riscv.<ext> x) -> riscv.<ext> x` for an idempotent width
    extension `ext` (`zextw` or `sextw`): the inner op already establishes the
    high-bit pattern (bits 63:32 clear, or a copy of bit 31) that the outer one
    would, so the outer is redundant and its result forwards to the inner op.

    LLVM: `zext.w` is `add.uw rd, rs, x0` and `sext.w` is `addiw rd, rs, 0`;
    either way a redundant re-extension of an already-extended value is folded
    away generically (by `SimplifyDemandedBits`, or by sext.w removal --
    `hasAllNBitUsers` treats an outer `sext.w` as a low-32-bit user).
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L120 -/
private def drop_redundant_ext_local (ext : Riscv) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, _) := matchOp op ctx (.riscv ext) 1 | return (ctx, none)
  let outerSrc := operands[0]!
  let some innerOp := getDefiningOp outerSrc ctx | return (ctx, none)
  let some (_, _) := matchOp innerOp ctx (.riscv ext) 1 | return (ctx, none)
  some (ctx, some (#[], #[outerSrc]))

private def drop_redundant_ext (ext : Riscv) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (drop_redundant_ext_local ext) rewriter op opInBounds

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

/-- Drop `riscv.<ext>` operands (`ext` = `zextw`/`sextw`) feeding a binary op
    whose semantics use only operand bits 31:0. For these consumers the high 32
    bits of each source are ignored, and both extensions leave bits 31:0
    unchanged, so extending the source first is redundant.

    LLVM enumerates exactly which consumers demand only operand bits 31:0 in
    `hasAllNBitUsers` (RISCVOptWInstrs.cpp); for such a consumer a feeding
    `zext.w`/`sext.w` is redundant and drops out via `SimplifyDemandedBits` /
    sext.w removal.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L120 -/
private def drop_ext_binary_low_word_local (ext dst : Riscv) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, props) := matchOp op ctx (.riscv dst) 2 | return (ctx, none)
  let (lhs, lhsChanged) := stripDefiningExt ext operands[0]! ctx
  let (rhs, rhsChanged) := stripDefiningExt ext operands[1]! ctx
  if !lhsChanged && !rhsChanged then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv dst) #[RegisterType.mk] #[lhs, rhs]
      #[] #[] props none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

private def drop_ext_binary_low_word (ext dst : Riscv) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (drop_ext_binary_low_word_local ext dst) rewriter op opInBounds

/-- Drop a `riscv.<ext>` operand feeding a unary immediate op whose semantics use
    only operand bits 31:0. Same reasoning (and same LLVM `hasAllNBitUsers`
    enumeration) as `drop_ext_binary_low_word`. -/
private def drop_ext_unary_imm_low_word_local (ext dst : Riscv) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, props) := matchOp op ctx (.riscv dst) 1 | return (ctx, none)
  let (src, changed) := stripDefiningExt ext operands[0]! ctx
  if !changed then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv dst) #[RegisterType.mk] #[src]
      #[] #[] props none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

private def drop_ext_unary_imm_low_word (ext dst : Riscv) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (drop_ext_unary_imm_low_word_local ext dst) rewriter op opInBounds

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
private def drop_ext_of_bitwise_local (ext dst : Riscv) (oneOperandSuffices : Bool) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, _) := matchOp op ctx (.riscv ext) 1 | return (ctx, none)
  let inner := operands[0]!
  let some innerOp := getDefiningOp inner ctx | return (ctx, none)
  let some (innerOperands, _) := matchOp innerOp ctx (.riscv dst) 2 | return (ctx, none)
  let (_, lhsGuarded) := stripDefiningExt ext innerOperands[0]! ctx
  let (_, rhsGuarded) := stripDefiningExt ext innerOperands[1]! ctx
  let guarded := if oneOperandSuffices then lhsGuarded || rhsGuarded else lhsGuarded && rhsGuarded
  if !guarded then return (ctx, none)
  some (ctx, some (#[], #[inner]))

private def drop_ext_of_bitwise (ext dst : Riscv) (oneOperandSuffices : Bool) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (drop_ext_of_bitwise_local ext dst oneOperandSuffices) rewriter op opInBounds

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
private def drop_ext_store_local (ext store : Riscv) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (addr, val, props) := matchRiscvStore store op ctx | return (ctx, none)
  let (val, changed) := stripDefiningExt ext val ctx
  if !changed then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv store) #[] #[addr, val]
      #[] #[] props none
  some (ctx, some (#[newOp], #[]))

private def drop_ext_store (ext store : Riscv) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (drop_ext_store_local ext store) rewriter op opInBounds

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

/-- riscv.li 0 -> rv64.get_register (x0)

    Every consumer of a materialized zero uses it as a source register, and on
    RV64 the hard-wired zero register `x0` reads as 0 in any source position, so
    we can replace the result of a `riscv.li 0` with a reference to `x0` and drop
    the materialization. This removes the `li 0` wherever the constant is only fed
    into ops that can take `x0` directly (slt, sltu, branch-arg inits, ...).

    LLVM does this during isel: an `ISD::Constant` of 0 selects to a copy from
    the `X0` register rather than being materialized (commit d9906882fc61).
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVISelDAGToDAG.cpp#L1119-L1126 -/
def li_zero_to_x0_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (_, cst) := matchOp op ctx (.riscv .li) 0 | return (ctx, none)
  if cst.value.value ≠ 0 then return (ctx, none)
  /- Nothing to do for a dead `li 0`; leave it for DCE and avoid creating a dead x0. -/
  if !op.hasUses! ctx.raw then return (ctx, none)
  let (ctx, x0Op) ← WfRewriter.createOp! ctx (.rv64 .get_register)
    #[(RegisterType.mk (some 0) : TypeAttr)] #[] #[] #[] () none
  some (ctx, some (#[x0Op], #[x0Op.getResult 0]))

def li_zero_to_x0 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite li_zero_to_x0_local rewriter op opInBounds

/-- `riscv.<ext>` (`zextw`/`sextw`) of the hard-wired zero register `x0` is a
    no-op: `x0` reads as 0 in any source position (see `li_zero_to_x0`), and 0 is
    both its own zero-extension and its own sign-extension.

    LLVM: `zext.w`/`sext.w` of a value known to be `0` (the `X0` register / an
    `ISD::Constant` 0) folds away via generic known-bits.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L759 -/
private def ext_x0_local (ext : Riscv) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, _) := matchOp op ctx (.riscv ext) 1 | return (ctx, none)
  let src := operands[0]!
  let .registerType regType := (src.getType! ctx.raw).val | return (ctx, none)
  if regType.index ≠ some 0 then return (ctx, none)
  some (ctx, some (#[], #[src]))

private def ext_x0 (ext : Riscv) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (ext_x0_local ext) rewriter op opInBounds

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

/-- `riscv.zextw (riscv.li v) -> riscv.li v` when `0 ≤ v < 2^32`: `li`'s
    materialized 64-bit value (`BitVec.ofInt 64 v`) already has bits 63:32
    clear in that range, so zero-extending it again is redundant.

    LLVM: `zext.w` is `(and X, 0xffffffff)` (isel pattern in RISCVInstrInfoZb.td);
    with `X` a constant whose bits 63:32 are already clear the mask folds away
    via generic constant folding / known-bits.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L759 -/
def zextw_li_low32_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, _) := matchOp op ctx (.riscv .zextw) 1 | return (ctx, none)
  let src := operands[0]!
  let some srcOp := getDefiningOp src ctx | return (ctx, none)
  let some (_, cst) := matchOp srcOp ctx (.riscv .li) 0 | return (ctx, none)
  if cst.value.value < 0 ∨ cst.value.value ≥ 4294967296 then return (ctx, none)
  some (ctx, some (#[], #[src]))

def zextw_li_low32 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite zextw_li_low32_local rewriter op opInBounds

/-- `riscv.sextw (riscv.li v) -> riscv.li v` when `-2^31 ≤ v < 2^31`: in that
    (signed 32-bit) range `li`'s materialized value (`BitVec.ofInt 64 v`) is
    already the sign-extension of its own low 32 bits, so `sextw` is redundant.
    Note the guard differs from `zextw_li_low32`'s unsigned `[0, 2^32)`: sign
    extension is a no-op exactly on the *signed* 32-bit range (which includes
    negative immediates, e.g. `li -1`).

    LLVM: constant folding / known-bits on `sext.w` of an already-sign-extended
    32-bit constant.
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L120 -/
def sextw_li_low32_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, _) := matchOp op ctx (.riscv .sextw) 1 | return (ctx, none)
  let src := operands[0]!
  let some srcOp := getDefiningOp src ctx | return (ctx, none)
  let some (_, cst) := matchOp srcOp ctx (.riscv .li) 0 | return (ctx, none)
  if cst.value.value < -2147483648 ∨ cst.value.value ≥ 2147483648 then return (ctx, none)
  some (ctx, some (#[], #[src]))

def sextw_li_low32 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sextw_li_low32_local rewriter op opInBounds

/-- Byte- and half-word mirrors of `zextw_li_low32`/`sextw_li_low32`: a `riscv.<ext>`
    of a `riscv.li v` is redundant when `v`'s materialized value already carries
    the extension's high-bit pattern. For a zero-extension that is the *unsigned*
    range below `2^width` (bits above `width` clear); for a sign-extension the
    *signed* range `[-2^(width-1), 2^(width-1))` (bits above `width` all equal the
    sign bit). `ext`/`width` picks the op and its bit width. -/
private def ext_li_range_local (ext : Riscv) (lo hi : Int) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, _) := matchOp op ctx (.riscv ext) 1 | return (ctx, none)
  let src := operands[0]!
  let some srcOp := getDefiningOp src ctx | return (ctx, none)
  let some (_, cst) := matchOp srcOp ctx (.riscv .li) 0 | return (ctx, none)
  if cst.value.value < lo ∨ cst.value.value ≥ hi then return (ctx, none)
  some (ctx, some (#[], #[src]))

private def ext_li_range (ext : Riscv) (lo hi : Int) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite (ext_li_range_local ext lo hi) rewriter op opInBounds

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

def SubSmaxSub_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (zeroOuter, maxV, sprops) := matchSub op ctx | return (ctx, none)
  let some _ := matchConstantZero zeroOuter ctx | return (ctx, none)
  let some dMax := getDefiningOp maxV ctx | return (ctx, none)
  let some (a, subV) := matchSmax dMax ctx | return (ctx, none)
  let some dSub := getDefiningOp subV ctx | return (ctx, none)
  let some (zeroInner, a2, _) := matchSub dSub ctx | return (ctx, none)
  let some _ := matchConstantZero zeroInner ctx | return (ctx, none)
  if a2 != a then return (ctx, none)
  let .integerType aty := (a.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 aty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[a.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, sub1) ← WfRewriter.createOp! ctx (.llvm .sub) #[a.getType! ctx.raw] #[(c0.getResult 0), a]
    #[] #[] sprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__smin) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (sub1.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[c0, sub1, newOp], #[newOp.getResult 0]))

def SubSmaxSub (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite SubSmaxSub_local rewriter op opInBounds

def SubUmaxSub_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (zeroOuter, maxV, sprops) := matchSub op ctx | return (ctx, none)
  let some _ := matchConstantZero zeroOuter ctx | return (ctx, none)
  let some dMax := getDefiningOp maxV ctx | return (ctx, none)
  let some (a, subV) := matchUmax dMax ctx | return (ctx, none)
  let some dSub := getDefiningOp subV ctx | return (ctx, none)
  let some (zeroInner, a2, _) := matchSub dSub ctx | return (ctx, none)
  let some _ := matchConstantZero zeroInner ctx | return (ctx, none)
  if a2 != a then return (ctx, none)
  let .integerType aty := (a.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 aty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[a.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, sub1) ← WfRewriter.createOp! ctx (.llvm .sub) #[a.getType! ctx.raw] #[(c0.getResult 0), a]
    #[] #[] sprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__umin) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (sub1.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[c0, sub1, newOp], #[newOp.getResult 0]))

def SubUmaxSub (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite SubUmaxSub_local rewriter op opInBounds

/-! ### narrow_binop :  trunc (binop X, C) → binop (trunc X, trunc C)

  A binop matched on a constant second operand is narrowed by pushing the outer
  `trunc` onto each operand and redoing the binop at the trunc's width. The outer
  trunc's own `nsw`/`nuw` flags are reused for the operand truncations. -/

-- trunc (add X, C) → add (trunc X, trunc C)
def narrow_binop_add_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, tp) := matchTrunc op ctx | return (ctx, none)
  let some dAdd := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, cst, _ap) := matchAdd dAdd ctx | return (ctx, none)
  let some _ := matchConstantIntVal cst ctx | return (ctx, none)
  let outTy := (op.getResult 0 : ValuePtr).getType! ctx.raw
  let (ctx, tx) ← WfRewriter.createOp! ctx (.llvm .trunc) #[outTy] #[x]
    #[] #[] tp none
  let (ctx, tc) ← WfRewriter.createOp! ctx (.llvm .trunc) #[outTy] #[cst]
    #[] #[] tp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[outTy] #[(tx.getResult 0), (tc.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) none
  some (ctx, some (#[tx, tc, newOp], #[newOp.getResult 0]))

def narrow_binop_add (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite narrow_binop_add_local rewriter op opInBounds

-- trunc (sub X, C) → sub (trunc X, trunc C)
def narrow_binop_sub_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, tp) := matchTrunc op ctx | return (ctx, none)
  let some dSub := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, cst, _sp) := matchSub dSub ctx | return (ctx, none)
  let some _ := matchConstantIntVal cst ctx | return (ctx, none)
  let outTy := (op.getResult 0 : ValuePtr).getType! ctx.raw
  let (ctx, tx) ← WfRewriter.createOp! ctx (.llvm .trunc) #[outTy] #[x]
    #[] #[] tp none
  let (ctx, tc) ← WfRewriter.createOp! ctx (.llvm .trunc) #[outTy] #[cst]
    #[] #[] tp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sub) #[outTy] #[(tx.getResult 0), (tc.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) none
  some (ctx, some (#[tx, tc, newOp], #[newOp.getResult 0]))

def narrow_binop_sub (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite narrow_binop_sub_local rewriter op opInBounds

-- trunc (mul X, C) → mul (trunc X, trunc C)
def narrow_binop_mul_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, tp) := matchTrunc op ctx | return (ctx, none)
  let some dMul := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, cst, _mp) := matchMul dMul ctx | return (ctx, none)
  let some _ := matchConstantIntVal cst ctx | return (ctx, none)
  let outTy := (op.getResult 0 : ValuePtr).getType! ctx.raw
  let (ctx, tx) ← WfRewriter.createOp! ctx (.llvm .trunc) #[outTy] #[x]
    #[] #[] tp none
  let (ctx, tc) ← WfRewriter.createOp! ctx (.llvm .trunc) #[outTy] #[cst]
    #[] #[] tp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .mul) #[outTy] #[(tx.getResult 0), (tc.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) none
  some (ctx, some (#[tx, tc, newOp], #[newOp.getResult 0]))

def narrow_binop_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite narrow_binop_mul_local rewriter op opInBounds

/-! ### truncate_of_sext :  trunc (sext x) where trunc result type = x's type → x -/

def truncate_of_sext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, _tp) := matchTrunc op ctx | return (ctx, none)
  let some dS := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _sp) := matchSext dS ctx | return (ctx, none)
  if (op.getResult 0 : ValuePtr).getType! ctx.raw != x.getType! ctx.raw then return (ctx, none)
  some (ctx, some (#[], #[x]))

def truncate_of_sext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite truncate_of_sext_local rewriter op opInBounds

/-! ### zext_of_zext :  zext (zext x) → zext x -/

def zext_of_zext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, zp) := matchZext op ctx | return (ctx, none)
  let some dZ := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _) := matchZext dZ ctx | return (ctx, none)
  let outTy := (op.getResult 0 : ValuePtr).getType! ctx.raw
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .zext) #[outTy] #[x]
    #[] #[] zp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def zext_of_zext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite zext_of_zext_local rewriter op opInBounds

/-! ### sext_of_sext :  sext (sext x) → sext x -/

def sext_of_sext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (v0, sp) := matchSext op ctx | return (ctx, none)
  let some dS := getDefiningOp v0 ctx | return (ctx, none)
  let some (x, _) := matchSext dS ctx | return (ctx, none)
  let outTy := (op.getResult 0 : ValuePtr).getType! ctx.raw
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .sext) #[outTy] #[x]
    #[] #[] sp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def sext_of_sext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sext_of_sext_local rewriter op opInBounds

/-! ### sub_to_add :  (sub x, C) → (add x, -C)   (C constant) -/

def sub_to_add_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, cval, _sp) := matchSub op ctx | return (ctx, none)
  let some c := matchConstantIntVal cval ctx | return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let negC := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-c.value) xty))
  let (ctx, cn) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] negC none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, (cn.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) none
  some (ctx, some (#[cn, newOp], #[newOp.getResult 0]))

def sub_to_add (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_to_add_local rewriter op opInBounds

/-! ### sub_of_mul_const :  (sub a, (mul x, C)) → (add a, (mul x, -C))   (C constant) -/

def sub_of_mul_const_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, mulV, _sp) := matchSub op ctx | return (ctx, none)
  let some dMul := getDefiningOp mulV ctx | return (ctx, none)
  let some (x, cval, mp) := matchMul dMul ctx | return (ctx, none)
  let some c := matchConstantIntVal cval ctx | return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let negC := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (-c.value) xty))
  let (ctx, cn) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] negC none
  let (ctx, newMul) ← WfRewriter.createOp! ctx (.llvm .mul) #[x.getType! ctx.raw] #[x, (cn.getResult 0)]
    #[] #[] mp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (newMul.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) none
  some (ctx, some (#[cn, newMul, newOp], #[newOp.getResult 0]))

def sub_of_mul_const (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_of_mul_const_local rewriter op opInBounds

/-! ### select_not :  select (not c), x, y → select c, y, x -/

def select_not_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tv, fv) := matchSelect op ctx | return (ctx, none)
  let some dC := getDefiningOp cond ctx | return (ctx, none)
  let some (c, m1v, _) := matchXor dC ctx | return (ctx, none)
  let some m1 := matchConstantIntVal m1v ctx | return (ctx, none)
  if m1.value ≠ -1 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .select) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[c, fv, tv]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def select_not (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite select_not_local rewriter op opInBounds

/-! ### commute_int_constant_to_rhs :  (C op x) → (x op C)   (move constant to the right) -/

def commute_const_add_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, props) := matchAdd op ctx | return (ctx, none)
  let some _ := matchConstantIntVal lhs ctx | return (ctx, none)
  if (matchConstantIntVal rhs ctx).isSome then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[rhs, lhs]
    #[] #[] props none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def commute_const_add (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite commute_const_add_local rewriter op opInBounds

def commute_const_mul_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, props) := matchMul op ctx | return (ctx, none)
  let some _ := matchConstantIntVal lhs ctx | return (ctx, none)
  if (matchConstantIntVal rhs ctx).isSome then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .mul) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[rhs, lhs]
    #[] #[] props none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def commute_const_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite commute_const_mul_local rewriter op opInBounds

def commute_const_and_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchAnd op ctx | return (ctx, none)
  let some _ := matchConstantIntVal lhs ctx | return (ctx, none)
  if (matchConstantIntVal rhs ctx).isSome then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[rhs, lhs]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def commute_const_and (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite commute_const_and_local rewriter op opInBounds

def commute_const_or_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, props) := matchOr op ctx | return (ctx, none)
  let some _ := matchConstantIntVal lhs ctx | return (ctx, none)
  if (matchConstantIntVal rhs ctx).isSome then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .or) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[rhs, lhs]
    #[] #[] props none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def commute_const_or (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite commute_const_or_local rewriter op opInBounds

def commute_const_xor_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchXor op ctx | return (ctx, none)
  let some _ := matchConstantIntVal lhs ctx | return (ctx, none)
  if (matchConstantIntVal rhs ctx).isSome then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .xor) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[rhs, lhs]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def commute_const_xor (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite commute_const_xor_local rewriter op opInBounds

/-! ### simplify_neg_minmax :  0 - (minmax a, (0 - a)) → oppositeMinMax a, (0 - a)

  Completes the smin/umin input cases of LLVM's `simplify_neg_minmax` (rule #184);
  the smax/umax input cases are handled by `SubSmaxSub` / `SubUmaxSub`. Mirrors
  `getInverseGMinMaxOpcode`: smin → smax, umin → umax. -/

def SubSminSub_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (zeroOuter, minV, sprops) := matchSub op ctx | return (ctx, none)
  let some _ := matchConstantZero zeroOuter ctx | return (ctx, none)
  let some dMin := getDefiningOp minV ctx | return (ctx, none)
  let some (a, subV) := matchSmin dMin ctx | return (ctx, none)
  let some dSub := getDefiningOp subV ctx | return (ctx, none)
  let some (zeroInner, a2, _) := matchSub dSub ctx | return (ctx, none)
  let some _ := matchConstantZero zeroInner ctx | return (ctx, none)
  if a2 != a then return (ctx, none)
  let .integerType aty := (a.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 aty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[a.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, sub1) ← WfRewriter.createOp! ctx (.llvm .sub) #[a.getType! ctx.raw] #[(c0.getResult 0), a]
    #[] #[] sprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__smax) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (sub1.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[c0, sub1, newOp], #[newOp.getResult 0]))

def SubSminSub (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite SubSminSub_local rewriter op opInBounds

def SubUminSub_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (zeroOuter, minV, sprops) := matchSub op ctx | return (ctx, none)
  let some _ := matchConstantZero zeroOuter ctx | return (ctx, none)
  let some dMin := getDefiningOp minV ctx | return (ctx, none)
  let some (a, subV) := matchUmin dMin ctx | return (ctx, none)
  let some dSub := getDefiningOp subV ctx | return (ctx, none)
  let some (zeroInner, a2, _) := matchSub dSub ctx | return (ctx, none)
  let some _ := matchConstantZero zeroInner ctx | return (ctx, none)
  if a2 != a then return (ctx, none)
  let .integerType aty := (a.getType! ctx.raw).val | return (ctx, none)
  let z := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 aty))
  let (ctx, c0) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[a.getType! ctx.raw] #[]
    #[] #[] z none
  let (ctx, sub1) ← WfRewriter.createOp! ctx (.llvm .sub) #[a.getType! ctx.raw] #[(c0.getResult 0), a]
    #[] #[] sprops none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__umax) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[a, (sub1.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[c0, sub1, newOp], #[newOp.getResult 0]))

def SubUminSub (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite SubUminSub_local rewriter op opInBounds

/-! ### lshr_of_trunc_of_lshr :  (lshr (trunc (lshr x, C1)), C2) → trunc (lshr x, (C1 + C2))

  C1, C2 constants. The two logical right shifts compose at x's full width, then a
  single trunc narrows to the result type. -/

def lshr_of_trunc_of_lshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (truncV, c2v, _) := matchLshr op ctx | return (ctx, none)
  let some c2 := matchConstantIntVal c2v ctx | return (ctx, none)
  let some dTrunc := getDefiningOp truncV ctx | return (ctx, none)
  let some (innerLshrV, _) := matchTrunc dTrunc ctx | return (ctx, none)
  let some dInner := getDefiningOp innerLshrV ctx | return (ctx, none)
  let some (x, c1v, ip) := matchLshr dInner ctx | return (ctx, none)
  let some c1 := matchConstantIntVal c1v ctx | return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value + c2.value) xty))
  let (ctx, cf) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] folded none
  let (ctx, newLshr) ← WfRewriter.createOp! ctx (.llvm .lshr) #[x.getType! ctx.raw] #[x, (cf.getResult 0)]
    #[] #[] ip none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .trunc) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[(newLshr.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) none
  some (ctx, some (#[cf, newLshr, newOp], #[newOp.getResult 0]))

def lshr_of_trunc_of_lshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite lshr_of_trunc_of_lshr_local rewriter op opInBounds

/-! ### funnel_shift_{right,left}_zero :  fshr x, y, 0 → y ,  fshl x, y, 0 → x -/

def funnel_shift_right_zero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (_x, y, amt) := matchFshr op ctx | return (ctx, none)
  let some c := matchConstantIntVal amt ctx | return (ctx, none)
  if c.value ≠ 0 then return (ctx, none)
  some (ctx, some (#[], #[y]))

def funnel_shift_right_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite funnel_shift_right_zero_local rewriter op opInBounds

def funnel_shift_left_zero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, _y, amt) := matchFshl op ctx | return (ctx, none)
  let some c := matchConstantIntVal amt ctx | return (ctx, none)
  if c.value ≠ 0 then return (ctx, none)
  some (ctx, some (#[], #[x]))

def funnel_shift_left_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite funnel_shift_left_zero_local rewriter op opInBounds

/-! ### canonicalize_icmp :  (icmp pred C, x) → (icmp swappedPred x, C)

  Moves a constant left operand of an icmp to the right, flipping the predicate to
  its swapped form. Mirrors LLVM's `matchCanonicalizeICmp`: fires only when the LHS
  is a constant and the RHS is not (so it does not oscillate). -/

def canonicalize_icmp_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, ip) := matchIcmp op ctx | return (ctx, none)
  let some _ := matchConstantIntVal lhs ctx | return (ctx, none)
  if (matchConstantIntVal rhs ctx).isSome then return (ctx, none)
  let swapped : Data.LLVM.IntPred := match ip.predicate with
    | .slt => .sgt | .sgt => .slt | .sle => .sge | .sge => .sle
    | .ult => .ugt | .ugt => .ult | .ule => .uge | .uge => .ule
    | p => p
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[rhs, lhs]
    #[] #[] (IcmpProperties.mk swapped) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def canonicalize_icmp (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite canonicalize_icmp_local rewriter op opInBounds

/-! ### bitreverse_shl / bitreverse_lshr

  `bitreverse(shl(bitreverse x), y) → lshr x, y` and the mirror
  `bitreverse(lshr(bitreverse x), y) → shl x, y`. Reversing, shifting one way,
  and reversing again is equivalent to a single shift the other way. -/

def bitreverse_shl_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some rev := matchBitreverse op ctx | return (ctx, none)
  let some dShl := getDefiningOp rev ctx | return (ctx, none)
  let some (inner, y, _) := matchShl dShl ctx | return (ctx, none)
  let some dInner := getDefiningOp inner ctx | return (ctx, none)
  let some x := matchBitreverse dInner ctx | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .lshr) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y]
    #[] #[] (ExactProperties.mk false) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def bitreverse_shl (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite bitreverse_shl_local rewriter op opInBounds

def bitreverse_lshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some rev := matchBitreverse op ctx | return (ctx, none)
  let some dLshr := getDefiningOp rev ctx | return (ctx, none)
  let some (inner, y, _) := matchLshr dLshr ctx | return (ctx, none)
  let some dInner := getDefiningOp inner ctx | return (ctx, none)
  let some x := matchBitreverse dInner ctx | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .shl) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y]
    #[] #[] (NswNuwProperties.mk false false) none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def bitreverse_lshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite bitreverse_lshr_local rewriter op opInBounds

/-! ### udiv_by_pow2 / mul_to_shl / urem_pow2_to_mask

  Strength reductions against a power-of-two constant:
    `udiv x, 2^k → lshr x, k`,  `mul x, 2^k → shl x, k`,
    `urem x, 2^k → and x, (2^k − 1)`. -/

def udiv_by_pow2_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, yv, _) := matchUdiv op ctx | return (ctx, none)
  let some k := isConstantPowerOfTwo yv ctx | return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let kConst := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (k : Int) xty))
  let (ctx, ck) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] kConst none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .lshr) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, (ck.getResult 0)]
    #[] #[] (ExactProperties.mk false) none
  some (ctx, some (#[ck, newOp], #[newOp.getResult 0]))

def udiv_by_pow2 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite udiv_by_pow2_local rewriter op opInBounds

def mul_to_shl_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, yv, mp) := matchMul op ctx | return (ctx, none)
  let some k := isConstantPowerOfTwo yv ctx | return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let kConst := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (k : Int) xty))
  let (ctx, ck) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] kConst none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .shl) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, (ck.getResult 0)]
    #[] #[] mp none
  some (ctx, some (#[ck, newOp], #[newOp.getResult 0]))

def mul_to_shl (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mul_to_shl_local rewriter op opInBounds

def urem_pow2_to_mask_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, yv, _) := matchUrem op ctx | return (ctx, none)
  let some k := isConstantPowerOfTwo yv ctx | return (ctx, none)
  let .integerType xty := (x.getType! ctx.raw).val | return (ctx, none)
  let mask : Int := (2 ^ k : Int) - 1
  let maskConst := LLVMConstantProperties.mk (.integer (IntegerAttr.mk mask xty))
  let (ctx, cm) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[x.getType! ctx.raw] #[]
    #[] #[] maskConst none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, (cm.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[cm, newOp], #[newOp.getResult 0]))

def urem_pow2_to_mask (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite urem_pow2_to_mask_local rewriter op opInBounds

/-! ### funnel_shift_overshift :  fshl/fshr x, y, C → fshl/fshr x, y, (C % bw)   (C ≥ bw)

  A funnel shift amount is taken modulo the bit-width, so an over-large constant
  amount is reduced to its residue. -/

def funnel_shift_overshift_l_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, y, amt) := matchFshl op ctx | return (ctx, none)
  let some c := matchConstantIntVal amt ctx | return (ctx, none)
  let .integerType aty := (amt.getType! ctx.raw).val | return (ctx, none)
  let bw : Int := (aty.bitwidth : Int)
  if c.value < bw then return (ctx, none)
  let newAmt := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c.value % bw) aty))
  let (ctx, cn) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[amt.getType! ctx.raw] #[]
    #[] #[] newAmt none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__fshl) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y, (cn.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[cn, newOp], #[newOp.getResult 0]))

def funnel_shift_overshift_l (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite funnel_shift_overshift_l_local rewriter op opInBounds

def funnel_shift_overshift_r_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (x, y, amt) := matchFshr op ctx | return (ctx, none)
  let some c := matchConstantIntVal amt ctx | return (ctx, none)
  let .integerType aty := (amt.getType! ctx.raw).val | return (ctx, none)
  let bw : Int := (aty.bitwidth : Int)
  if c.value < bw then return (ctx, none)
  let newAmt := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c.value % bw) aty))
  let (ctx, cn) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[amt.getType! ctx.raw] #[]
    #[] #[] newAmt none
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .intr__fshr) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x, y, (cn.getResult 0)]
    #[] #[] () none
  some (ctx, some (#[cn, newOp], #[newOp.getResult 0]))

def funnel_shift_overshift_r (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite funnel_shift_overshift_r_local rewriter op opInBounds

/-! ### funnel_shift_or_shift_to_funnel_shift_{left,right}

  `(fshl x, z, y) | (shl x, y) → fshl x, z, y` and the mirror
  `(fshr z, x, y) | (lshr x, y) → fshr z, x, y`. The plain shift is subsumed by
  the funnel shift that already produces the wanted bits, so the OR collapses to
  the existing funnel-shift value. G_OR is commutative: both operand orders are
  handled. -/

def funnel_shift_or_shift_to_funnel_shift_left_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (o0, o1, _) := matchOr op ctx | return (ctx, none)
  -- Try (fshl = o0, shl = o1) then (fshl = o1, shl = o0).
  let tryOrder (fshlV shlV : ValuePtr) : Option ValuePtr := do
    let some dFshl := getDefiningOp fshlV ctx | none
    let some (fx, _fz, fy) := matchFshl dFshl ctx | none
    let some dShl := getDefiningOp shlV ctx | none
    let some (sx, sy, _) := matchShl dShl ctx | none
    guard (fx = sx ∧ fy = sy)
    some fshlV
  let some keep := (tryOrder o0 o1).orElse (fun _ => tryOrder o1 o0) | return (ctx, none)
  some (ctx, some (#[], #[keep]))

def funnel_shift_or_shift_to_funnel_shift_left (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite funnel_shift_or_shift_to_funnel_shift_left_local rewriter op opInBounds

def funnel_shift_or_shift_to_funnel_shift_right_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (o0, o1, _) := matchOr op ctx | return (ctx, none)
  -- Try (fshr = o0, lshr = o1) then (fshr = o1, lshr = o0).
  let tryOrder (fshrV lshrV : ValuePtr) : Option ValuePtr := do
    let some dFshr := getDefiningOp fshrV ctx | none
    let some (_fz, fx, fy) := matchFshr dFshr ctx | none
    let some dLshr := getDefiningOp lshrV ctx | none
    let some (sx, sy, _) := matchLshr dLshr ctx | none
    guard (fx = sx ∧ fy = sy)
    some fshrV
  let some keep := (tryOrder o0 o1).orElse (fun _ => tryOrder o1 o0) | return (ctx, none)
  some (ctx, some (#[], #[keep]))

def funnel_shift_or_shift_to_funnel_shift_right (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite funnel_shift_or_shift_to_funnel_shift_right_local rewriter op opInBounds

/-! ### constant_fold_binop :  binop(C1, C2) → C

  Both operands constant: evaluate the binop at compile time and materialize the
  single result constant. Division/remainder by zero is left un-folded. -/

def constant_fold_binop_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let opType := op.getOpType! ctx.raw
  let operands := op.getOperands! ctx.raw
  if operands.size ≠ 2 then return (ctx, none)
  let some c1 := matchConstantIntVal operands[0]! ctx | return (ctx, none)
  let some c2 := matchConstantIntVal operands[1]! ctx | return (ctx, none)
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
  let some result := folded | return (ctx, none)
  let .integerType rty := ((op.getResult 0 : ValuePtr).getType! ctx.raw).val | return (ctx, none)
  let foldedProps := LLVMConstantProperties.mk (.integer (IntegerAttr.mk result rty))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[]
    #[] #[] foldedProps none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def constant_fold_binop (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite constant_fold_binop_local rewriter op opInBounds

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
