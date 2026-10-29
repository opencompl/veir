module

public import Veir.Pass
import Veir.PatternRewriter.Driver
public import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-!
  #Instcombine pass

  This file contains a (very) partial implementation of the instcombine pass, which performs
  simple peephole optimizations on the IR, such as folding constants or simplifying arithmetic.
-/

/-! ## Pattern Rewrites -/

/-- Rewrites `x * 2` to `x + x`. -/
def mulITwoToAddi_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, properties) := matchMuli op ctx.raw
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx.raw
    | return (ctx, none)
  if cst ≠ 2 then
    return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.add #[lhs.getType! ctx.raw] #[lhs, lhs]
    #[] #[] properties none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def mulITwoToAddi (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mulITwoToAddi_local rewriter op opInBounds

/-- Rewrites `x * 0` to `0`. -/
def mulIZeroToCst_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchMuli op ctx.raw
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx.raw
    | return (ctx, none)
  if cst ≠ 0 then
    return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 type))
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.mlir__constant #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def mulIZeroToCst (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mulIZeroToCst_local rewriter op opInBounds

/-- Rewrites `x * 1` to `x`. -/
def mulIOneToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchMuli op ctx.raw
    | return (ctx, none)
  if !isConstantOne rhs ctx.raw then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def mulIOneToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mulIOneToX_local rewriter op opInBounds

/-- Rewrites `x - 0` to `x`. -/
def subiZeroToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchSubi op ctx.raw
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx.raw
    | return (ctx, none)
  if cst ≠ 0 then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def subiZeroToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite subiZeroToX_local rewriter op opInBounds

/-- Rewrites `x - x` to `0`. -/
def subiSelfToZero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchSubi op ctx.raw
    | return (ctx, none)
  if lhs ≠ rhs then
    return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 type))
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.mlir__constant #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def subiSelfToZero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite subiSelfToZero_local rewriter op opInBounds

/-- Rewrites `x & x` to `x`. -/
def andiSelfToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchAndi op ctx.raw
    | return (ctx, none)
  if lhs ≠ rhs then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def andiSelfToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite andiSelfToX_local rewriter op opInBounds

/-- Rewrites `x & 0` to `0`. -/
def andiZeroToZero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchAndi op ctx.raw
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx.raw
    | return (ctx, none)
  if cst ≠ 0 then
    return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 type))
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.mlir__constant #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def andiZeroToZero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite andiZeroToZero_local rewriter op opInBounds

/-- Rewrites `x | 0` to `x`. -/
def oriZeroToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchOri op ctx.raw
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx.raw
    | return (ctx, none)
  if cst ≠ 0 then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def oriZeroToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite oriZeroToX_local rewriter op opInBounds

/-- Rewrites `x | x` to `x`. -/
def oriSelfToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchOri op ctx.raw
    | return (ctx, none)
  if lhs ≠ rhs then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def oriSelfToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite oriSelfToX_local rewriter op opInBounds

/-- Rewrites `x ^ 0` to `x`. -/
def xoriZeroToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchXori op ctx.raw
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx.raw
    | return (ctx, none)
  if cst ≠ 0 then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def xoriZeroToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite xoriZeroToX_local rewriter op opInBounds

/-- Rewrites `x ^ x` to `0`. -/
def xoriSelfToZero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchXori op ctx.raw
    | return (ctx, none)
  if lhs ≠ rhs then
    return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 type))
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.mlir__constant #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def xoriSelfToZero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite xoriSelfToZero_local rewriter op opInBounds

/-- Rewrites `~~x` to `x`. -/
def notNotToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some outerNotted := matchNot (op.getResult 0) ctx.raw
    | return (ctx, none)
  let some inner := matchNot outerNotted ctx.raw
    | return (ctx, none)
  some (ctx, some (#[], #[inner]))

def notNotToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite notNotToX_local rewriter op opInBounds

/-- Rewrites `~(~a & ~b)` to `a | b` (DeMorgan). -/
/- TODO: the precondition should be strengthened by some hasOneUse() checks -/
def deMorganAndToOr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some andVal := matchNot (op.getResult 0) ctx.raw
    | return (ctx, none)
  let .opResult andResPtr := andVal
    | return (ctx, none)
  let some (andL, andR) := matchAndi andResPtr.op ctx.raw
    | return (ctx, none)
  let some a := matchNot andL ctx.raw
    | return (ctx, none)
  let some b := matchNot andR ctx.raw
    | return (ctx, none)
  let resultType := a.getType! ctx.raw
  let orProps : DisjointProperties := { disjoint := false }
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.or #[resultType] #[a, b]
    #[] #[] orProps none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def deMorganAndToOr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite deMorganAndToOr_local rewriter op opInBounds

/-- Rewrites `~(~a | ~b)` to `a & b` (DeMorgan). -/
/- TODO: the precondition should be strengthened by some hasOneUse() checks -/
def deMorganOrToAnd_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some orVal := matchNot (op.getResult 0) ctx.raw
    | return (ctx, none)
  let .opResult orResPtr := orVal
    | return (ctx, none)
  let some (orL, orR, _) := matchOri orResPtr.op ctx.raw
    | return (ctx, none)
  let some a := matchNot orL ctx.raw
    | return (ctx, none)
  let some b := matchNot orR ctx.raw
    | return (ctx, none)
  let resultType := a.getType! ctx.raw
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.and #[resultType] #[a, b]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def deMorganOrToAnd (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite deMorganOrToAnd_local rewriter op opInBounds

/-- Rewrites `x * -1` to `0 - x`. Both overflow as signed integers exactly when `x` is the minimum
    signed value, so `nsw` carries over; `nuw` does not. -/
def mulNegOneToNeg_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, properties) := matchMul op ctx.raw
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx.raw
    | return (ctx, none)
  if cst ≠ -1 then
    return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 type))
  let (ctx, zero) ← WfRewriter.createOp! ctx Llvm.mlir__constant #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.sub #[lhs.getType! ctx.raw]
    #[zero.getResult 0, lhs] #[] #[] ({ nsw := properties.nsw, nuw := false } : NswNuwProperties)
    none
  some (ctx, some (#[zero, newOp], #[newOp.getResult 0]))

def mulNegOneToNeg (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mulNegOneToNeg_local rewriter op opInBounds

/-- Rewrites `x urem 2^k` to `x & (2^k - 1)`. -/
def uremPow2ToAnd_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchUrem op ctx.raw
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx.raw
    | return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  -- The divisor as an unsigned integer.
  let divisor := (BitVec.ofInt type.bitwidth cst).toNat
  if divisor = 0 || divisor &&& (divisor - 1) ≠ 0 then
    return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (divisor - 1) type))
  let (ctx, mask) ← WfRewriter.createOp! ctx Llvm.mlir__constant #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.and #[lhs.getType! ctx.raw]
    #[lhs, mask.getResult 0] #[] #[] () none
  some (ctx, some (#[mask, newOp], #[newOp.getResult 0]))

def uremPow2ToAnd (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite uremPow2ToAnd_local rewriter op opInBounds

/-- Rewrites `sext (sext x)` to `sext x`. -/
def sextSextToSext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (inner, _) := matchSext op ctx.raw
    | return (ctx, none)
  let some innerOp := inner.definingOp?
    | return (ctx, none)
  let some (x, _) := matchSext innerOp ctx.raw
    | return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx Llvm.sext
    #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[x] #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def sextSextToSext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sextSextToSext_local rewriter op opInBounds

/-- Rewrites `bitreverse (bitreverse x)` to `x`. -/
def bitreverseBitreverseToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some inner := matchBitreverse op ctx.raw
    | return (ctx, none)
  let some innerOp := inner.definingOp?
    | return (ctx, none)
  let some x := matchBitreverse innerOp ctx.raw
    | return (ctx, none)
  some (ctx, some (#[], #[x]))

def bitreverseBitreverseToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite bitreverseBitreverseToX_local rewriter op opInBounds

/-- Rewrites `minmax x, x` to `x`, for `minmax` ∈ {`smax`, `smin`, `umax`, `umin`}. -/
def minMaxSelfToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := (matchSmax op ctx.raw).orElse fun _ =>
      (matchSmin op ctx.raw).orElse fun _ =>
      (matchUmax op ctx.raw).orElse fun _ => matchUmin op ctx.raw
    | return (ctx, none)
  if lhs ≠ rhs then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def minMaxSelfToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite minMaxSelfToX_local rewriter op opInBounds

def InstCombinePass.impl (fold : Bool) (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    mulITwoToAddi, mulIZeroToCst, mulIOneToX,
    subiZeroToX, subiSelfToZero,
    andiSelfToX, andiZeroToZero,
    oriZeroToX, oriSelfToX,
    xoriZeroToX, xoriSelfToZero,
    notNotToX, deMorganAndToOr, deMorganOrToAnd,
    mulNegOneToNeg, uremPow2ToAnd, sextSextToSext, bitreverseBitreverseToX, minMaxSelfToX
  ]
  match RewritePattern.applyInContext pattern ctx (fold := fold) with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def InstCombinePass : Pass OpCode :=
  { name := "instcombine"
    description :=
      "Combine instructions into more efficient forms, e.g., fold constants or simplify llvmmetic."
    run := fun options => InstCombinePass.impl options.fold }
