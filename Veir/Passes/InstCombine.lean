module

public import Veir.Pass
import Veir.PatternRewriter.Basic
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
  let some (lhs, rhs, properties) := matchMuli op ctx
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx
    | return (ctx, none)
  if cst.value ≠ 2 then
    return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .add) #[lhs.getType! ctx.raw] #[lhs, lhs]
    #[] #[] properties none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def mulITwoToAddi (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mulITwoToAddi_local rewriter op opInBounds

/-- Rewrites `x * 0` to `0`. -/
def mulIZeroToCst_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchMuli op ctx
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx
    | return (ctx, none)
  if cst.value ≠ 0 then
    return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 type))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def mulIZeroToCst (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mulIZeroToCst_local rewriter op opInBounds

/-- Rewrites `x + 0` to `x`. -/
def addiZeroToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchAddi op ctx
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx
    | return (ctx, none)
  if cst.value ≠ 0 then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def addiZeroToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite addiZeroToX_local rewriter op opInBounds

/-- Rewrites `x * 1` to `x`. -/
def mulIOneToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchMuli op ctx
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx
    | return (ctx, none)
  if cst.value ≠ 1 then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def mulIOneToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mulIOneToX_local rewriter op opInBounds

/-- Rewrites `x - 0` to `x`. -/
def subiZeroToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchSubi op ctx
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx
    | return (ctx, none)
  if cst.value ≠ 0 then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def subiZeroToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite subiZeroToX_local rewriter op opInBounds

/-- Rewrites `x - x` to `0`. -/
def subiSelfToZero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchSubi op ctx
    | return (ctx, none)
  if lhs ≠ rhs then
    return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 type))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def subiSelfToZero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite subiSelfToZero_local rewriter op opInBounds

/-- Rewrites `x & x` to `x`. -/
def andiSelfToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchAndi op ctx
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
  let some (lhs, rhs) := matchAndi op ctx
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx
    | return (ctx, none)
  if cst.value ≠ 0 then
    return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 type))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def andiZeroToZero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite andiZeroToZero_local rewriter op opInBounds

/-- Rewrites `x | 0` to `x`. -/
def oriZeroToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchOri op ctx
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx
    | return (ctx, none)
  if cst.value ≠ 0 then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def oriZeroToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite oriZeroToX_local rewriter op opInBounds

/-- Rewrites `x | x` to `x`. -/
def oriSelfToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchOri op ctx
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
  let some (lhs, rhs) := matchXori op ctx
    | return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx
    | return (ctx, none)
  if cst.value ≠ 0 then
    return (ctx, none)
  some (ctx, some (#[], #[lhs]))

def xoriZeroToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite xoriZeroToX_local rewriter op opInBounds

/-- Rewrites `x ^ x` to `0`. -/
def xoriSelfToZero_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchXori op ctx
    | return (ctx, none)
  if lhs ≠ rhs then
    return (ctx, none)
  let .integerType type := (lhs.getType! ctx.raw).val
    | return (ctx, none)
  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 type))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .mlir__constant) #[lhs.getType! ctx.raw] #[]
    #[] #[] cstProp none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def xoriSelfToZero (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite xoriSelfToZero_local rewriter op opInBounds

/-- Rewrites `~~x` to `x`. -/
def notNotToX_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some outerNotted := matchNot (op.getResult 0) ctx
    | return (ctx, none)
  let some inner := matchNot outerNotted ctx
    | return (ctx, none)
  some (ctx, some (#[], #[inner]))

def notNotToX (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite notNotToX_local rewriter op opInBounds

/-- Rewrites `~(~a & ~b)` to `a | b` (DeMorgan). -/
/- TODO: the precondition should be strengthened by some hasOneUse() checks -/
def deMorganAndToOr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some andVal := matchNot (op.getResult 0) ctx
    | return (ctx, none)
  let .opResult andResPtr := andVal
    | return (ctx, none)
  let some (andL, andR) := matchAndi andResPtr.op ctx
    | return (ctx, none)
  let some a := matchNot andL ctx
    | return (ctx, none)
  let some b := matchNot andR ctx
    | return (ctx, none)
  let resultType := a.getType! ctx.raw
  let orProps : DisjointProperties := { disjoint := false }
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .or) #[resultType] #[a, b]
    #[] #[] orProps none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def deMorganAndToOr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite deMorganAndToOr_local rewriter op opInBounds

/-- Rewrites `~(~a | ~b)` to `a & b` (DeMorgan). -/
/- TODO: the precondition should be strengthened by some hasOneUse() checks -/
def deMorganOrToAnd_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some orVal := matchNot (op.getResult 0) ctx
    | return (ctx, none)
  let .opResult orResPtr := orVal
    | return (ctx, none)
  let some (orL, orR, _) := matchOri orResPtr.op ctx
    | return (ctx, none)
  let some a := matchNot orL ctx
    | return (ctx, none)
  let some b := matchNot orR ctx
    | return (ctx, none)
  let resultType := a.getType! ctx.raw
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.llvm .and) #[resultType] #[a, b]
    #[] #[] () none
  some (ctx, some (#[newOp], #[newOp.getResult 0]))

def deMorganOrToAnd (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite deMorganOrToAnd_local rewriter op opInBounds

def InstCombinePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    mulITwoToAddi, mulIZeroToCst, mulIOneToX,
    addiZeroToX,
    subiZeroToX, subiSelfToZero,
    andiSelfToX, andiZeroToZero,
    oriZeroToX, oriSelfToX,
    xoriZeroToX, xoriSelfToZero,
    notNotToX, deMorganAndToOr, deMorganOrToAnd
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def InstCombinePass : Pass OpCode :=
  { name := "instcombine"
    description :=
      "Combine instructions into more efficient forms, e.g., fold constants or simplify llvmmetic."
    run := InstCombinePass.impl }
