import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-!
  #Instcombine pass

  This file contains a (very) partial implementation of the instcombine pass, which performs
  simple peephole optimizations on the IR, such as folding constants or simplifying arithmetic.
-/

/-! ## Pattern Rewrites -/

set_option warn.sorry false in
/-- Rewrites `x * 2` to `x + x`. -/
def mulITwoToAddi (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, properties) := matchMuli op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 2 then
    return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[lhs.getType! rewriter.ctx.raw] #[lhs, lhs]
    #[] #[] properties (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x * 0` to `0`. -/
def mulIZeroToCst (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, properties) := matchMuli op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 0 then
    return rewriter
  let .integerType type := (lhs.getType! rewriter.ctx.raw).val
    | return rewriter
  let cstProp := LLVMConstantProperties.mk (IntegerAttr.mk 0 type)
  let (rewriter, newOp) ← rewriter.createOp (.llvm .mlir__constant) #[lhs.getType! rewriter.ctx.raw] #[]
    #[] #[] cstProp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x + 0` to `x`. -/
def addiZeroToX (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchAddi op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 0 then
    return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) lhs sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x * 1` to `x`. -/
def mulIOneToX (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchMuli op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 1 then
    return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) lhs sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x - 0` to `x`. -/
def subiZeroToX (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchSubi op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 0 then
    return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) lhs sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x - x` to `0`. -/
def subiSelfToZero (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchSubi op rewriter.ctx
    | return rewriter
  if lhs ≠ rhs then
    return rewriter
  let .integerType type := (lhs.getType! rewriter.ctx.raw).val
    | return rewriter
  let cstProp := LLVMConstantProperties.mk (IntegerAttr.mk 0 type)
  let (rewriter, newOp) ← rewriter.createOp (.llvm .mlir__constant) #[lhs.getType! rewriter.ctx.raw] #[]
    #[] #[] cstProp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x & x` to `x`. -/
def andiSelfToX (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchAndi op rewriter.ctx
    | return rewriter
  if lhs ≠ rhs then
    return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) lhs sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x & 0` to `0`. -/
def andiZeroToZero (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchAndi op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 0 then
    return rewriter
  let .integerType type := (lhs.getType! rewriter.ctx.raw).val
    | return rewriter
  let cstProp := LLVMConstantProperties.mk (IntegerAttr.mk 0 type)
  let (rewriter, newOp) ← rewriter.createOp (.llvm .mlir__constant) #[lhs.getType! rewriter.ctx.raw] #[]
    #[] #[] cstProp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x | 0` to `x`. -/
def oriZeroToX (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchOri op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 0 then
    return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) lhs sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x | x` to `x`. -/
def oriSelfToX (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchOri op rewriter.ctx
    | return rewriter
  if lhs ≠ rhs then
    return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) lhs sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x ^ 0` to `x`. -/
def xoriZeroToX (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchXori op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 0 then
    return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) lhs sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x ^ x` to `0`. -/
def xoriSelfToZero (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchXori op rewriter.ctx
    | return rewriter
  if lhs ≠ rhs then
    return rewriter
  let .integerType type := (lhs.getType! rewriter.ctx.raw).val
    | return rewriter
  let cstProp := LLVMConstantProperties.mk (IntegerAttr.mk 0 type)
  let (rewriter, newOp) ← rewriter.createOp (.llvm .mlir__constant) #[lhs.getType! rewriter.ctx.raw] #[]
    #[] #[] cstProp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-- Match `xor X, -1` (the canonical "not X"), returning `X`. -/
def matchNot (val : ValuePtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let .opResult opResultPtr := val | none
  let op := opResultPtr.op
  let (lhs, rhs) ← matchXori op ctx
  let cst ← matchConstantVal rhs ctx
  guard (cst.value = -1)
  return lhs

set_option warn.sorry false in
/-- Rewrites `~~x` to `x`. -/
def notNotToX (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some outerNotted := matchNot (op.getResult 0) rewriter.ctx
    | return rewriter
  let some inner := matchNot outerNotted rewriter.ctx
    | return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) inner sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `~(~a & ~b)` to `a | b` (DeMorgan). -/
/- TODO: the precondition should be strengthened by some hasOneUse() checks -/
def deMorganAndToOr (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some andVal := matchNot (op.getResult 0) rewriter.ctx
    | return rewriter
  let .opResult andResPtr := andVal
    | return rewriter
  let some (andL, andR) := matchAndi andResPtr.op rewriter.ctx
    | return rewriter
  let some a := matchNot andL rewriter.ctx
    | return rewriter
  let some b := matchNot andR rewriter.ctx
    | return rewriter
  let resultType := a.getType! rewriter.ctx.raw
  let orProps : DisjointProperties := { disjoint := false }
  let (rewriter, newOp) ← rewriter.createOp (.llvm .or) #[resultType] #[a, b]
    #[] #[] orProps (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `~(~a | ~b)` to `a & b` (DeMorgan). -/
/- TODO: the precondition should be strengthened by some hasOneUse() checks -/
def deMorganOrToAnd (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some orVal := matchNot (op.getResult 0) rewriter.ctx
    | return rewriter
  let .opResult orResPtr := orVal
    | return rewriter
  let some (orL, orR, _) := matchOri orResPtr.op rewriter.ctx
    | return rewriter
  let some a := matchNot orL rewriter.ctx
    | return rewriter
  let some b := matchNot orR rewriter.ctx
    | return rewriter
  let resultType := a.getType! rewriter.ctx.raw
  let (rewriter, newOp) ← rewriter.createOp (.llvm .and) #[resultType] #[a, b]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

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
