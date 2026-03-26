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
  let (rewriter, newOp) ← rewriter.createOp .llvm_add #[lhs.getType! rewriter.ctx] #[lhs, lhs]
    #[] #[] properties (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry

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
  let .integerType type := (lhs.getType! rewriter.ctx).val
    | return rewriter
  let cstProp := LLVMConstantProperties.mk (IntegerAttr.mk 0 type)
  let (rewriter, newOp) ← rewriter.createOp .llvm_constant #[lhs.getType! rewriter.ctx] #[]
    #[] #[] cstProp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry

set_option warn.sorry false in
def InstCombinePass.impl (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed }) (op : OperationPtr)
    (_ : op.InBounds ctx.val) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do
  let pattern := RewritePattern.GreddyRewritePattern #[mulITwoToAddi, mulIZeroToCst]
  match RewritePattern.applyInContext pattern ctx ctx.property.inBounds with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ⟨ctx, sorry⟩

public def InstCombinePass : Pass OpCode :=
  { name := "instcombine"
    description :=
      "Combine instructions into more efficient forms, e.g., fold constants or simplify llvmmetic."
    run := InstCombinePass.impl }
