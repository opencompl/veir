module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.Interfaces.ConstantLikeInterfaces
import Veir.Passes.Matching

namespace Veir

/-!
  # Canonicalize pass

  Rewrites operations into canonical forms, including moving constants
  to the right side of commutative operations and reducing modular
  constants to their canonical representatives.
-/

def canonicalizeModArithConstant (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (_, props) := matchOp op rewriter.ctx.raw Mod_Arith.constant 0
    | return rewriter
  let resultType := (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw
  let .modArithType modArithType := resultType.val
    | return rewriter
  let canonicalValue := props.value.value % modArithType.modulus.value
  if canonicalValue = props.value.value then return rewriter
  let canonicalProps : ModArithConstantProperties :=
    { value := { props.value with value := canonicalValue } }
  return rewriter.setProperties! op Mod_Arith.constant canonicalProps

def commutativeConstantRHS (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let opType := op.getOpType! rewriter.ctx.raw
  if ¬ opType.isCommutative then return rewriter
  let operands := op.getOperands! rewriter.ctx.raw
  /- Stable partition: non-constant operands first, then the constants. -/
  let (nonConsts, consts) := operands.partition (!·.isConstantLike rewriter.ctx.raw)
  let reordered := nonConsts ++ consts
  if reordered == operands then return rewriter
  let resultTypes := op.getResultTypes! rewriter.ctx.raw
  let properties := op.getProperties! rewriter.ctx.raw opType
  let (rewriter, newOp) ← rewriter.createOp! opType resultTypes reordered
    #[] #[] properties (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ## Pass implementation -/

def CanonicalizePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    canonicalizeModArithConstant,
    commutativeConstantRHS
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying canonicalization patterns"
  | some ctx => pure ctx

public def CanonicalizePass : Pass OpCode :=
  { name := "canonicalize"
    description := "Rewrite operations into a canonical form."
    run := fun _ => CanonicalizePass.impl }

end Veir
