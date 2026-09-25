module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis
import Veir.Interfaces.FoldInterfaces
import Veir.Passes.Matching

namespace Veir

/-!
  # Canonicalize pass

  Rewrites operations into canonical forms, including propagating constants,
  folding operations, moving constants to the right side of commutative operations,
  and reducing modular constants to their canonical representatives.
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
  let reordered :=
    if operands.size = 2 then
      let lhs := operands[0]!
      let rhs := operands[1]!
      if lhs.isConstantLike rewriter.ctx.raw && !rhs.isConstantLike rewriter.ctx.raw then
        #[rhs, lhs]
      else
        operands
    else
      /- Stable partition: non-constant operands first, then the constants. -/
      let (nonConsts, consts) := operands.partition (!·.isConstantLike rewriter.ctx.raw)
      nonConsts ++ consts
  if reordered == operands then return rewriter
  let resultTypes := op.getResultTypes! rewriter.ctx.raw
  let properties := op.getProperties! rewriter.ctx.raw opType
  let (rewriter, newOp) ← rewriter.createOp! opType resultTypes reordered
    #[] #[] properties (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ## Pass implementation -/

/-- Replace a used SSA value with the constant found by the analysis, if its
    recorded dialect can materialize it. Existing constants need no replacement. -/
private def replaceKnownConstant (rewriter : PatternRewriter OpCode)
    (facts : DataFlowContext) (value : ValuePtr) (ip : InsertPoint) :
    Option (PatternRewriter OpCode) := do
  if (value.getFirstUse! rewriter.ctx.raw).isNone || value.isConstantLike rewriter.ctx.raw then
    return rewriter
  let some fact := facts.getFact? .sparseConstant (.ValuePtr value) | return rewriter
  let .constant constant := fact.payload.latticeElement | return rewriter
  let some opCode := fact.payload.metadata | return rewriter
  let type := value.getType! rewriter.ctx.raw
  let some ⟨constantOpCode, properties⟩ := opCode.materializeConstant constant type
    | return rewriter
  let (rewriter, constantOp) ← rewriter.createOp! constantOpCode #[type]
    #[] #[] #[] properties (some ip)
  return rewriter.replaceValue! value (constantOp.getResult 0)

/-- Solve once on the original IR, then materialize the facts. Only values with
    facts from the rooted analysis are rewritten. Leave dead producers for the
    greedy folding driver, and never consult these facts after folding. -/
private def propagateConstants (ctx : WfIRContext OpCode) (root : OperationPtr) :
    Option (WfIRContext OpCode) := do
  let facts ← fixpointSolve root #[SparseConstantPropagationAnalysis] ctx
  let mut rewriter : PatternRewriter OpCode :=
    { ctx, hasDoneAction := false, worklist := .empty }
  -- Iterate the original context so newly inserted constants are not visited.
  for op in ctx.raw.operations.keys do
    if (op.get! ctx.raw).parent.isSome then
      for result in op.getResults! ctx.raw do
        rewriter ← replaceKnownConstant rewriter facts result (.before op)
  for block in ctx.raw.blocks.keys do
    for argument in block.getArguments! ctx.raw do
      rewriter ← replaceKnownConstant rewriter facts argument
        (InsertPoint.atStart! block rewriter.ctx.raw)
  return rewriter.ctx

def CanonicalizePass.impl (options : PassOptions) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let mut ctx := ctx
  let mut patterns : Array (RewritePattern OpCode) := #[]
  if (options.get? "sccp").getD true then
    let some propagated := propagateConstants ctx op
      | throw "Error while propagating constants"
    ctx := propagated
    -- Fold every operation, including folds to nonconstant operands that the
    -- constant lattice cannot represent. Do not rerun the analysis afterward.
    patterns := patterns.push foldOperation
  if (options.get? "mod-arith-constant").getD true then
    patterns := patterns.push canonicalizeModArithConstant
  if (options.get? "commutative-constant-rhs").getD true then
    patterns := patterns.push commutativeConstantRHS
  let pattern := RewritePattern.GreedyRewritePattern patterns
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying canonicalization patterns"
  | some result => pure result

public def CanonicalizePass : Pass OpCode :=
  { name := "canonicalize"
    description := "Rewrite operations into a canonical form."
    options := .ofList [
      ("sccp",
        { description := "Propagate constants, then fold operations to constants or operands."
          defaultValue := true }),
      ("mod-arith-constant",
        { description := "Reduce modular constants to their canonical representatives."
          defaultValue := true }),
      ("commutative-constant-rhs",
        { description := "Move constants to the right side of commutative operations."
          defaultValue := true })]
    run := CanonicalizePass.impl }

end Veir
