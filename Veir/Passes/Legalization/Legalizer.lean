module

public import Veir.Passes.Legalization.LegalizerInfo
public import Veir.Passes.StrictDriver
public import Veir.PatternRewriter.Choice
import Veir.PatternRewriter.Basic
import Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import Veir.PatternRewriter.Puddle.Execution
import Veir.Interfaces.ControlFlowInterfaces

/-!
# GMIR Legalizer

This file implements the target-independent legalizer. A target builds its legalization pass by
calling `LegalizerInfo.legalize` with its target specific `LegalizerInfo`.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/Legalizer.h
-/

namespace Veir

public section

namespace LegalizerInfo

/-- Whether `opcode` is an artifact, as in LLVM's `Legalizer.cpp`. -/
private def isArtifact : GMIR → Bool
  | .g_trunc | .g_zext | .g_anyext | .g_sext | .g_merge_values | .g_unmerge_values => true
  | _ => false

/-- Whether an operand of `op` is the result of a gMIR operation that is not legal yet. -/
private def hasIllegalSource (info : LegalizerInfo) (ctx : IRContext OpCode) (op : OperationPtr) :
    Bool :=
  (op.getOperands! ctx).any fun
    | .opResult result =>
      match toDialect? GMIR (result.op.getOpType! ctx) with
      | some opcode => !(info.getAction ctx result.op opcode matches .legal)
      | none => false
    | _ => false

/--
Applies the action of the rules to `op`. Does not match legal operations or illegal ones.

An artifact is not legalized while its source is still illegal. LLVM's legalizer legalizes all
other instructions before it combines artifacts, and only legalizes the artifacts it cannot combine.
Legalizing the source first may turn it into an artifact that the artifact combiner folds away,
e.g. widening a `g_icmp` under a `g_zext` leaves `g_zext (g_trunc (g_icmp))`.
-/
private def legalizeInstrStep (info : LegalizerInfo) : LocalRewritePattern OpCode :=
  fun ctx op => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx.raw) | return (ctx, none)
    if isArtifact opcode && hasIllegalSource info ctx.raw op then return (ctx, none)
    let pattern? : Option (LocalRewritePattern OpCode) := match info.getAction ctx.raw op opcode with
      | .widenScalar typeIdx width => widenScalar? opcode typeIdx width
      | .narrowScalar typeIdx width =>
        (narrowScalar? opcode typeIdx width).map Puddle.Pattern.interpret
      | .lower => (lower? opcode).map Puddle.Pattern.interpret
      | .custom => (info.legalizeCustom opcode).map Puddle.Pattern.interpret
      | .legal | .unsupported => none
    let some pattern := pattern? | return (ctx, none)
    pattern ctx op

/-- Combines the artifact `op` away with the first `tryCombineInstruction` pattern that applies. -/
private def combineArtifactStep : LocalRewritePattern OpCode :=
  fun ctx op => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx.raw) | return (ctx, none)
    go op (tryCombineInstruction opcode) ctx
where
  go (op : OperationPtr) : List (Puddle.Pattern OpCode) → WfIRContext OpCode →
      Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr))
    | [], ctx => some (ctx, none)
    | pattern :: patterns, ctx =>
      match pattern.interpret ctx op with
      | some (ctx, none) => go op patterns ctx
      | result => result

/-- The error message when `action` cannot legalize `name`, whose type groups have `types`. -/
private def illegalReason (name : String) (types : Array TypeAttr) (action : LegalizeAction) :
    String :=
  let reason := match action, types.find? fun type => (LLT.ofType? type).isNone with
    | .widenScalar (.type idx) _, _ => s!"widening type group {idx} is not implemented"
    | .narrowScalar (.type idx) _, _ => s!"narrowing type group {idx} is not implemented"
    | .lower, _ => "the lowering is not implemented"
    | .custom, _ => "the custom legalization does not apply"
    | _, some type => s!"unsupported type {type}"
    | _, none => "no legalization rule matches"
  s!"unable to legalize {name}: {reason}"

/-! ## Block arguments -/

/-- The action for a block argument of type `type`, or `none` if it has no low-level type. -/
private def blockArgumentAction? (info : LegalizerInfo) (type : TypeAttr) :
    Option LegalizeAction :=
  (LegalityQuery.ofTypes? #[type] ()).map info.getBlockArgumentAction

/--
  The blocks in the functions under `root` that a branch jumps to. Only their arguments are phis:
  the arguments of an entry block are the parameters of the function.
-/
private def phiBlocks (ctx : IRContext OpCode) (root : OperationPtr) : List BlockPtr := Id.run do
  let mut blocks := []
  for func in collectNestedFunctions ctx root do
    let mut block? := (func.getRegion! ctx 0).getFirstBlock! ctx
    while let some block := block? do
      if block.hasPredecessor! ctx then blocks := block :: blocks
      block? := block.getNextBlock! ctx
  return blocks.reverse

/-- Widens the block arguments in the functions under `root` as the block-argument rules ask. -/
private def legalizeBlockArguments (info : LegalizerInfo) (ctx : WfIRContext OpCode)
    (root : OperationPtr) : Except String (WfIRContext OpCode) :=
  (phiBlocks ctx.raw root).foldlM (init := ctx) fun ctx block => do
    let args := (block.getArguments! ctx.raw).toList.zipIdx.filterMap fun (arg, i) => do
      let .widenScalar (.type 0) width ← blockArgumentAction? info (arg.getType! ctx.raw) | none
      return (i, width)
    if args.isEmpty then return ctx
    let some ctx := widenBlockArguments block args ctx
      | throw "unable to widen a block argument: a predecessor is not a branch"
    return ctx

/-- Fails if a block argument that is a phi is not legal. -/
private def checkBlockArguments (info : LegalizerInfo) (ctx : IRContext OpCode) :
    Except String Unit :=
  ctx.forBlocksDepM fun block _ => do
    if !block.hasPredecessor! ctx then return
    for arg in block.getArguments! ctx do
      let type := arg.getType! ctx
      match blockArgumentAction? info type with
      | none | some .legal => pure ()
      | some action => throw (illegalReason s!"a block argument of type {type}" #[type] action)

/-- Fails if a gMIR operation in `ctx` is not legal. -/
private def checkOperations (info : LegalizerInfo) (ctx : IRContext OpCode) :
    Except String Unit :=
  ctx.forOpsDepM fun op _ => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx) | return
    match info.getAction ctx op opcode with
    | .legal => pure ()
    | action =>
      let name := String.fromUTF8! (IsOpCode.name (op.getOpType! ctx))
      throw (illegalReason name (opcode.getTypeGroupTypes! op ctx) action)

/--
Legalizes the block arguments and all GMIR operations in the functions under `root`. Fails if one of
them remains illegal.
-/
def legalize (info : LegalizerInfo) (ctx : WfIRContext OpCode) (root : OperationPtr) :
    Except String (WfIRContext OpCode) := do
  -- `legalizeBlockArguments` is unproven, so not run: a narrow phi is rejected instead.
  info.checkBlockArguments ctx.raw
  -- As in LLVM, an artifact is combined before it is legalized.
  -- TODO: Use a proper worklist for artifacts.
  let pattern := RewritePattern.GreedyRewritePattern
    #[.fromLocalRewrite combineArtifactStep, .fromLocalRewrite info.legalizeInstrStep]
  let some ctx := RewritePattern.applyToFunctions pattern ctx root
    | throw "error while applying legalization"
  -- The greedy rewriter does not report the operations it could not rewrite, so we check the
  -- legality of every operation afterwards.
  info.checkOperations ctx.raw
  info.checkBlockArguments ctx.raw
  return ctx

/-! ## Strict legalization

The strict legalizer runs the rules of the registries, which are all proved to refine the module,
through the module-filtered driver, and rejects what they cannot legalize: a narrow phi, as the
default legalizer does since `legalizeBlockArguments` is unproven. -/

/-- The proved rule that legalizes `op`, an `opcode`, chosen as `legalizeInstrStep` chooses it. -/
def legalizeInstrChoiceStrict (info : LegalizerInfo) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (opcode : GMIR) : Option (Puddle.Pattern OpCode) :=
  if isArtifact opcode && hasIllegalSource info ctx.raw op then none else
  match info.getAction ctx.raw op opcode with
  | .widenScalar typeIdx width => widenScalarPattern? opcode typeIdx width
  | .narrowScalar typeIdx width => narrowScalar? opcode typeIdx width
  | .lower => lower? opcode
  | .custom => info.legalizeCustom opcode
  | .legal | .unsupported => none

/-- The proved rules the strict legalizer tries at `op`, in order: the artifact combines, as
`combineArtifactStep` tries them, then the legalization rule. -/
def legalizeStrictRules (info : LegalizerInfo) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    List (Puddle.Pattern OpCode) :=
  match toDialect? GMIR (op.getOpType! ctx.raw) with
  | none => []
  | some opcode =>
    tryCombineInstruction opcode ++ (legalizeInstrChoiceStrict info ctx op opcode).toList

/-- The pattern of the strict legalizer: combine an artifact away, else legalize the operation. -/
def legalizeStrictPattern (info : LegalizerInfo) : RewritePattern OpCode :=
  RewritePattern.ofRules (legalizeStrictRules info)

/-- The strict legalizer, `pass` naming the pass in its errors: it checks the module and its phis,
applies the proved rules to its functions, and fails if an operation is left illegal. -/
def legalizeStrict (info : LegalizerInfo) (pass : String) : PurePass := fun ctx root => do
  checkModuleRoot pass ctx root
  info.checkBlockArguments ctx.raw
  let ctx ← applyToFunctionsStrict pass (legalizeStrictPattern info) ctx root
  info.checkOperations ctx.raw
  return ctx

end LegalizerInfo

end

end Veir
