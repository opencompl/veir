module

public import Veir.Passes.Legalization.LegalizerInfo
public import Veir.Passes.CheckedDriver
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
def blockArgumentAction? (info : LegalizerInfo) (type : TypeAttr) :
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

/-- Argument `i` of `block` is an integer narrower than `width` bits. -/
def narrowerArgument (block : BlockPtr) (ctx : IRContext OpCode) (i width : Nat) : Bool :=
  match (block.getArguments! ctx)[i]? with
  | some arg =>
    match (arg.getType! ctx).val with
    | .integerType t => decide (t.bitwidth < width)
    | _ => false
  | none => false

/-- Widens the arguments of the phi `block` as the block-argument rules ask. What the soundness of
the widening needs (`widenBlockArguments_sound`) is checked here rather than derived from the rules
and the traversal: the block is a phi block, each argument is widened once, from a narrower
integer. -/
def widenPhiBlock (info : LegalizerInfo) (ctx : WfIRContext OpCode) (block : BlockPtr) :
    Except String (WfIRContext OpCode) :=
  let args := (block.getArguments! ctx.raw).toList.zipIdx.filterMap fun (arg, i) => do
    let .widenScalar (.type 0) width ← blockArgumentAction? info (arg.getType! ctx.raw) | none
    return (i, width)
  if args.isEmpty then .ok ctx
  else if block.InBounds ctx.raw ∧ block.hasPredecessor! ctx.raw = true then
    if (args.map Prod.fst).Nodup then
      if args.all (fun (i, width) => narrowerArgument block ctx.raw i width) = true then
        match widenBlockArguments block args ctx with
        | some ctx => .ok ctx
        | none => .error "unable to widen a block argument: a predecessor is not a branch"
      else .error "unable to widen a block argument: it is not a narrower integer"
    else .error "unable to widen a block argument: an argument is widened twice"
  else .error "unable to widen a block argument: the block is not a phi block"

/-- Widens the block arguments in the functions under `root` as the block-argument rules ask. -/
def legalizeBlockArguments (info : LegalizerInfo) (ctx : WfIRContext OpCode)
    (root : OperationPtr) : Except String (WfIRContext OpCode) :=
  (phiBlocks ctx.raw root).foldlM (widenPhiBlock info) ctx

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

/-! ## Legalization

The legalizer widens the narrow phis (`legalizeBlockArguments`, assumed to refine the module:
`legalizeBlockArguments_sound`), then runs the rules of the registries, which are all proved to
refine the module, through the module-filtered driver, and rejects what they cannot legalize.

An artifact is not legalized while its source is still illegal. LLVM's legalizer legalizes all
other instructions before it combines artifacts, and only legalizes the artifacts it cannot combine.
Legalizing the source first may turn it into an artifact that the artifact combiner folds away,
e.g. widening a `g_icmp` under a `g_zext` leaves `g_zext (g_trunc (g_icmp))`. -/

/-- The rule that legalizes `op`, an `opcode`: the action of the rules, as a pattern. Legal and
unsupported operations have none. -/
def legalizeInstrChoice (info : LegalizerInfo) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (opcode : GMIR) : Option (Puddle.Pattern OpCode) :=
  if isArtifact opcode && hasIllegalSource info ctx.raw op then none else
  match info.getAction ctx.raw op opcode with
  | .widenScalar typeIdx width => widenScalarPattern? opcode typeIdx width
  | .narrowScalar typeIdx width => narrowScalar? opcode typeIdx width
  | .lower => lower? opcode
  | .custom => info.legalizeCustom opcode
  | .legal | .unsupported => none

/-- The rules the legalizer tries at `op`, in order: the artifact combines (as in LLVM, an
artifact is combined before it is legalized), then the legalization rule. -/
def legalizeRules (info : LegalizerInfo) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    List (Puddle.Pattern OpCode) :=
  match toDialect? GMIR (op.getOpType! ctx.raw) with
  | none => []
  | some opcode =>
    tryCombineInstruction opcode ++ (legalizeInstrChoice info ctx op opcode).toList

/-- The pattern of the legalizer: combine an artifact away, else legalize the operation. -/
def legalizePattern (info : LegalizerInfo) : RewritePattern OpCode :=
  RewritePattern.ofRules (legalizeRules info)

/-- The legalizer, `pass` naming the pass in its errors: it checks the module, widens its phis,
applies the rules to its functions, and fails if an operation or a phi is left illegal (the greedy
rewriter does not report the operations it could not rewrite). -/
def legalize (info : LegalizerInfo) (pass : String) : PurePass := fun ctx root => do
  checkModuleRoot pass ctx root
  let ctx ← info.legalizeBlockArguments ctx root
  let ctx ← applyToFunctionsChecked pass (legalizePattern info) ctx root
  info.checkOperations ctx.raw
  info.checkBlockArguments ctx.raw
  return ctx

end LegalizerInfo

end

end Veir
