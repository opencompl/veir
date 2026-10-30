module

public import Veir.Passes.Legalization.LegalizerInfo
import Veir.PatternRewriter.Basic
import Veir.Passes.Legalization.LegalizerHelper
import Veir.Passes.Legalization.LegalizationArtifactCombiner
import Veir.PatternRewriter.Puddle.Execution

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

/-- Applies the action of the rules to `op`. Does not match legal operations or illegal ones. -/
private def legalizeInstrStep (info : LegalizerInfo) : LocalRewritePattern OpCode :=
  fun ctx op => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx.raw) | return (ctx, none)
    let pattern? : Option (LocalRewritePattern OpCode) := match info.getAction ctx.raw op opcode with
      | .widenScalar typeIdx width => widenScalar? opcode typeIdx width
      | .lower => (lower? opcode).map Puddle.Pattern.interpret
      | .custom => (info.legalizeCustom opcode).map Puddle.Pattern.interpret
      | .legal | .unsupported => none
    let some pattern := pattern? | return (ctx, none)
    pattern ctx op

/-- Combines the artifact `op` away with the first `tryCombineInstruction` pattern that applies. -/
private def combineArtifactStep : LocalRewritePattern OpCode :=
  fun ctx op => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx.raw) | return (ctx, none)
    for pattern in tryCombineInstruction opcode do
      if let (ctx, some rewrite) ← pattern.interpret ctx op then
        return (ctx, some rewrite)
    return (ctx, none)

/-- The error message for `op`, which could not be legalized with `action`. -/
private def illegalReason (ctx : IRContext OpCode) (op : OperationPtr) (opcode : GMIR)
    (action : LegalizeAction) : String :=
  let name := String.fromUTF8! (IsOpCode.name (op.getOpType! ctx))
  let types := opcode.getTypeGroupTypes! op ctx
  let reason := match action, types.find? fun type => (LLT.ofType? type).isNone with
    | .widenScalar (.type idx) _, _ => s!"widening type group {idx} is not implemented"
    | .lower, _ => "the lowering is not implemented"
    | .custom, _ => "the custom legalization does not apply"
    | _, some type => s!"unsupported type {type}"
    | _, none => "no legalization rule matches"
  s!"unable to legalize {name}: {reason}"

/-! ## Block arguments

  The block arguments are the phis of gMIR. As LLVM's `widenScalar` of `G_PHI`, an integer block
  argument narrower than `width` is widened to `width`: every branch to its block passes the
  `g_anyext` of its operand, and a `g_trunc` at the start of the block gives the rest of the
  block the value at its original type. The legalization artifact combiner then folds the
  `g_anyext` of a `g_trunc` away, so that the widened values flow through the branches. -/

/-- Whether `type` is an integer type narrower than `width`, which `widenBlockArguments` widens. -/
private def isNarrowInteger (width : Nat) (type : TypeAttr) : Bool :=
  match type.val with
  | .integerType intType => 0 < intType.bitwidth && intType.bitwidth < width
  | _ => false

/-- The operand indices of `op`, a `g_br` or `g_brcond`, that it passes to its successor `s`. -/
private def successorOperands (ctx : IRContext OpCode) (op : OperationPtr) (s : Nat) :
    List Nat :=
  if op.getOpType! ctx = OpCode.gmir .g_br then
    List.range (op.getNumOperands! ctx)
  else
    -- The segments of a `g_brcond` are its condition and the operands of each successor.
    let sizes := (op.getProperties! ctx GMIR.g_brcond).operandSegmentSizes.values.map Int.toNat
    let start := 1 + (sizes.extract 1 (s + 1)).foldl (· + ·) 0
    List.range' start (sizes[s + 1]?.getD 0)

/-- Widen the operand `index` of the branch `op`, a value of a narrow block argument of its
    target, with a `g_anyext` in front of `op`. -/
private def widenBranchOperand (width : Nat) (op : OperationPtr) (ctx : WfIRContext OpCode)
    (index : Nat) : Except String (WfIRContext OpCode) := do
  let operand := op.getOperand! ctx.raw index
  if !isNarrowInteger width (operand.getType! ctx.raw) then
    return ctx
  let some (ctx, ext) := WfRewriter.createOp! ctx GMIR.g_anyext
      #[(IntegerType.signless width : TypeAttr)] #[operand] #[] #[] () (InsertPoint.before op)
    | throw "legalizer: cannot widen a branch operand"
  return WfRewriter.replaceOperand! ctx { op := op, index := index } (ext.getResult 0)

/-- Widen the narrow argument `i` of `block`, with a `g_trunc` at the start of the block. -/
private def widenBlockArgument (width : Nat) (block : BlockPtr) (ctx : WfIRContext OpCode)
    (i : Nat) : Except String (WfIRContext OpCode) := do
  let arg : BlockArgumentPtr := { block := block, index := i }
  let type := (ValuePtr.blockArgument arg).getType! ctx.raw
  if !isNarrowInteger width type then
    return ctx
  let ctx := WfRewriter.setType! ctx arg (IntegerType.signless width)
  let some (ctx, trunc) := WfRewriter.createOp! ctx GMIR.g_trunc #[type] #[] #[] #[]
      (({ nsw := false, nuw := false } : NswNuwProperties) : propertiesOf GMIR.g_trunc)
      (InsertPoint.atStart! block ctx.raw)
    | throw "legalizer: cannot truncate a widened block argument"
  let ctx := WfRewriter.replaceValue! ctx arg (trunc.getResult 0)
  return WfRewriter.pushOperand! ctx trunc arg

/--
  Widen the integer block arguments narrower than `width` of every block that is reached only by
  `g_br` and `g_brcond`. The arguments of a block without predecessors, such as the entry block
  of a function, are left alone.
-/
def widenBlockArguments (width : Nat) (ctx : WfIRContext OpCode) :
    Except String (WfIRContext OpCode) := do
  let ops := ctx.raw.operations.keys
  let isBranch (op : OperationPtr) :=
    let opType := op.getOpType! ctx.raw
    opType = OpCode.gmir .g_br || opType = OpCode.gmir .g_brcond
  -- The blocks that another terminator also reaches keep their argument types.
  let blocked := Std.HashSet.ofList <| ops.flatMap fun op =>
    if isBranch op then [] else (op.getSuccessors! ctx.raw).toList
  let widened (block : BlockPtr) := !blocked.contains block && block.hasPredecessor! ctx.raw
  let blocks := ctx.raw.blocks.keys.filter widened
  let ctx ← ops.filter isBranch |>.foldlM (init := ctx) fun ctx op =>
    (List.range (op.getNumSuccessors! ctx.raw)).foldlM (init := ctx) fun ctx s =>
      if widened (op.getSuccessor! ctx.raw s) then
        (successorOperands ctx.raw op s).foldlM (widenBranchOperand width op) ctx
      else
        pure ctx
  blocks.foldlM (init := ctx) fun ctx block =>
    (List.range (block.getNumArguments! ctx.raw)).foldlM (widenBlockArgument width block) ctx

/-- Legalizes all GMIR operations of `ctx`. Fails if one of them remains illegal. -/
def legalize (info : LegalizerInfo) (ctx : WfIRContext OpCode) :
    Except String (WfIRContext OpCode) := do
  -- As in LLVM, an artifact is combined before it is legalized.
  -- TODO: Use a proper worklist for artifacts.
  let pattern := RewritePattern.GreedyRewritePattern
    #[.fromLocalRewrite combineArtifactStep, .fromLocalRewrite info.legalizeInstrStep]
  let some ctx := RewritePattern.applyInContext pattern ctx
    | throw "error while applying legalization"
  -- The greedy rewriter does not report the operations it could not rewrite, so we check the
  -- legality of every operation afterwards.
  ctx.raw.forOpsDepM fun op _ => do
    let some opcode := toDialect? GMIR (op.getOpType! ctx.raw) | return
    match info.getAction ctx.raw op opcode with
    | .legal => pure ()
    | action => throw (illegalReason ctx.raw op opcode action)
  return ctx

end LegalizerInfo

end

end Veir
