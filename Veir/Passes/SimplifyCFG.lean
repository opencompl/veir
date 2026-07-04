import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Rewriter.InlineBlock

namespace Veir

def SimplifyCFG.constantBoolValue? (val : ValuePtr) (ctx : IRContext OpCode) : Option Bool := do
  let .opResult result := val | none
  let definingOp := result.op
  match definingOp.getOpType! ctx with
  | .arith .constant =>
      let props := definingOp.getProperties! ctx (.arith .constant)
      return decide (props.value.value ≠ 0)
  | .llvm .mlir__constant =>
      let props := definingOp.getProperties! ctx (.llvm .mlir__constant)
      let .integer intAttr := props.value | none
      return decide (intAttr.value ≠ 0)
  | _ => none

def SimplifyCFG.condBrEdgeArgs (operands : Array ValuePtr) (props : CondBrProperties) :
    Array ValuePtr × Array ValuePtr :=
  let trueArgCount := Int.toNat props.operandSegmentSizes.values[1]!
  let falseArgCount := Int.toNat props.operandSegmentSizes.values[2]!
  let trueArgs := operands.extract 1 (1 + trueArgCount)
  let falseArgs := operands.extract (1 + trueArgCount) (1 + trueArgCount + falseArgCount)
  (trueArgs, falseArgs)

def SimplifyCFG.condBrArgsAndDest? (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (props : CondBrProperties) :
    Option (Array ValuePtr × BlockPtr) := do
  let operands := op.getOperands! rewriter.ctx.raw
  let cond := operands[0]!
  let some takeTrue := SimplifyCFG.constantBoolValue? cond rewriter.ctx.raw | none
  let (trueArgs, falseArgs) := SimplifyCFG.condBrEdgeArgs operands props
  let dest := op.getSuccessor! rewriter.ctx.raw (if takeTrue then 0 else 1)
  let args := if takeTrue then trueArgs else falseArgs
  return (args, dest)

def SimplifyCFG.sameSuccessorCondBrArgsAndDest? (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (props : CondBrProperties) :
    Option (Array ValuePtr × BlockPtr) := do
  let trueDest := op.getSuccessor! rewriter.ctx.raw 0
  let falseDest := op.getSuccessor! rewriter.ctx.raw 1
  if trueDest != falseDest then
    none
  let operands := op.getOperands! rewriter.ctx.raw
  let (trueArgs, falseArgs) := SimplifyCFG.condBrEdgeArgs operands props
  if trueArgs != falseArgs then
    none
  return (trueArgs, trueDest)

def SimplifyCFG.foldCfSameSuccessorCondBr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw ≠ .cf .cond_br then
    return rewriter
  let props := op.getProperties! rewriter.ctx.raw (.cf .cond_br)
  let some (args, dest) := SimplifyCFG.sameSuccessorCondBrArgsAndDest? rewriter op props
    | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.cf .br) #[] args #[dest] #[] () (some (.before op))
  return rewriter.replaceOp! op newOp

def SimplifyCFG.foldLLVMSameSuccessorCondBr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw ≠ .llvm .cond_br then
    return rewriter
  let props := op.getProperties! rewriter.ctx.raw (.llvm .cond_br)
  let some (args, dest) := SimplifyCFG.sameSuccessorCondBrArgsAndDest? rewriter op props
    | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .br) #[] args #[dest] #[] () (some (.before op))
  return rewriter.replaceOp! op newOp

def SimplifyCFG.foldCfConstantCondBr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw ≠ .cf .cond_br then
    return rewriter
  let props := op.getProperties! rewriter.ctx.raw (.cf .cond_br)
  let some (args, dest) := SimplifyCFG.condBrArgsAndDest? rewriter op props | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.cf .br) #[] args #[dest] #[] () (some (.before op))
  return rewriter.replaceOp! op newOp

def SimplifyCFG.foldLLVMConstantCondBr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw ≠ .llvm .cond_br then
    return rewriter
  let props := op.getProperties! rewriter.ctx.raw (.llvm .cond_br)
  let some (args, dest) := SimplifyCFG.condBrArgsAndDest? rewriter op props | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .br) #[] args #[dest] #[] () (some (.before op))
  return rewriter.replaceOp! op newOp

def SimplifyCFG.substituteTrampolineArg? (block : BlockPtr) (incomingArgs : Array ValuePtr)
    (value : ValuePtr) : Option ValuePtr := do
  let .blockArgument arg := value | none
  if arg.block != block then
    none
  incomingArgs[arg.index]?

def SimplifyCFG.composeTrampolineArgs? (ctx : IRContext OpCode) (block : BlockPtr)
    (incomingArgs : Array ValuePtr) (trampolineBranch : OperationPtr) : Option (Array ValuePtr) := do
  let mut args := #[]
  for value in trampolineBranch.getOperands! ctx do
    let value ← SimplifyCFG.substituteTrampolineArg? block incomingArgs value
    args := args.push value
  return args

def SimplifyCFG.trampolineBranch? (ctx : IRContext OpCode) (block : BlockPtr)
    (brOpType : OpCode) : Option OperationPtr := do
  let blockData := block.get! ctx
  let some firstOp := blockData.firstOp | none
  let some lastOp := blockData.lastOp | none
  if firstOp != lastOp then
    none
  if firstOp.getOpType! ctx != brOpType then
    none
  let dest := firstOp.getSuccessor! ctx 0
  if dest == block then
    none
  return firstOp

def SimplifyCFG.bypassBlock? (ctx : IRContext OpCode) (block : BlockPtr)
    (incomingArgs : Array ValuePtr) (brOpType : OpCode) :
    Option (Array ValuePtr × BlockPtr) := do
  let trampolineBranch ← SimplifyCFG.trampolineBranch? ctx block brOpType
  let args ← SimplifyCFG.composeTrampolineArgs? ctx block incomingArgs trampolineBranch
  return (args, trampolineBranch.getSuccessor! ctx 0)

def SimplifyCFG.condBrPropertiesForArgs (oldProps : CondBrProperties)
    (trueArgs falseArgs : Array ValuePtr) : CondBrProperties :=
  { branch_weights := oldProps.branch_weights
    operandSegmentSizes :=
      { elementType := { bitwidth := 32 }
        values := #[1, Int.ofNat trueArgs.size, Int.ofNat falseArgs.size] } }

def SimplifyCFG.bypassCfUnconditionalBranch (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw != .cf .br then
    return rewriter
  let dest := op.getSuccessor! rewriter.ctx.raw 0
  let some (args, newDest) :=
    SimplifyCFG.bypassBlock? rewriter.ctx.raw dest (op.getOperands! rewriter.ctx.raw) (.cf .br)
    | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.cf .br) #[] args #[newDest] #[] () (some (.before op))
  return rewriter.replaceOp! op newOp

def SimplifyCFG.bypassLLVMUnconditionalBranch (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw != .llvm .br then
    return rewriter
  let dest := op.getSuccessor! rewriter.ctx.raw 0
  let some (args, newDest) :=
    SimplifyCFG.bypassBlock? rewriter.ctx.raw dest (op.getOperands! rewriter.ctx.raw) (.llvm .br)
    | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .br) #[] args #[newDest] #[] () (some (.before op))
  return rewriter.replaceOp! op newOp

def SimplifyCFG.bypassCfCondBranch (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw != .cf .cond_br then
    return rewriter
  let props := op.getProperties! rewriter.ctx.raw (.cf .cond_br)
  let operands := op.getOperands! rewriter.ctx.raw
  let cond := operands[0]!
  let (trueArgs, falseArgs) := SimplifyCFG.condBrEdgeArgs operands props
  let trueDest := op.getSuccessor! rewriter.ctx.raw 0
  let falseDest := op.getSuccessor! rewriter.ctx.raw 1
  let (trueArgs, trueDest, changedTrue) :=
    match SimplifyCFG.bypassBlock? rewriter.ctx.raw trueDest trueArgs (.cf .br) with
    | some (args, dest) => (args, dest, true)
    | none => (trueArgs, trueDest, false)
  let (falseArgs, falseDest, changedFalse) :=
    match SimplifyCFG.bypassBlock? rewriter.ctx.raw falseDest falseArgs (.cf .br) with
    | some (args, dest) => (args, dest, true)
    | none => (falseArgs, falseDest, false)
  if !changedTrue && !changedFalse then
    return rewriter
  let newProps := SimplifyCFG.condBrPropertiesForArgs props trueArgs falseArgs
  let args := #[cond] ++ trueArgs ++ falseArgs
  let (rewriter, newOp) ←
    rewriter.createOp! (.cf .cond_br) #[] args #[trueDest, falseDest] #[] newProps (some (.before op))
  return rewriter.replaceOp! op newOp

def SimplifyCFG.bypassLLVMCondBranch (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw != .llvm .cond_br then
    return rewriter
  let props := op.getProperties! rewriter.ctx.raw (.llvm .cond_br)
  let operands := op.getOperands! rewriter.ctx.raw
  let cond := operands[0]!
  let (trueArgs, falseArgs) := SimplifyCFG.condBrEdgeArgs operands props
  let trueDest := op.getSuccessor! rewriter.ctx.raw 0
  let falseDest := op.getSuccessor! rewriter.ctx.raw 1
  let (trueArgs, trueDest, changedTrue) :=
    match SimplifyCFG.bypassBlock? rewriter.ctx.raw trueDest trueArgs (.llvm .br) with
    | some (args, dest) => (args, dest, true)
    | none => (trueArgs, trueDest, false)
  let (falseArgs, falseDest, changedFalse) :=
    match SimplifyCFG.bypassBlock? rewriter.ctx.raw falseDest falseArgs (.llvm .br) with
    | some (args, dest) => (args, dest, true)
    | none => (falseArgs, falseDest, false)
  if !changedTrue && !changedFalse then
    return rewriter
  let newProps := SimplifyCFG.condBrPropertiesForArgs props trueArgs falseArgs
  let args := #[cond] ++ trueArgs ++ falseArgs
  let (rewriter, newOp) ←
    rewriter.createOp! (.llvm .cond_br) #[] args #[trueDest, falseDest] #[] newProps (some (.before op))
  return rewriter.replaceOp! op newOp

def SimplifyCFG.isUniquelyReachedFrom? (ctx : IRContext OpCode) (dest : BlockPtr)
    (branch : OperationPtr) : Bool :=
  match (dest.get! ctx).firstUse with
  | some use =>
      let blockOperand := use.get! ctx
      blockOperand.owner == branch && blockOperand.nextUse.isNone
  | none => false

set_option warn.sorry false in
def SimplifyCFG.mergeUnconditionalBranch (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (opIn : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let opType := op.getOpType! rewriter.ctx.raw
  if opType ≠ .cf .br && opType ≠ .llvm .br then
    return rewriter
  let some pred := (op.get! rewriter.ctx.raw).parent | return rewriter
  let dest := op.getSuccessor! rewriter.ctx.raw 0
  if hSelf : pred = dest then
    return rewriter
  if !SimplifyCFG.isUniquelyReachedFrom? rewriter.ctx.raw dest op then
    return rewriter
  let some destParent := (dest.get! rewriter.ctx.raw).parent | return rewriter
  if (destParent.get! rewriter.ctx.raw).firstBlock == some dest then
    return rewriter

  let ip := InsertPoint.before op
  let blockArgs := (List.range (dest.getNumArguments! rewriter.ctx.raw)).toArray.map
    fun i => (ValuePtr.blockArgument { block := dest, index := i })
  let branchArgs := op.getOperands! rewriter.ctx.raw
  let afterInline ← match hInline : Rewriter.inlineBlock rewriter.ctx.raw dest ip
      (ipIn := by simpa [ip] using opIn)
      (block' := pred)
      (ipBlock := by sorry)
      (blockNe := by sorry)
      (blockIn := by sorry) with
    | some rawCtx => some (⟨rawCtx, Rewriter.inlineBlock_wellFormed hInline⟩ : WfIRContext OpCode)
    | none => none
  let mut mergedCtx := afterInline
  for (blockArg, i) in blockArgs.zipIdx do
    let some branchArg := branchArgs[i]? | none
    mergedCtx := WfRewriter.replaceValue mergedCtx blockArg branchArg sorry sorry sorry
  let finalCtx := WfRewriter.eraseOp mergedCtx op sorry sorry sorry
  let some finalCtx := WfRewriter.eraseBlock finalCtx dest sorry | none
  return { rewriter with ctx := finalCtx, hasDoneAction := true }

def SimplifyCFG.isDeadBlock (ctx : IRContext OpCode) (block : BlockPtr) : Bool :=
  let blockData := block.get! ctx
  match blockData.parent with
  | none => false
  | some region =>
      blockData.firstUse.isNone && (region.get! ctx).firstBlock != some block

set_option warn.sorry false in
def SimplifyCFG.eraseDeadBlockOps (rewriter : PatternRewriter OpCode)
    (block : BlockPtr) (fuel : Nat) : PatternRewriter OpCode :=
  match fuel with
  | 0 => rewriter
  | fuel + 1 =>
      match (block.get! rewriter.ctx.raw).lastOp with
      | none => rewriter
      | some deadOp =>
          if deadOp.getNumRegions! rewriter.ctx.raw != 0 then
            rewriter
          else if deadOp.hasUses! rewriter.ctx.raw then
            rewriter
          else
            let ctx := WfRewriter.eraseOp rewriter.ctx deadOp sorry sorry sorry
            let rewriter :=
              { rewriter with
                ctx := ctx
                hasDoneAction := true
                worklist := rewriter.worklist.remove deadOp }
            SimplifyCFG.eraseDeadBlockOps rewriter block fuel

set_option warn.sorry false in
def SimplifyCFG.removeDeadBlock (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some block := (op.get! rewriter.ctx.raw).parent | return rewriter
  if !SimplifyCFG.isDeadBlock rewriter.ctx.raw block then
    return rewriter
  let rewriter :=
    SimplifyCFG.eraseDeadBlockOps rewriter block rewriter.ctx.raw.operations.size
  if (block.get! rewriter.ctx.raw).lastOp.isSome then
    return rewriter
  let some ctx := WfRewriter.eraseBlock rewriter.ctx block sorry | return rewriter
  return { rewriter with ctx := ctx, hasDoneAction := true }

def SimplifyCFGPass.impl (ctx : WfIRContext OpCode)
    (_op : OperationPtr) (_ : _op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    SimplifyCFG.foldCfSameSuccessorCondBr,
    SimplifyCFG.foldLLVMSameSuccessorCondBr,
    SimplifyCFG.foldCfConstantCondBr,
    SimplifyCFG.foldLLVMConstantCondBr,
    SimplifyCFG.bypassCfUnconditionalBranch,
    SimplifyCFG.bypassLLVMUnconditionalBranch,
    SimplifyCFG.bypassCfCondBranch,
    SimplifyCFG.bypassLLVMCondBranch,
    SimplifyCFG.mergeUnconditionalBranch,
    SimplifyCFG.removeDeadBlock
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying simplify-cfg"
  | some ctx => pure ctx

public def SimplifyCFGPass : Pass OpCode :=
  { name := "simplify-cfg"
    description := "Simplify control-flow graph structure."
    run := SimplifyCFGPass.impl }

end Veir
