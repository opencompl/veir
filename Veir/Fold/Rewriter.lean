module

public import Veir.Fold
public import Veir.PatternRewriter.Basic

/-!
  # Folding rewrites and constant materialization

  This module contains the mutating half of the folding infrastructure: the
  machinery for turning a `FoldDecision` into IR. It is implementation, not
  API; the entry points built on it live in `Veir.Interfaces.FoldInterfaces`.
-/

public section

namespace Veir

/-- Preferred constant operation for ordinary integer results. Register
    constants are materialized according to their result type. -/
inductive IntegerConstantDialect where
  | arith
  | llvm
deriving Inhabited, BEq, DecidableEq

/-- Select the conventional integer constant dialect for an operation. -/
def IntegerConstantDialect.forOp : OpCode → IntegerConstantDialect
  | .llvm _ => .llvm
  | _ => .arith

/--
  Detached constant materialization, for use by `LocalRewritePattern`s: the
  returned operation is not linked into a block. Clients that need to insert a
  constant at a program point use `PatternRewriter.materializeConstant!`
  instead.

  Concrete integers use the requested ordinary integer dialect. Poison becomes
  `llvm.mlir.poison`, and register values become `riscv.li`.
-/
def WfRewriter.materializeConstant! (ctx : WfIRContext OpCode)
    (rv : RuntimeValue) (resType : TypeAttr)
    (integerDialect : IntegerConstantDialect)
    : Option (WfIRContext OpCode × OperationPtr) :=
  if rv.conformsFoldResult resType then
    match rv with
    | .int bw (.val v) =>
      match integerDialect with
      | .llvm =>
        let properties : LLVMConstantProperties :=
          { value := .integer (IntegerAttr.mk v.toInt (IntegerType.mk bw)) }
        WfRewriter.createOp! ctx (.llvm .mlir__constant) #[resType] #[] #[] #[] properties none
      | .arith =>
        let properties : ArithConstantProperties :=
          { value := IntegerAttr.mk v.toInt (IntegerType.mk bw) }
        WfRewriter.createOp! ctx (.arith .constant) #[resType] #[] #[] #[] properties none
    | .int _ .poison =>
      WfRewriter.createOp! ctx (.llvm .mlir__poison) #[resType] #[] #[] #[] () none
    | .reg r =>
      let properties : RISCVImmediateProperties :=
        { value := IntegerAttr.mk r.val.toInt (IntegerType.mk 64) }
      WfRewriter.createOp! ctx (.riscv .li) #[resType] #[] #[] #[] properties none
    | _ => none
  else none

/--
  Local rewrite that folds an existing operation. An unmaterializable semantic
  constant is treated as a non-match, leaving the IR unchanged.
-/
def foldOperationLocal (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  if _ : op.InBounds ctx.raw then
    let opType := op.getOpType! ctx.raw
    let operands := op.getOperands! ctx.raw
    let constOperands := operands.map (ValuePtr.constantValue · ctx.raw)
    match foldDecisionForOp op constOperands ctx.raw with
    | .noFold => some (ctx, none)
    | .useOperand j =>
      match operands[j]? with
      | some operand => some (ctx, some (#[], #[operand]))
      | none => some (ctx, none)
    | .useConstant rv =>
      match (op.getResultTypes! ctx.raw)[0]? with
      | none => some (ctx, none)
      | some resultType =>
        match WfRewriter.materializeConstant! ctx rv resultType
            (.forOp opType) with
        | some (ctx, newOp) => some (ctx, some (#[newOp], #[newOp.getResult 0]))
        | none => some (ctx, none)
  else some (ctx, none)

/-!
  ## Bodies of the folding entry points

  The declarations clients call, together with the contracts they promise, are
  in `Veir.Interfaces.FoldInterfaces`; only the code lives here. Call the
  interface, not these.
-/

namespace Fold.Impl

/-- Implements `PatternRewriter.materializeConstant!`. -/
def materializeConstant! (rewriter : PatternRewriter OpCode)
    (rv : RuntimeValue) (resType : TypeAttr)
    (integerDialect : IntegerConstantDialect) (ip : InsertPoint)
    : Option (PatternRewriter OpCode × OperationPtr) :=
  if rv.conformsFoldResult resType then
    match rv with
    | .int bw (.val v) =>
      match integerDialect with
      | .llvm =>
        let properties : LLVMConstantProperties :=
          { value := .integer (IntegerAttr.mk v.toInt (IntegerType.mk bw)) }
        rewriter.createOp! (.llvm .mlir__constant) #[resType] #[] #[] #[] properties (some ip)
      | .arith =>
        let properties : ArithConstantProperties :=
          { value := IntegerAttr.mk v.toInt (IntegerType.mk bw) }
        rewriter.createOp! (.arith .constant) #[resType] #[] #[] #[] properties (some ip)
    | .int _ .poison =>
      rewriter.createOp! (.llvm .mlir__poison) #[resType] #[] #[] #[] () (some ip)
    | .reg r =>
      let properties : RISCVImmediateProperties :=
        { value := IntegerAttr.mk r.val.toInt (IntegerType.mk 64) }
      rewriter.createOp! (.riscv .li) #[resType] #[] #[] #[] properties (some ip)
    | _ => none
  else none

/-- Implements `PatternRewriter.createOrFoldOp!`. -/
def createOrFoldOp! (rewriter : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr)
    (properties : HasOpInfo.propertiesOf opType) (insertionPoint : InsertPoint)
    : Option (PatternRewriter OpCode × Array ValuePtr) := do
  let constOperands := operands.map (ValuePtr.constantValue · rewriter.ctx.raw)
  match foldDecision opType properties resultTypes constOperands with
  | .useOperand j =>
    match operands[j]? with
    | some operand => return (rewriter, #[operand])
    | none =>
      let (rewriter, newOp) ← rewriter.createOp! opType resultTypes operands
        #[] #[] properties (some insertionPoint)
      return (rewriter, newOp.getResults! rewriter.ctx.raw)
  | .useConstant rv =>
    match resultTypes[0]? with
    | some resultType =>
      match materializeConstant! rewriter rv resultType (.forOp opType) insertionPoint with
      | some (rewriter, newOp) =>
        return (rewriter, newOp.getResults! rewriter.ctx.raw)
      | none =>
        let (rewriter, newOp) ← rewriter.createOp! opType resultTypes operands
          #[] #[] properties (some insertionPoint)
        return (rewriter, newOp.getResults! rewriter.ctx.raw)
    | none =>
      let (rewriter, newOp) ← rewriter.createOp! opType resultTypes operands
        #[] #[] properties (some insertionPoint)
      return (rewriter, newOp.getResults! rewriter.ctx.raw)
  | .noFold =>
    let (rewriter, newOp) ← rewriter.createOp! opType resultTypes operands
      #[] #[] properties (some insertionPoint)
    return (rewriter, newOp.getResults! rewriter.ctx.raw)

/-- Implements `PatternRewriter.createOrFoldAndReplaceOp!`. -/
def createOrFoldAndReplaceOp! (rewriter : PatternRewriter OpCode)
    (oldOp : OperationPtr) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array ValuePtr) (properties : HasOpInfo.propertiesOf opType)
    (insertionPoint : InsertPoint) : Option (PatternRewriter OpCode) := do
  let (rewriter, newValues) ←
    createOrFoldOp! rewriter opType resultTypes operands properties insertionPoint
  guard (oldOp.getNumResults! rewriter.ctx.raw == newValues.size)
  let mut rewriter := rewriter
  for h : i in 0...newValues.size do
    rewriter := rewriter.replaceValue! (oldOp.getResult i) newValues[i]
  return rewriter.eraseOp! oldOp

end Fold.Impl

end Veir
