import Veir.Fold
import Veir.PatternRewriter.Basic

/-!
  # Folding rewrites and constant materialization

  This module contains the mutating half of the folding infrastructure. Pure
  clients such as data-flow analyses should import `Veir.Fold` and call
  `foldDecision` or `foldDecisionForOp` instead.
-/

namespace Veir

/-- Preferred constant operation for ordinary integer results. Other result
    kinds, such as registers and modular integers, are materialized according
    to their result type. -/
inductive IntegerConstantDialect where
  | arith
  | llvm
deriving Inhabited, BEq, DecidableEq

/-- Select the conventional integer constant dialect for an operation. -/
def IntegerConstantDialect.forOp : OpCode → IntegerConstantDialect
  | .llvm _ => .llvm
  | _ => .arith

/--
  Materialize a runtime value as a constant-like operation at the given
  insertion point. Concrete integers use the requested ordinary integer
  dialect, except that modular integer result types use `mod_arith.constant`.
  Poison becomes `llvm.mlir.poison`, and register values become `riscv.li`.
-/
def PatternRewriter.materializeConstant! (rewriter : PatternRewriter OpCode)
    (rv : RuntimeValue) (resType : TypeAttr)
    (integerDialect : IntegerConstantDialect) (ip : InsertPoint)
    : Option (PatternRewriter OpCode × OperationPtr) :=
  match rv with
  | .int bw (.val v) =>
    match resType.val with
    | .modArithType mt =>
      let properties : ModArithConstantProperties :=
        { value := IntegerAttr.mk v.toNat mt.modulus.type }
      rewriter.createOp! (.mod_arith .constant) #[resType] #[] #[] #[] properties (some ip)
    | _ =>
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

/--
  Detached counterpart of `PatternRewriter.materializeConstant!`, for use by
  `LocalRewritePattern`s. The returned operation is not linked into a block.
-/
def WfRewriter.materializeConstant! (ctx : WfIRContext OpCode)
    (rv : RuntimeValue) (resType : TypeAttr)
    (integerDialect : IntegerConstantDialect)
    : Option (WfIRContext OpCode × OperationPtr) :=
  match rv with
  | .int bw (.val v) =>
    match resType.val with
    | .modArithType mt =>
      let properties : ModArithConstantProperties :=
        { value := IntegerAttr.mk v.toNat mt.modulus.type }
      WfRewriter.createOp! ctx (.mod_arith .constant) #[resType] #[] #[] #[] properties none
    | _ =>
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

/-- Replace all uses of the single result of `op` and erase `op`. -/
def PatternRewriter.replaceOpWithValue! {OpInfo : Type} [HasOpInfo OpInfo]
    (rewriter : PatternRewriter OpInfo)
    (op : OperationPtr) (newVal : ValuePtr) : PatternRewriter OpInfo :=
  let rewriter := rewriter.replaceValue! (op.getResult 0) newVal
  rewriter.eraseOp! op

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

/-- Rewrite-pattern wrapper around the pure folding decision. -/
def foldOperation (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite foldOperationLocal rewriter op opInBounds

/-- Create an operation at the insertion point unless it can be folded. -/
def PatternRewriter.createOrFoldOp! (rewriter : PatternRewriter OpCode) (opType : OpCode)
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
      match rewriter.materializeConstant! rv resultType (.forOp opType) insertionPoint with
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

/-- Create or fold an operation, replace `oldOp`, and erase it. -/
def PatternRewriter.createOrFoldAndReplaceOp! (rewriter : PatternRewriter OpCode)
    (oldOp : OperationPtr) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array ValuePtr) (properties : HasOpInfo.propertiesOf opType)
    (insertionPoint : InsertPoint) : Option (PatternRewriter OpCode) := do
  let (rewriter, newValues) ←
    rewriter.createOrFoldOp! opType resultTypes operands properties insertionPoint
  guard (oldOp.getNumResults! rewriter.ctx.raw == newValues.size)
  let mut rewriter := rewriter
  for h : i in 0...newValues.size do
    rewriter := rewriter.replaceValue! (oldOp.getResult i) newValues[i]
  return rewriter.eraseOp! oldOp

end Veir
