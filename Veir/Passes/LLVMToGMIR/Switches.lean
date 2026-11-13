module

public import Veir.Pass

namespace Veir

/-!
  Translate `llvm.switch` to a chain of `g_icmp` and `g_brcond`, at the same stage as
  LLVM's `IRTranslator::translateSwitch` and `lowerSwitchRangeWorkItem`. For now, each case
  is tested separately in source order, without clustering, profile ordering or jump tables.
  Comparisons keep the switch condition's type; the target legalizer widens them later.

  Unlike LLVM's `G_BRCOND`, VeIR's `g_brcond` carries both successors and their block arguments.
  Each case retains its own forwarded operands, even when several cases share a destination.
-/

/-- Replace a switch by equality tests followed by a branch to its default destination. -/
public def convertLLVMSwitch (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (WfIRContext OpCode) := do
  if op.getOpType! ctx.raw ≠ .llvm .switch then return ctx
  let props := op.getProperties! ctx.raw Llvm.switch
  let some cases := props.caseValues?
    | throw "llvm-to-gmir: cannot read switch case values"
  if op.getNumSuccessors! ctx.raw ≠ cases.size + 1 then
    throw "llvm-to-gmir: switch case values do not match its successors"
  let value := op.getOperand! ctx.raw 0
  let type := value.getType! ctx.raw
  let .integerType intType := type.val
    | throw "llvm-to-gmir: switch condition is not an integer"
  let defaultDest := op.getSuccessor! ctx.raw 0
  let some defaultArgs := BranchOpInterface.getSuccessorOperands? op 0 ctx.raw
    | throw "llvm-to-gmir: cannot read switch default operands"
  let defaultArgs := defaultArgs.forwardedOperands
  if cases.isEmpty then
    let some (ctx, _) := WfRewriter.createOp! ctx GMIR.g_br #[] defaultArgs
      #[defaultDest] #[] () (some (.before op))
      | throw "llvm-to-gmir: cannot create switch default branch"
    return WfRewriter.eraseOp! ctx op

  let some block := op.getParent! ctx.raw
    | throw "llvm-to-gmir: switch has no parent block"
  let some region := block.getParent! ctx.raw
    | throw "llvm-to-gmir: switch block has no parent region"
  -- Put the additional tests immediately after the original block, in chain order.
  let blockIP := match block.getNextBlock! ctx.raw with
    | some next => BlockInsertPoint.before next
    | none => BlockInsertPoint.atEnd region
  let mut ctx := ctx
  let mut ip := InsertPoint.before op
  for i in [:cases.size] do
    let dest := op.getSuccessor! ctx.raw (i + 1)
    let some args := BranchOpInterface.getSuccessorOperands? op (i + 1) ctx.raw
      | throw "llvm-to-gmir: cannot read switch case operands"
    let args := args.forwardedOperands
    let (ctx', next, nextArgs) := if i + 1 = cases.size then
        (ctx, defaultDest, defaultArgs)
      else
        let (ctx, next) := WfRewriter.createBlock! ctx #[] (some blockIP)
        (ctx, next, #[])
    ctx := ctx'
    let some (ctx', constant) := WfRewriter.createOp! ctx GMIR.g_constant #[type]
      #[] #[] #[] (GMIRConstantProperties.mk (.ofInt cases[i]! intType)) (some ip)
      | throw "llvm-to-gmir: cannot create switch case constant"
    let some (ctx', cmp) := WfRewriter.createOp! ctx' GMIR.g_icmp #[IntegerType.signless 1]
      #[value, constant.getResult 0] #[] #[] (IcmpProperties.mk .eq) (some ip)
      | throw "llvm-to-gmir: cannot create switch comparison"
    let branchProps : GMIRBrCondProperties :=
      { operandSegmentSizes :=
          { elementType := .signless 32, values := #[1, args.size, nextArgs.size] } }
    let some (ctx', _) := WfRewriter.createOp! ctx' GMIR.g_brcond #[]
      (#[↑(cmp.getResult 0)] ++ args ++ nextArgs) #[dest, next] #[] branchProps (some ip)
      | throw "llvm-to-gmir: cannot create switch conditional branch"
    ctx := ctx'
    ip := .atEnd next
  return WfRewriter.eraseOp! ctx op

/-- Visit the original operations once; the generated comparisons and branches are already gMIR. -/
public def convertLLVMSwitches (ctx : WfIRContext OpCode) : Except String (WfIRContext OpCode) :=
  ctx.raw.operations.keys.foldlM convertLLVMSwitch ctx

end Veir
