module

public import Veir.Pass

namespace Veir

/-!
  Translate `llvm.switch` to a chain of `g_icmp` and `g_brcond`, as LLVM's
  `IRTranslator::translateSwitch` and `lowerSwitchWorkItem` do at `-O0`: the cases are sorted
  by signed value (`sortAndRangeify`) and then tested one at a time, without jump tables, bit
  tests, binary trees, or profile ordering. These are all things we should implement
  as optimizations!
-/

public def convertLLVMSwitch (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode) := do
  if op.getOpType! ctx.raw ≠ .llvm .switch then return ctx
  let props := op.getProperties! ctx.raw Llvm.switch
  let value := op.getOperand! ctx.raw 0
  let type := value.getType! ctx.raw
  let .integerType intType := type.val | none
  let defaultDest := op.getSuccessor! ctx.raw 0
  let defaultArgs := (← BranchOpInterface.getSuccessorOperands? op 0 ctx.raw).forwardedOperands
  let cases := (← props.caseValues? intType.bitwidth).values.mapIdx fun i v =>
    ((BitVec.ofInt intType.bitwidth v).toInt, i + 1)
  let cases := cases.qsort (·.1 < ·.1)
  if cases.isEmpty then
    let (ctx, _) ← WfRewriter.createOp! ctx GMIR.g_br #[] defaultArgs
      #[defaultDest] #[] () (some (.before op))
    return WfRewriter.eraseOp! ctx op

  let block ← op.getParent! ctx.raw
  let region ← block.getParent! ctx.raw
  let blockIP := match block.getNextBlock! ctx.raw with
    | some next => BlockInsertPoint.before next
    | none => BlockInsertPoint.atEnd region
  let mut ctx := ctx
  let mut ip := InsertPoint.before op
  for h : i in [:cases.size] do
    let (caseValue, succIndex) := cases[i]
    let dest := op.getSuccessor! ctx.raw succIndex
    let args := (← BranchOpInterface.getSuccessorOperands? op succIndex ctx.raw).forwardedOperands
    let isLast := i + 1 = cases.size
    let (ctx', next, nextArgs) := if isLast then
        (ctx, defaultDest, defaultArgs)
      else
        let (ctx, next) := WfRewriter.createBlock! ctx #[] (some blockIP)
        (ctx, next, #[])
    let (ctx', constant) ← WfRewriter.createOp! ctx' GMIR.g_constant #[type]
      #[] #[] #[] (GMIRConstantProperties.mk (.ofInt caseValue intType)) (some ip)
    let (ctx', cmp) ← WfRewriter.createOp! ctx' GMIR.g_icmp #[IntegerType.signless 1]
      #[value, constant.getResult 0] #[] #[] (IcmpProperties.mk .eq) (some ip)
    let branchProps : GMIRBrCondProperties :=
      { operandSegmentSizes :=
          { elementType := .signless 32, values := #[1, args.size, nextArgs.size] } }
    let (ctx', _) ← WfRewriter.createOp! ctx' GMIR.g_brcond #[]
      (#[↑(cmp.getResult 0)] ++ args ++ nextArgs) #[dest, next] #[] branchProps (some ip)
    ctx := ctx'
    if !isLast then ip := .atEnd next
  return WfRewriter.eraseOp! ctx op

public def convertLLVMSwitches (ctx : WfIRContext OpCode) : Except String (WfIRContext OpCode) :=
  match ctx.raw.operations.keys.foldlM convertLLVMSwitch ctx with
  | some ctx => .ok ctx
  | none => .error "llvm-to-gmir: cannot translate a switch"

end Veir
