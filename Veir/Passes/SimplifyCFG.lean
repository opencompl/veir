module

public import Veir.Pass
import Veir.Rewriter.WfRewriter

namespace Veir
namespace SimplifyCFG

/-- The operands preceding the successor arguments of the supported branches. -/
private def fixedOperandCount? : OpCode → Option Nat
  | .cf .br | .llvm .br | .cir .br | .riscv_cf .branch => some 0
  | .cf .cond_br | .llvm .cond_br | .cir .brcond
  | .riscv_cf .beqz | .riscv_cf .bnez => some 1
  | .riscv_cf .beq | .riscv_cf .bne | .riscv_cf .blt
  | .riscv_cf .bge | .riscv_cf .bltu | .riscv_cf .bgeu => some 2
  | _ => none

/-- Find a block containing only a direct branch. Arguments used outside that
    branch prevent bypassing the block: those uses still need its definitions. -/
private def forwardingBranch? (ctx : IRContext OpCode) (block : BlockPtr) :
    Option OperationPtr := do
  let body := block.get! ctx
  let branch ← body.firstOp
  guard (body.lastOp == some branch)
  guard (fixedOperandCount? (branch.getOpType! ctx) == some 0)
  for arg in block.getArguments! ctx do
    let mut use := arg.getFirstUse! ctx
    while let some operand := use do
      guard (operand.op == branch)
      use := (operand.get! ctx).nextUse
  return branch

/-- Follow an empty-block chain, substituting each block's incoming arguments.
    Leave cycles unchanged, including self-loops. -/
private def forward (ctx : IRContext OpCode) (target : BlockPtr)
    (arguments : Array ValuePtr) : BlockPtr × Array ValuePtr := Id.run do
  let mut target' := target
  let mut arguments' := arguments
  let mut visited : Std.HashSet BlockPtr := ∅
  while let some branch := forwardingBranch? ctx target' do
    if visited.contains target' then return (target, arguments)
    visited := visited.insert target'
    let nextArguments := (branch.getOperands! ctx).map fun value =>
      match value with
      | .blockArgument arg =>
          if arg.block == target' then arguments'[arg.index]! else value
      | _ => value
    target' := branch.getSuccessor! ctx 0
    arguments' := nextArguments
  return (target', arguments')

/-- Rebuild a branch with forwarded destinations and the corresponding operand
    segments, preserving its properties and attributes. -/
private def simplifyBranch (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (WfIRContext OpCode) := do
  let opType := op.getOpType! ctx.raw
  let some fixed := fixedOperandCount? opType | return ctx
  let operands := op.getOperands! ctx.raw
  let successors := op.getSuccessors! ctx.raw
  let mut properties := Properties.toAttrDict opType (op.getProperties! ctx.raw opType)
  let mut sizes : Array Int := #[]
  if fixed > 0 then
    let some (.denseArrayAttr segments) := properties["operandSegmentSizes".toUTF8]?
      | throw "branch has no operand segment sizes"
    sizes := segments.values
  let mut newOperands := operands.extract 0 fixed
  let mut newSuccessors := #[]
  let mut offset := fixed
  for i in [:successors.size] do
    let count := if fixed == 0 then operands.size else sizes[fixed + i]!.toNat
    let (target, arguments) := forward ctx.raw successors[i]!
      (operands.extract offset (offset + count))
    newSuccessors := newSuccessors.push target
    newOperands := newOperands ++ arguments
    if fixed > 0 then
      sizes := sizes.set! (fixed + i) (Int.ofNat arguments.size)
    offset := offset + count
  if newSuccessors == successors && newOperands == operands then return ctx
  if fixed > 0 then
    properties := properties.insert "operandSegmentSizes".toUTF8
      (.denseArrayAttr { elementType := { bitwidth := 32 }, values := sizes })
  let newProperties ← Properties.fromAttrDict opType properties
  let some (ctx', replacement) := WfRewriter.createOp! ctx opType #[] newOperands
    newSuccessors #[] newProperties (some (.before op))
    | throw "could not create forwarded branch"
  let ctx' := WfRewriter.setAttributes! ctx' replacement (op.get! ctx.raw).attrs
  return WfRewriter.eraseOp! ctx' op

/-- Visit the pass root and its nested operations. Bypassed blocks remain in the
    region; this pass only forwards branches. -/
public partial def run (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (WfIRContext OpCode) := do
  let mut ctx := ctx
  for region in op.getRegions! ctx.raw do
    let mut block := (region.get! ctx.raw).firstBlock
    while let some current := block do
      let mut inner := (current.get! ctx.raw).firstOp
      while let some child := inner do
        inner := (child.get! ctx.raw).next
        ctx ← run ctx child
      block := (current.get! ctx.raw).next
  simplifyBranch ctx op

end SimplifyCFG

public def SimplifyCFGPass : Pass OpCode :=
  { name := "simplifycfg"
    description := "Forward branches through blocks containing only a direct branch."
    run := fun _ ctx op _ => do
      match SimplifyCFG.run ctx op with
      | .ok ctx => pure ctx
      | .error err => throw err }

end Veir
