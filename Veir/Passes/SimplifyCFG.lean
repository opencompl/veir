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

/-- Replace a forwarded block argument with its incoming SSA value. -/
private def substituteArgument (block : BlockPtr) (arguments : Array ValuePtr)
    (value : ValuePtr) : ValuePtr :=
  match value with
  | .blockArgument arg =>
      if arg.block = block then arguments[arg.index]! else value
  | _ => value

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
    let nextArguments := (branch.getOperands! ctx).map (substituteArgument target' arguments')
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

/-- Explicit traversal frames keep the recursive driver transparent to proofs. -/
private inductive WorkItem where
  | operation (op : OperationPtr)
  | rewrite (op : OperationPtr)
  | region (region : RegionPtr)
  | blocks (block : BlockPtr)
  | operations (op : OperationPtr)

/-- Traverse in postorder, saving each next-operation pointer before rewriting
    its predecessor. `none` is the logical result of a nonterminating traversal. -/
private def runWorklist (ctx : WfIRContext OpCode) (pending : List WorkItem) :
    Option (Except String (WfIRContext OpCode)) :=
  match pending with
  | [] => some (.ok ctx)
  | .operation op :: rest =>
      runWorklist ctx
        ((op.getRegions! ctx.raw).toList.map .region ++ .rewrite op :: rest)
  | .rewrite op :: rest =>
      match simplifyBranch ctx op with
      | .ok ctx' => runWorklist ctx' rest
      | .error err => some (.error err)
  | .region region :: rest =>
      runWorklist ctx (((region.get! ctx.raw).firstBlock.toList.map .blocks) ++ rest)
  | .blocks block :: rest =>
      let body := block.get! ctx.raw
      runWorklist ctx (body.firstOp.toList.map .operations ++
        body.next.toList.map .blocks ++ rest)
  | .operations op :: rest =>
      runWorklist ctx (.operation op ::
        ((op.get! ctx.raw).next.toList.map .operations ++ rest))
partial_fixpoint

/-- Visit the pass root and its nested operations. Bypassed blocks remain in the
    region; this pass only forwards branches. -/
public def run (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (WfIRContext OpCode) :=
  (runWorklist ctx [.operation op]).getD (.error "nonterminating IR traversal")

end SimplifyCFG

public def SimplifyCFGPass : Pass OpCode :=
  { name := "simplifycfg"
    description := "Forward branches through blocks containing only a direct branch."
    run := fun _ ctx op _ => do
      match SimplifyCFG.run ctx op with
      | .ok ctx => pure ctx
      | .error err => throw err }

end Veir
