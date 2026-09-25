module

public import Veir.Pass
import Veir.Rewriter.WfRewriter
import Veir.Interfaces.ConstantLikeInterfaces
import Veir.Interfaces.ControlFlowInterfaces

/-!
# SimplifyCFG

Simplify the control-flow graph of every multi-block region:

1. A conditional branch whose condition operands are constants becomes an
   unconditional branch to the successor it would take.
2. An edge to a block containing only an unconditional branch is redirected to
   that branch's destination, substituting the bypassed block's arguments.
3. Blocks unreachable from their region's entry block are erased.
-/

namespace Veir
namespace SimplifyCFG

/-- The unconditional branch of the same dialect as a conditional branch. -/
private def unconditionalBranch? : OpCode → Option OpCode
  | .cf .cond_br => some (.cf .br)
  | .llvm .cond_br => some (.llvm .br)
  | .cir .brcond => some (.cir .br)
  | .riscv_cf .beqz | .riscv_cf .bnez | .riscv_cf .beq | .riscv_cf .bne
  | .riscv_cf .blt | .riscv_cf .bge | .riscv_cf .bltu | .riscv_cf .bgeu =>
      some (.riscv_cf .branch)
  | _ => none

/-- The operands forwarded to each successor of a supported branch. -/
private def successorOperands (ctx : IRContext OpCode) (op : OperationPtr) :
    Array (Array ValuePtr) :=
  (Array.range (op.getNumSuccessors! ctx)).map fun i =>
    (BranchOpInterface.getSuccessorOperands? op i ctx).get!.forwardedOperands

/-- Erase `op` and insert in its place a branch of type `opType` with the given
    leading operands, forwarding `forwarded[i]` to `successors[i]`. The new
    branch keeps `properties` and the old branch's discardable attributes. -/
private def replaceBranch (ctx : WfIRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (properties : Std.HashMap ByteArray Attribute) (fixed : Array ValuePtr)
    (successors : Array BlockPtr) (forwarded : Array (Array ValuePtr)) :
    Except String (WfIRContext OpCode) := do
  let mut properties := properties
  if fixed.size > 0 then
    let sizes := (Array.replicate fixed.size 1) ++ forwarded.map (Int.ofNat ·.size)
    properties := properties.insert "operandSegmentSizes".toUTF8
      (.denseArrayAttr { elementType := { bitwidth := 32 }, values := sizes })
  let newProperties ← Properties.fromAttrDict opType properties
  let some (ctx', replacement) := WfRewriter.createOp! ctx opType #[]
      (fixed ++ forwarded.flatten) successors #[] newProperties (some (.before op))
    | throw "simplifycfg: could not create branch"
  let ctx' := WfRewriter.setAttributes! ctx' replacement (op.get! ctx.raw).attrs
  return WfRewriter.eraseOp! ctx' op

/-- The index of the successor that a conditional branch takes, when its
    condition operands are all constants. Evaluate the branch with the
    interpreter, passing only the condition operands and placeholder
    successors so that the index is recovered even when both successors are the
    same block. Branches on poison are left alone. -/
private def constantSuccessor? (ctx : IRContext OpCode) (op : OperationPtr) : Option Nat := do
  let opType := op.getOpType! ctx
  let fixed ← BranchOpInterface.numFixedOperands? opType
  guard (fixed > 0)
  let conditions ← ((op.getOperands! ctx).extract 0 fixed).mapM (·.constantValue ctx)
  let placeholders := #[⟨0⟩, ⟨1⟩]
  match interpretOp' opType (op.getProperties! ctx opType) #[] conditions placeholders .empty with
  | .ok (_, _, some (.branch _ dest)) => placeholders.idxOf? dest
  | _ => none

/-- Replace a conditional branch on constants with an unconditional branch. -/
private def foldConstantBranch (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (Option (WfIRContext OpCode)) := do
  let some opType := unconditionalBranch? (op.getOpType! ctx.raw) | return none
  let some index := constantSuccessor? ctx.raw op | return none
  let forwarded := (successorOperands ctx.raw op)[index]!
  some <$> replaceBranch ctx op opType ∅ #[] #[op.getSuccessor! ctx.raw index] #[forwarded]

/-- The unconditional branch that is the only operation in `block`, provided
    that branch is the only user of the block's arguments. -/
private def forwardingBranch? (ctx : IRContext OpCode) (block : BlockPtr) :
    Option OperationPtr := do
  let body := block.get! ctx
  let branch ← body.firstOp
  guard (body.lastOp == some branch)
  guard (BranchOpInterface.numFixedOperands? (branch.getOpType! ctx) == some 0)
  for arg in block.getArguments! ctx do
    let mut use := arg.getFirstUse! ctx
    while let some operand := use do
      guard (operand.op == branch)
      use := (operand.get! ctx).nextUse
  return branch

/-- Follow a chain of forwarding blocks from `target`, which receives
    `arguments`. Return the first block that does not forward, along with the
    values it receives. A chain that cycles is left unchanged. -/
private def forward (ctx : IRContext OpCode) (target : BlockPtr)
    (arguments : Array ValuePtr) : BlockPtr × Array ValuePtr := Id.run do
  let mut target' := target
  let mut arguments' := arguments
  let mut visited : Std.HashSet BlockPtr := ∅
  while let some branch := forwardingBranch? ctx target' do
    if visited.contains target' then return (target, arguments)
    visited := visited.insert target'
    let substitute (value : ValuePtr) : ValuePtr :=
      match value with
      | .blockArgument arg => if arg.block == target' then arguments'[arg.index]! else value
      | _ => value
    arguments' := (branch.getOperands! ctx).map substitute
    target' := branch.getSuccessor! ctx 0
  return (target', arguments')

/-- Redirect each successor of a branch past any forwarding blocks. -/
private def forwardBranch (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (Option (WfIRContext OpCode)) := do
  let opType := op.getOpType! ctx.raw
  let some fixed := BranchOpInterface.numFixedOperands? opType | return none
  let successors := op.getSuccessors! ctx.raw
  let forwarded := successorOperands ctx.raw op
  let (newSuccessors, newForwarded) := (successors.zip forwarded).map
    (fun (target, arguments) => forward ctx.raw target arguments) |>.unzip
  if newSuccessors == successors && newForwarded == forwarded then return none
  let properties := Properties.toAttrDict opType (op.getProperties! ctx.raw opType)
  some <$> replaceBranch ctx op opType properties
    ((op.getOperands! ctx.raw).extract 0 fixed) newSuccessors newForwarded

/-- The blocks of a region, in order. -/
private def blocksOf (ctx : IRContext OpCode) (region : RegionPtr) : Array BlockPtr := Id.run do
  let mut blocks := #[]
  let mut block := (region.get! ctx).firstBlock
  while let some current := block do
    blocks := blocks.push current
    block := (current.get! ctx).next
  return blocks

/-- The operations of a block, in order. -/
private def opsOf (ctx : IRContext OpCode) (block : BlockPtr) : Array OperationPtr := Id.run do
  let mut ops := #[]
  let mut op := (block.get! ctx).firstOp
  while let some current := op do
    ops := ops.push current
    op := (current.get! ctx).next
  return ops

/-- The blocks of a region reachable from its entry block. -/
private def reachableBlocks (ctx : IRContext OpCode) (region : RegionPtr) :
    Std.HashSet BlockPtr := Id.run do
  let mut reached : Std.HashSet BlockPtr := ∅
  let mut worklist := (region.get! ctx).firstBlock.toArray
  while let some block := worklist.back? do
    worklist := worklist.pop
    if reached.contains block then continue
    reached := reached.insert block
    if let some terminator := (block.get! ctx).lastOp then
      worklist := worklist ++ terminator.getSuccessors! ctx
  return reached

/-- Order the operations of dead blocks so that each is erased only after all
    of its users. Return `none` when that is impossible: an operation has
    regions, or dead operations use each other's results cyclically, which the
    verifier allows in unreachable code. -/
private def erasureOrder? (ctx : IRContext OpCode) (deadOps : Array OperationPtr) :
    Option (Array OperationPtr) := Id.run do
  let dead := Std.HashSet.ofArray deadOps
  let mut remainingUses : Std.HashMap OperationPtr Nat := ∅
  for op in deadOps do
    let mut count := 0
    for result in op.getResults! ctx do
      let mut use := result.getFirstUse! ctx
      while let some operand := use do
        count := count + 1
        use := (operand.get! ctx).nextUse
    remainingUses := remainingUses.insert op count
  let mut ready := deadOps.filter (remainingUses[·]! == 0)
  let mut order := #[]
  while let some op := ready.back? do
    ready := ready.pop
    if op.getNumRegions! ctx != 0 then return none
    order := order.push op
    for operand in op.getOperands! ctx do
      let some definer := operand.definingOp? | continue
      if !dead.contains definer then continue
      let count := remainingUses[definer]! - 1
      remainingUses := remainingUses.insert definer count
      if count == 0 then ready := ready.push definer
  return if order.size == deadOps.size then some order else none

/-- Erase the blocks of `region` that are unreachable from its entry block.
    Their predecessors are all unreachable too, so once their operations are
    gone, nothing refers to them. -/
private def eraseDeadBlocks (ctx : WfIRContext OpCode) (region : RegionPtr) :
    Option (WfIRContext OpCode) := do
  let reachable := reachableBlocks ctx.raw region
  let dead := (blocksOf ctx.raw region).filter (!reachable.contains ·)
  guard (!dead.isEmpty)
  let order ← erasureOrder? ctx.raw (dead.flatMap (opsOf ctx.raw))
  let ctx := order.foldl WfRewriter.eraseOp! ctx
  return dead.foldl WfRewriter.detachBlock! ctx

/-- Simplify the control flow of one region until nothing changes. -/
private partial def simplifyRegion (ctx : WfIRContext OpCode) (region : RegionPtr) :
    Except String (WfIRContext OpCode) := do
  let mut ctx := ctx
  let mut changed := false
  for block in blocksOf ctx.raw region do
    let some terminator := (block.get! ctx.raw).lastOp | continue
    if let some ctx' ← foldConstantBranch ctx terminator then
      ctx := ctx'
      changed := true
  for block in blocksOf ctx.raw region do
    let some terminator := (block.get! ctx.raw).lastOp | continue
    if let some ctx' ← forwardBranch ctx terminator then
      ctx := ctx'
      changed := true
  if let some ctx' := eraseDeadBlocks ctx region then
    ctx := ctx'
    changed := true
  if changed then simplifyRegion ctx region else return ctx

/-- Simplify every region nested in `op`, innermost first. -/
public partial def run (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (WfIRContext OpCode) := do
  let mut ctx := ctx
  for region in op.getRegions! ctx.raw do
    for block in blocksOf ctx.raw region do
      for child in opsOf ctx.raw block do
        ctx ← run ctx child
    ctx ← simplifyRegion ctx region
  return ctx

end SimplifyCFG

public def SimplifyCFGPass : Pass OpCode :=
  { name := "simplifycfg"
    description := "Fold constant branches, forward branches through empty blocks, \
      and erase unreachable blocks."
    run := fun _ ctx op _ => do
      match SimplifyCFG.run ctx op with
      | .ok ctx => pure ctx
      | .error err => throw err }

end Veir
