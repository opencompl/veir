module

public import Veir.Analysis.DataFlow.SparseFact
public import Veir.Interfaces.ControlFlowInterfaces

public section

namespace Veir

namespace SparseForwardDataFlowAnalysis

variable {kind : FactKind} {Domain : Type}

-- TODO: When this is verified, we will need something stronger than this for `Domain`
variable [Top Domain] [Bot Domain] [Join Domain] [DecidableEq Domain]

/--
The transfer function signature used for custom sparse analyses.

The framework handles operand subscriptions, invokes this hook with the current
operand lattice elements, and then joins any returned updates into the result
facts. Returning `none` for a result means the transfer contributes no new fact
for that result.
-/
abbrev VisitOperationFn (Domain : Type) :=
  OperationPtr -> Array Domain -> WfIRContext OpCode -> Array (Option Domain)

/--
Join a sparse lattice fact into the target value state and propagate updates
when it changes.

This is the generic sparse analysis primitive that merges an incoming lattice
element into the stored state for an SSA value.
-/
def joinAndPropagate
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (target : ValuePtr)
    (incoming : Domain)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  let oldValue := SparseFact.getElement kind target dfCtx
  let newValue := oldValue ⊔ incoming
  if newValue = oldValue then
    return dfCtx
  dfCtx.modifyFactAndPropagate kind (.ValuePtr target) 
    (SparseFact.setLatticeElement · newValue, true) irCtx

/-- Conservatively treat blocks as live when no liveness facts exist. -/
private def isBlockLive
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool :=
  let _ := block
  let _ := dfCtx
  let _ := irCtx
  true

/--
Conservatively treat CFG edges as live when dead code analysis is
not registered. Otherwise consult the liveness lattice, where points are
not live by default.
-/
private def isEdgeLive
    (edge : CFGEdge)
    (dfCtx : DataFlowContext)
    (_irCtx : WfIRContext OpCode) : Bool :=
  let _ := edge
  let _ := dfCtx
  true

/-- No-op when no liveness analysis is registered. -/
private def subscribeToBlockLiveness
    (analysisKind : AnalysisKind)
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext :=
  let _ := analysisKind
  let _ := block
  let _ := irCtx
  dfCtx

/-- No-op when no liveness analysis is registered. -/
private def subscribeToEdgeLiveness
    (analysisKind : AnalysisKind)
    (edge : CFGEdge)
    (dfCtx : DataFlowContext) : DataFlowContext :=
  let _ := analysisKind
  let _ := edge
  dfCtx

/--
Visit a block during sparse initialization.
-/
private def visitBlock
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  -- Exit early on blocks with no arguments.
  if block.getNumArguments! irCtx.raw = 0 then
    return dfCtx 

  -- If the block is not live, bail out.
  if !isBlockLive block dfCtx irCtx then
    return dfCtx

  let some parentRegion := (block.get! irCtx.raw).parent
    | return dfCtx

  -- The argument lattices of entry blocks are set by region control flow or
  -- the callgraph.
  if (parentRegion.get! irCtx.raw).firstBlock = some block then
    -- TODO: Mirror MLIR's handling of `visitCallableOperation` and
    -- `visitRegionSuccessors` and `visitNonControlFlowArgumentsImpl`
    -- for entry blocks.
    return dfCtx

  let mut dfCtx := dfCtx

  -- Iterate over the predecessors of the non-entry block.
  let mut maybePredUse := (block.get! irCtx.raw).firstUse

  while let some predUse := maybePredUse do
    let predUseStruct := predUse.get! irCtx.raw
    maybePredUse := predUseStruct.nextUse

    let predecessorOp := predUseStruct.owner
    let some predecessorBlock := (predecessorOp.get! irCtx.raw).parent
      | continue

    let edge : CFGEdge := { source := predecessorBlock, target := block }
    dfCtx := subscribeToEdgeLiveness analysisKind edge dfCtx

    -- If the edge from the predecessor block to the current block is not live,
    -- bail out.
    if !isEdgeLive edge dfCtx irCtx then
      continue

    -- Check if we can reason about the dataflow from the predecessor.
    if !(predecessorOp.getOpType! irCtx.raw).isTerminator then
      for target in block.getArguments! irCtx.raw do
        dfCtx := joinAndPropagate kind target ⊤ dfCtx irCtx
      return dfCtx

    let some successorOperands :=
        BranchOpInterface.getSuccessorOperands? predecessorOp predUse.index irCtx.raw
      | for target in block.getArguments! irCtx.raw do
          dfCtx := joinAndPropagate kind target ⊤ dfCtx irCtx
        return dfCtx

    for i in [0:block.getNumArguments! irCtx.raw] do
      let arg := block.getArgument i
      match successorOperands[i]? with
      | some operand =>
        -- Add the current block start program point as a dependency of the
        -- predecessor block's successor operand lattice state, so this block
        -- is revisited when that operand lattice changes.
        let dependentPoint := InsertPoint.atStart! block irCtx.raw
        let workItem : WorkItem := (dependentPoint, analysisKind)
        dfCtx := dfCtx.modifyFact kind (.ValuePtr operand) (fun state =>
          if state.dependents.any (fun dependent =>
              dependent.1 = dependentPoint && dependent.2 = analysisKind) then
            -- Do not add dependent again if it's already added.
            state
          else
            state.addDependent workItem)

        -- Call transfer function
        let incoming :=
          SparseFact.getElement kind operand dfCtx
        dfCtx := joinAndPropagate kind arg incoming dfCtx irCtx
      | none =>
        -- Conservatively consider internally produced arguments to be at the
        -- pessimistic sparse state.
        dfCtx := joinAndPropagate kind arg ⊤ dfCtx irCtx

  return dfCtx

mutual

/--
Ensure an operand has a sparse lattice state and subscribe the current sparse
analysis to its updates. This is what makes use-def driven revisitation work.
-/
partial def subscribeToOperand
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (operand : ValuePtr)
    (dfCtx : DataFlowContext) : DataFlowContext :=
  dfCtx.modifyFact kind (.ValuePtr operand) (fun state =>
    state.subscribe analysisKind)

/--
Visit one operation in the sparse analysis.
We first subscribe to operand lattices, then hand the operation and current
operand lattice elements to the user provided transfer function. The framework
applies any returned result updates itself.
-/
partial def visitOperation
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (visitOperationImpl : VisitOperationFn Domain)
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  -- Exit early on operations with no results.
  if op.getNumResults! irCtx.raw = 0 then
    return dfCtx

  -- If the containing block is not live, bail out. Liveness is by default
  -- unreachable until proven live, so a missing state is treated as dead.
  if let some parentBlock := (op.get! irCtx.raw).parent then
    if !isBlockLive parentBlock dfCtx irCtx then
      return dfCtx

  -- TODO: Mirror MLIR more closely by `visitRegionSuccessors`
  -- Comment: The results of a region branch operation are determined by control-flow.

  -- TODO: Mirror MLIR more closely by `visitCallOperation`

  let mut dfCtx := dfCtx
  for operand in op.getOperands! irCtx.raw do
    dfCtx := subscribeToOperand kind analysisKind operand dfCtx

  let operandLatticeElements := (op.getOperands! irCtx.raw).map (fun operand =>
    SparseFact.getElement kind operand dfCtx)
  let resultUpdates := visitOperationImpl op operandLatticeElements irCtx

  for (result, incoming?) in (op.getResults! irCtx.raw).zip resultUpdates do
    if let some incoming := incoming? then
      dfCtx := joinAndPropagate kind result incoming dfCtx irCtx
  return dfCtx

/--
Recursively initialize an operation tree for sparse analysis.
Visit the current operation first, then walk its nested regions, 
blocks, and nested operations.
-/
partial def initializeRecursively
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (visitOperationImpl : VisitOperationFn Domain)
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  -- Initialize the analysis by visiting every owner of an SSA value (all
  -- operations and blocks).
  let mut dfCtx := dfCtx
  dfCtx := visitOperation kind analysisKind visitOperationImpl op dfCtx irCtx

  for regionPtr in (op.get! irCtx.raw).regions do
    let region := regionPtr.get! irCtx.raw
    let mut maybeBlock := region.firstBlock

    while let some block := maybeBlock do
      dfCtx := subscribeToBlockLiveness analysisKind block dfCtx irCtx
      dfCtx := visitBlock kind analysisKind block dfCtx irCtx
      let mut maybeOp := (block.get! irCtx.raw).firstOp

      while let some nestedOp := maybeOp do
        dfCtx := initializeRecursively kind analysisKind visitOperationImpl nestedOp dfCtx irCtx
        maybeOp := (nestedOp.get! irCtx.raw).next

      maybeBlock := (block.get! irCtx.raw).next
  dfCtx

end

/--
Initialize the analysis by visiting every owner of an SSA value: all
operations and blocks.
-/
private def init
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (visitOperationImpl : VisitOperationFn Domain)
    (top : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  -- Mark the entry block arguments as having reached their pessimistic
  -- fixpoints.
  let mut dfCtx := dfCtx
  for regionPtr in (top.get! irCtx.raw).regions do
    let region := regionPtr.get! irCtx.raw
    if let some firstBlock := region.firstBlock then
      for arg in firstBlock.getArguments! irCtx.raw do
        dfCtx := joinAndPropagate kind arg ⊤ dfCtx irCtx

  initializeRecursively kind analysisKind visitOperationImpl top dfCtx irCtx

/--
Visit an insertion point. If this is at beginning of block and all
control flow predecessors or callsites are known, then the arguments'
lattices are propagated from them. If this is after call operation or an
operation with region control-flow, then its result lattices are set
accordingly. Otherwise, the operation transfer function is invoked.
-/
private def visit
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (visitOperationImpl : VisitOperationFn Domain)
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext :=
  match point.prev! irCtx.raw with
  | some prevOp =>
    visitOperation kind analysisKind visitOperationImpl prevOp dfCtx irCtx
  | none =>
    match point.block! irCtx.raw with
    | some block =>
      visitBlock kind analysisKind block dfCtx irCtx
    | none =>
      dfCtx

/--
Build a sparse forward analysis over one abstract value domain.

Sparse facts default to `⊥`. Whenever control flow or transfer functions lose
precision, the framework conservatively joins `⊤` into the affected values.
-/
def new
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (visitOperationImpl : VisitOperationFn Domain)
    : DataFlowAnalysis :=
  { kind := analysisKind
    init := init kind analysisKind visitOperationImpl
    visit := visit kind analysisKind visitOperationImpl }

end SparseForwardDataFlowAnalysis

end Veir
