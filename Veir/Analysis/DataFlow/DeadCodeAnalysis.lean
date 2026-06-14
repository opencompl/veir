module

public import Veir.Analysis.DataFlowFramework
public import Veir.Analysis.DataFlow.SparseFact
public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Std.Data.HashSet

public section

namespace Veir

namespace ExecutableFact

def mkDefault : ExecutableFact :=
  { payload := { latticeElement := .dead } }

def propagate (state : ExecutableFact) (anchor : LatticeAnchor) 
  (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := { dfCtx with workList := state.enqueueDependents dfCtx.workList }
  match anchor with
  | .InsertPoint point =>
    -- Only deal with block start insertion points!
    if point.prev! irCtx ≠ none then
      panic! "Dead code propagate called on non block start insertion point"

    -- Reinvoke the analyses on the block itself
    for analysisKind in state.subscribers do
      dfCtx := dfCtx.enqueue (point, analysisKind)

    let some block := point.block! irCtx
      | panic! "Dead Code propagate: block start insertion point without block"

    -- Reinvoke analyses on all operations in the block
    for analysisKind in state.subscribers do
      let mut maybeOp := (block.get! irCtx).firstOp
      while h : maybeOp.isSome do
        let op := maybeOp.get h
        let some point := InsertPoint.after? op irCtx
          | panic! "Dead Code propagate: block operation without insertion point"
        dfCtx := dfCtx.enqueue (point, analysisKind)
        maybeOp := (op.get! irCtx).next
  | .CFGEdge edge =>
    for analysisKind in state.subscribers do
      dfCtx := dfCtx.enqueue (InsertPoint.atStart! edge.target irCtx, analysisKind)
  | _ => 
    pure ()
  dfCtx

instance : FactSpec .executable where
  mkDefault := ExecutableFact.mkDefault
  propagate := ExecutableFact.propagate

end ExecutableFact

namespace DeadCodeAnalysis

variable [FactSpec .executable] [SparseFactSpec .sparseConstant AbstractConstant]

def kind : AnalysisKind :=
  .deadCode

/--
Mark the CFG edge from `src` to `dst` as live.
This also marks the destination block entry point as live.
-/
def markEdgeLive
    (src : BlockPtr)
    (dst : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  let point := InsertPoint.atStart! dst irCtx
  dfCtx := dfCtx.modifyFactAndPropagate .executable (.InsertPoint point) (fun fact =>
    (fact.setToLive, !fact.live)) irCtx
  dfCtx := dfCtx.modifyFactAndPropagate .executable (.CFGEdge { source := src, target := dst }) (fun fact =>
    (fact.setToLive, !fact.live)) irCtx
  dfCtx

/-- Mark the entry blocks of all regions attached to `op` as live. -/
def markEntryBlocksLive
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  for regionPtr in (op.get! irCtx).regions do
    let region := regionPtr.get! irCtx
    if let some block := region.firstBlock then
      let point := InsertPoint.atStart! block irCtx
      dfCtx := dfCtx.modifyFactAndPropagate .executable (.InsertPoint point) (fun fact =>
        (fact.setToLive, !fact.live)) irCtx
  dfCtx

/-- 
Return whether the given operation is a branch op.
TODO: This function likely needs to be replaced with
an interface much like what MLIR has.
-/
private def isBranchOp
    (op : OperationPtr)
    (irCtx : IRContext OpCode) : Bool :=
  -- TODO: Replace this `.test .test` check once VeIR has proper branch ops.
  match (op.get! irCtx).opType with
  | .test .test => true
  | _ => false

/--
Read a literal constant directly from the defining operation when possible.
-/
private def getLiteralConstant?
    (value : ValuePtr)
    (irCtx : IRContext OpCode) : Option AbstractConstant :=
  match value with
  | .opResult result =>
    if result.index ≠ 0 then
      none
    else
      match (result.op.get! irCtx).opType with
      | .arith .constant =>
        let intAttr := (result.op.getProperties! irCtx (.arith .constant)).value
        some (.constant ⟨intAttr.type.bitwidth, Data.LLVM.Int.constant intAttr.type.bitwidth intAttr.value⟩)
      | _ =>
        none
  | .blockArgument _ =>
    none

/--
Get the constant domain lattice elements of the operands of an operation.
If sparse constant propagation is absent, unknown non-literal operands are treated
as `top` so dead code analysis acts conservative instead of marking all branches
as dead. When sparse constant propagation is registered but has not yet produced
lattice facts for at least one of the operands, return `none` to indicate that dead
code analysis should bail out until sparse constant propagation changes the facts.
When sparse constant propagation is registered, this function also subscribes dead
code analysis to the operand lattice facts so the branch is revisited when those
facts change.
-/
private def getOperandValues
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext × Option (Array AbstractConstant) := Id.run do
  let mut dfCtx := dfCtx
  let mut operands : Array AbstractConstant := #[]
  for operand in op.getOperands! irCtx do
    match getLiteralConstant? operand irCtx with
    | some literal =>
        operands := operands.push literal
    | none =>
      if !dfCtx.hasAnalysis .sparseConstantPropagation then
        operands := operands.push .top
      else
        dfCtx := dfCtx.modifyFact .sparseConstant (.ValuePtr operand) (fun fact =>
          fact.subscribe kind)
        let latticeElement :=
          SparseFact.getElementD .sparseConstant operand ⊥ dfCtx
        if latticeElement == AbstractConstant.bottom then
          return (dfCtx, none)
        operands := operands.push latticeElement
  (dfCtx, some operands)

/--
Returns the successor that would be chosen with the given constant operands.
Returns `none` if a single successor could not be chosen.

TODO: Replace this once VeIR supports branch operators! For now, we treat
`.test .test` as a branch operator with the following semantics:
- one successor: always take it
- two successors: inspect the first operand as a boolean-like integer,
  taking successor 0 when nonzero and successor 1 when zero
- otherwise: unknown
-/
private def getSuccessorForOperands?
    (op : OperationPtr)
    (operands : Array AbstractConstant)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  if op.getNumSuccessors! irCtx = 1 then
    some (op.getSuccessor! irCtx 0)
  else if op.getNumSuccessors! irCtx = 2 then
    match operands[0]? with
    | some (AbstractConstant.constant constant) =>
      match constant.value with
      | Data.LLVM.Int.val value =>
        if value = 0 then
          some (op.getSuccessor! irCtx 1)
        else
          some (op.getSuccessor! irCtx 0)
      | Data.LLVM.Int.poison =>
        none
    | _ =>
      none
  else
    none

def visitBranchOperation
    (branch : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Try to deduce a single successor for the branch.
  let (dfCtx, operands?) := getOperandValues branch dfCtx irCtx
  let some operands := operands?
    | return dfCtx
  let some parentBlock := (branch.get! irCtx).parent
    | return dfCtx

  match getSuccessorForOperands? branch operands irCtx with
  | some successor =>
    markEdgeLive parentBlock successor dfCtx irCtx
  | none =>
    let mut dfCtx := dfCtx
    for successor in branch.getSuccessors! irCtx do
      dfCtx := markEdgeLive parentBlock successor dfCtx irCtx
    dfCtx

private def visitOp
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- If the parent block is not executable, there is nothing to do.
  if hParent : (op.get! irCtx).parent.isSome then
    let parentBlock := (op.get! irCtx).parent.get hParent
    let blockPoint := InsertPoint.atStart! parentBlock irCtx
    match dfCtx.getFact? .executable (.InsertPoint blockPoint) with
    | some executableFact =>
      -- If parent block not live, skip op.
      if !executableFact.live then
        return dfCtx
    -- Liveness is false by default, so also return here as the parent block is
    -- not executable.
    | none =>
      return dfCtx

  let mut dfCtx := dfCtx

  -- TODO: If we have a live call op, add this as a live predecessor of the callee.

  if op.getNumRegions! irCtx ≠ 0 then
    -- TODO: Check if we can reason about region control-flow.

    -- TODO: Check if this is a callable operation and use callsite information
    -- to decide whether to mark the callable executable.

    -- else:
    dfCtx := markEntryBlocksLive op dfCtx irCtx

  -- TODO: If `op` is a region or callable return, visit the corresponding
  -- terminator semantics once VeIR has the necessary interfaces.

  if op.getNumSuccessors! irCtx ≠ 0 then
    if hParent : (op.get! irCtx).parent.isSome then
      let parentBlock := (op.get! irCtx).parent.get hParent

      -- Check if we can reason about the control-flow.
      if isBranchOp op irCtx then
        dfCtx := visitBranchOperation op dfCtx irCtx
      else
        -- Conservatively mark all successors as executable.
        for successor in op.getSuccessors! irCtx do
          dfCtx := markEdgeLive parentBlock successor dfCtx irCtx
    else
      -- TODO: Handle standalone operations with successors if VeIR ever models them.
      pure ()

  dfCtx

def visit
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  if point.prev! irCtx = none then
    return dfCtx

  visitOp ((point.prev! irCtx).get!) dfCtx irCtx

/--
Recursively initialize the analysis on nested regions.
Visit operations that may affect control-flow, subscribe them to parent-block
liveness, then recurse into nested regions.
-/
partial def initializeRecursively
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx

  -- Initialize the analysis by visiting every op with control-flow semantics.
  if op.getNumRegions! irCtx ≠ 0 || op.getNumSuccessors! irCtx ≠ 0 then
    -- TODO: || isRegionOrCallableReturn op || isACallOpInterface op

    -- When the liveness of the parent block changes, make sure to re-invoke
    -- the analysis on the op.
    if h : (op.get! irCtx).parent.isSome then
      let parentBlock := (op.get! irCtx).parent.get h
      let blockPoint := InsertPoint.atStart! parentBlock irCtx
      dfCtx := dfCtx.modifyFact .executable (.InsertPoint blockPoint) (fun fact =>
        fact.subscribe kind)

    -- Visit the op.
    dfCtx := visitOp op dfCtx irCtx

  -- Recurse on nested operations.
  for regionPtr in (op.get! irCtx).regions do
    -- TODO: If we haven't seen a symbol table yet, check if the current
    -- operation has one. If so, update the flag to allow for resolving
    -- callables in nested regions.
    let region := regionPtr.get! irCtx
    let mut maybeBlock := region.firstBlock
    while let some block := maybeBlock do
      let mut maybeOp := (block.get! irCtx).firstOp
      while let some nestedOp := maybeOp do
        dfCtx := initializeRecursively nestedOp dfCtx irCtx
        maybeOp := (nestedOp.get! irCtx).next
      maybeBlock := (block.get! irCtx).next
  dfCtx

def init
    (top : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Mark the top level blocks as executable.
  let dfCtx := markEntryBlocksLive top dfCtx irCtx

  -- TODO: Mark as overdefined the predecessors of symbol callables with
  -- potentially unknown predecessors.

  initializeRecursively top dfCtx irCtx

end DeadCodeAnalysis

def DeadCodeAnalysis [FactSpec .executable] [SparseFactSpec .sparseConstant AbstractConstant] : DataFlowAnalysis :=
  { kind := DeadCodeAnalysis.kind
    init := DeadCodeAnalysis.init
    visit := DeadCodeAnalysis.visit }

end Veir
