module

public import Veir.Analysis.DataFlow.Domains
public import Veir.Analysis.DataFlow.SparseAnalysis

public section

namespace Veir

namespace SparseConstantPropagation

instance : SparseFactSpec .sparseConstant ConstantDomain where
  payloadEq := rfl

variable [FactSpec .executable]

def kind : AnalysisKind :=
  .sparseConstantPropagation

/--
Set a sparse lattice element to the conservative entry state.
This mirrors MLIR's sparse constant propagation by joining in `unknown`.
-/
def setToEntryState
    (target : ValuePtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  SparseForwardDataFlowAnalysis.joinLatticeElement
    .sparseConstant target ConstantDomain.unknown dfCtx irCtx

/--
Join a new fact into the value's lattice state and propagate updates when it changes.
Bottom is kept sparse (no inserted map entry). This is because an anchor with no entry is by default bottom.
-/
def propagateConstant (target : ValuePtr) (constant : ConstantDomain)
    (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext :=
  SparseForwardDataFlowAnalysis.joinLatticeElement
    .sparseConstant target constant dfCtx irCtx

/-- Mark all provided SSA values as unknown (top). -/
def setAllToUnknownConstants (values : Array ValuePtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  SparseForwardDataFlowAnalysis.setAllToEntryStates setToEntryState values dfCtx irCtx

/-- Collect all result values of an operation as `ValuePtr.opResult`. -/
def opResults (op : OperationPtr) (irCtx : IRContext OpCode) : Array ValuePtr := Id.run do
  let mut values : Array ValuePtr := #[]
  for i in [0:op.getNumResults! irCtx] do
    values := values.push (ValuePtr.opResult (op.getResult i))
  values

/-- Recursively collect block arguments across a block list. -/
partial def blockArguments (block : BlockPtr) (irCtx : IRContext OpCode)
    (acc : Array ValuePtr := #[]) : Array ValuePtr := Id.run do
  let mut acc := acc
  for i in [0:block.getNumArguments! irCtx] do
    acc := acc.push (ValuePtr.blockArgument (block.getArgument i))
  match (block.get! irCtx).next with
  | some nextBlock =>
    blockArguments nextBlock irCtx acc
  | none =>
    acc

/-- Collect all arguments from every block in a region. -/
def regionArguments (region : RegionPtr) (irCtx : IRContext OpCode) : Array ValuePtr :=
  match (region.get! irCtx).firstBlock with
  | some firstBlock =>
    blockArguments firstBlock irCtx
  | none =>
    #[]

/-- Set all operation results and nested region block arguments to unknown (top). -/
def setOpAndRegionValuesToUnknown (op : OperationPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := setAllToUnknownConstants (opResults op irCtx) dfCtx irCtx
  for i in [0:op.getNumRegions! irCtx] do
    let region := op.getRegion! irCtx i
    dfCtx := setAllToUnknownConstants (regionArguments region irCtx) dfCtx irCtx
  dfCtx

/--
Fold a binary operation on known constants when bitwidths agree.
Returns `none` if widths mismatch or folding yields no value.
-/
def foldKnownBinary?
    (lhs rhs : KnownConstant)
    (f : {w : Nat} -> Data.LLVM.Int w -> Data.LLVM.Int w -> Option (Data.LLVM.Int w))
    : Option KnownConstant :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsValue := Data.LLVM.Int.cast rhs.value (Eq.symm h)
    match f lhs.value rhsValue with
    | some folded =>
      some { bitwidth := lhs.bitwidth, value := folded }
    | none =>
      none
  else
    none

/--
Try to fold a binary op from operand lattice facts.
Only folds when the op has exactly two operands and one result.
-/
def foldBinaryOp? (op : OperationPtr) (dfCtx : DataFlowContext) (irCtx : IRContext OpCode)
    (f : {w : Nat} -> Data.LLVM.Int w -> Data.LLVM.Int w -> Option (Data.LLVM.Int w))
    : Option ConstantDomain :=
  if op.getNumResults! irCtx == 0 then
    none
  else if op.getNumOperands! irCtx != 2 then
    none
  else
    let lhsValue := op.getOperand! irCtx 0
    let rhsValue := op.getOperand! irCtx 1
    match SparseFact.getElementD .sparseConstant dfCtx lhsValue .bottom,
        SparseFact.getElementD .sparseConstant dfCtx rhsValue .bottom with
    | ConstantDomain.constant lhs, ConstantDomain.constant rhs =>
      match foldKnownBinary? lhs rhs f with
      | some folded => some (.constant folded)
      | none => none
    | _, _ => none

/--
Sparse constant propagation transfer function.
- region operations conservatively force results to the entry state,
- uninitialized operands delay propagation,
- otherwise we try to fold and merge any discovered constant facts.
-/
def visitOperation
    (op : OperationPtr)
    (operands : Array ValuePtr)
    (results : Array ValuePtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Don't try to simulate the results of a region operation as we can't
  -- guarantee that folding will be out-of-place. We don't allow in-place
  -- folds as the desire here is for simulated execution, and not general
  -- folding.
  if op.getNumRegions! irCtx != 0 then
    return SparseForwardDataFlowAnalysis.setAllToEntryStates setToEntryState results dfCtx irCtx

  -- Wait until every operand lattice has been initialized before trying to
  -- infer a result.
  if operands.any (fun operand =>
    SparseFact.getElementD .sparseConstant dfCtx operand ConstantDomain.bottom 
      == ConstantDomain.bottom) 
  then return  dfCtx

  -- TODO: Mirror MLIR's generic `op->fold` path once Veir has an operation
  -- folder and fold-result representation. For now we manually handle the
  -- arithmetic ops. 
  match (op.get! irCtx).opType with
  | .arith .constant =>
    if h : results.size > 0 then
      -- Read the `arith.constant` and convert it into the lattice domain.
      let intAttr := (op.getProperties! irCtx (.arith .constant)).value
      let constant := ConstantDomain.ofInt intAttr.type.bitwidth intAttr.value
      propagateConstant (results[0]'h) constant dfCtx irCtx
    else
      dfCtx
  | .arith .addi =>
    let flags := op.getProperties! irCtx (.arith .addi)
    match foldBinaryOp? op dfCtx irCtx (fun lhs rhs =>
        match Data.LLVM.Int.add lhs rhs flags.nsw flags.nuw with
        | .val v => some (.val v)
        | .poison => none) with
    | some constant =>
      if h : results.size > 0 then
        propagateConstant (results[0]'h) constant dfCtx irCtx
      else
        dfCtx
    | none =>
      setAllToUnknownConstants results dfCtx irCtx
  | .arith .muli =>
    let flags := op.getProperties! irCtx (.arith .muli)
    match foldBinaryOp? op dfCtx irCtx (fun lhs rhs =>
        match Data.LLVM.Int.mul lhs rhs flags.nsw flags.nuw with
        | .val v => some (.val v)
        | .poison => none) with
    | some constant =>
      if h : results.size > 0 then
        propagateConstant (results[0]'h) constant dfCtx irCtx
      else
        dfCtx
    | none =>
      setAllToUnknownConstants results dfCtx irCtx
  | .arith .andi =>
    match foldBinaryOp? op dfCtx irCtx (fun lhs rhs =>
        match lhs, rhs with
        | .val lhs', .val rhs' => some (.val (BitVec.and lhs' rhs'))
        | _, _ => none) with
    | some constant =>
      if h : results.size > 0 then
        propagateConstant (results[0]'h) constant dfCtx irCtx
      else
        dfCtx
    | none =>
      setAllToUnknownConstants results dfCtx irCtx
  | .arith .subi =>
    let flags := op.getProperties! irCtx (.arith .subi)
    match foldBinaryOp? op dfCtx irCtx (fun lhs rhs =>
        match Data.LLVM.Int.sub lhs rhs flags.nsw flags.nuw with
        | .val v => some (.val v)
        | .poison => none) with
    | some constant =>
      if h : results.size > 0 then
        propagateConstant (results[0]'h) constant dfCtx irCtx
      else
        dfCtx
    | none =>
      setAllToUnknownConstants results dfCtx irCtx
  | _ =>
    setAllToUnknownConstants results dfCtx irCtx

end SparseConstantPropagation

def SparseConstantPropagationAnalysis [SparseFactSpec .sparseConstant ConstantDomain] [FactSpec .executable] : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    (Domain := ConstantDomain)
    SparseConstantPropagation.kind
    SparseConstantPropagation.visitOperation
    SparseConstantPropagation.setToEntryState

end Veir
