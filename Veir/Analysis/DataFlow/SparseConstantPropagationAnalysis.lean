module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Analysis.DataFlow.SparseAnalysis

public section

namespace Veir

namespace SparseConstantPropagation

instance : SparseFactSpec .sparseConstant AbstractConstant where
  payloadEq := rfl

def kind : AnalysisKind :=
  .sparseConstantPropagation

/--
Join a new fact into the value's lattice state and propagate updates when it changes.
Bottom is kept sparse (no inserted map entry). This is because an anchor with no entry is by default bottom.
-/
def propagateConstant (target : ValuePtr) (constant : AbstractConstant)
    (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext :=
  SparseForwardDataFlowAnalysis.joinLatticeElement
    .sparseConstant target constant dfCtx irCtx

/-- Mark all provided SSA values as unknown (top). -/
def setAllToUnknownConstants (values : Array ValuePtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  for value in values do
    dfCtx := SparseForwardDataFlowAnalysis.joinLatticeElement
      .sparseConstant value ⊤ dfCtx irCtx
  dfCtx

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
  Option.elim (block.get! irCtx).next acc (blockArguments · irCtx acc)

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
  for region in (op.get! irCtx).regions do
    dfCtx := setAllToUnknownConstants (regionArguments region irCtx) dfCtx irCtx
  dfCtx

/--
Fold a binary operation on known constants when bitwidths agree.
Returns `none` if widths mismatch or folding yields no value.
-/
def foldKnownBinary?
    (lhs rhs : ConcreteConstant)
    (f : {w : Nat} -> Data.LLVM.Int w -> Data.LLVM.Int w -> Option (Data.LLVM.Int w))
    : Option ConcreteConstant :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsValue := Data.LLVM.Int.cast rhs.value (Eq.symm h)
    f lhs.value rhsValue |> .map ({ bitwidth := lhs.bitwidth, value := · })
  else
    none

/--
Try to fold a binary op from operand lattice facts.
Only folds when the op has exactly two operands and one result.
-/
def foldBinaryOp? (op : OperationPtr) (dfCtx : DataFlowContext) (irCtx : IRContext OpCode)
    (f : {w : Nat} -> Data.LLVM.Int w -> Data.LLVM.Int w -> Option (Data.LLVM.Int w))
    : Option AbstractConstant :=
  if op.getNumResults! irCtx = 0 then
    none
  else if op.getNumOperands! irCtx ≠ 2 then
    none
  else
    let lhsValue := op.getOperand! irCtx 0
    let rhsValue := op.getOperand! irCtx 1
    match SparseFact.getElementD .sparseConstant lhsValue ⊥ dfCtx,
        SparseFact.getElementD .sparseConstant rhsValue ⊥ dfCtx with
    | AbstractConstant.constant lhs, AbstractConstant.constant rhs =>
      foldKnownBinary? lhs rhs f |> .map (.constant ·)
    | _, _ => none

/--
Sparse constant propagation transfer function.
- region operations conservatively force results to the entry state,
- uninitialized operands delay propagation,
- otherwise we try to fold and merge any discovered constant facts.
-/
def visitOperation
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let results := op.getResults! irCtx

  -- Don't try to simulate the results of a region operation as we can't
  -- guarantee that folding will be out-of-place. We don't allow in-place
  -- folds as the desire here is for simulated execution, and not general
  -- folding.
  if op.getNumRegions! irCtx ≠ 0 then
    return setAllToUnknownConstants results dfCtx irCtx

  -- Wait until every operand lattice has been initialized before trying to
  -- infer a result.
  if (op.getOperands! irCtx).any
      (fun operand => SparseFact.getElementD .sparseConstant operand ⊥ dfCtx = ⊥)
  then
    return dfCtx

  -- TODO: Mirror MLIR's generic `op->fold` path once Veir has an operation
  -- folder and fold-result representation. For now we manually handle the
  -- arithmetic ops. 
  match (op.get! irCtx).opType with
  | .arith .constant =>
    if h : results.size > 0 then
      -- Read the `arith.constant` and convert it into the lattice domain.
      let intAttr := (op.getProperties! irCtx (.arith .constant)).value
      let constant : AbstractConstant :=
        .constant ⟨intAttr.type.bitwidth, Data.LLVM.Int.constant intAttr.type.bitwidth intAttr.value⟩
      propagateConstant (results[0]'h) constant dfCtx irCtx
    else
      dfCtx
  | .arith .addi =>
    let flags := op.getProperties! irCtx (.arith .addi)
    match foldBinaryOp? op dfCtx irCtx (fun lhs rhs =>
        match Data.LLVM.Int.add lhs rhs flags.attr.nsw flags.attr.nuw with
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
        match Data.LLVM.Int.mul lhs rhs flags.attr.nsw flags.attr.nuw with
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
        match Data.LLVM.Int.sub lhs rhs flags.attr.nsw flags.attr.nuw with
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

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.kind
    SparseConstantPropagation.visitOperation

end Veir
