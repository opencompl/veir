module

public import Veir.Analysis.DataFlowFramework
public import Veir.Data.LLVM.Int.Basic

public section

namespace Veir

class Join (α : Type) where
  join : α -> α -> α

class Meet (α : Type) where
  meet : α -> α -> α

structure KnownConstant where
  bitwidth : Nat
  value : Data.LLVM.Int bitwidth
deriving BEq

-- Constant domain (this is the lattice element for this domain)
inductive ConstantValue where
  | top
  | bottom
  | constant (value : KnownConstant)
deriving BEq

/-- Alias for the top element: value is unknown or conflicting. -/
def ConstantValue.unknown : ConstantValue :=
  .top
/-- Alias for the bottom element: no information has been learned yet. -/
def ConstantValue.uninitialized : ConstantValue :=
  .bottom

/-- Build a constant lattice element from an integer at the given bitwidth. -/
def ConstantValue.ofInt (bitwidth : Nat) (value : Int) : ConstantValue :=
  .constant { bitwidth := bitwidth
              value := .val (BitVec.ofInt bitwidth value) }

-- For this analysis, only join is relevant.
instance : Join ConstantValue where
  join (lhs rhs : ConstantValue) : ConstantValue :=
    match lhs, rhs with
    | .bottom, x => x
    | x, .bottom => x
    | .top, _ => .top
    | _, .top => .top
    | .constant lhsVal, .constant rhsVal =>
      if lhsVal == rhsVal then
        .constant lhsVal
      else
        .top

-- ====================== Example `AnalysisState` Children ======================= --
structure AbstractSparseLatticeState extends BaseAnalysisState where
  useDefSubscribers : Array DataFlowAnalysis

/--
When the lattice gets updated, propagate an update to users of the value
using its use-def chain to subscribed analyses.
-/
instance : Update AbstractSparseLatticeState DataFlowContext where
  onUpdate (state : AbstractSparseLatticeState) (dfCtx : DataFlowContext)
      (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
    let mut dfCtx := { dfCtx with workList := state.onUpdate dfCtx }
    match state.anchor with
    | .ValuePtr value =>
      let mut maybeUse := value.getFirstUse! irCtx
      while h : maybeUse.isSome do
        let use := maybeUse.get h
        let user := (use.get! irCtx).owner
        for analysis in state.useDefSubscribers do
          dfCtx := { dfCtx with workList := dfCtx.workList.enqueue (.OperationPtr user, analysis) }
        maybeUse := (use.get! irCtx).nextUse
    | _ =>
      pure ()
    dfCtx

structure ConstantLatticeState extends AbstractSparseLatticeState where
  value : ConstantValue
deriving TypeName

instance : Update ConstantLatticeState DataFlowContext where
  onUpdate state dfCtx irCtx :=
    Update.onUpdate
      state.toAbstractSparseLatticeState
      dfCtx
      irCtx

/-- Create a new typed analysis state for a value anchor. -/
def ConstantLatticeState.new (value : ValuePtr) (constant : ConstantValue) : AnalysisState :=
  AnalysisState.new
    ({ anchor := .ValuePtr value
       dependents := #[]
       useDefSubscribers := #[]
       value := constant } : ConstantLatticeState)

-- =============================================================================== --

-- ===================== Example `DataFlowAnalysis` Children ===================== --
namespace ConstantAnalysis

/-- 
Get the lattice element at the specified anchor
Note, if there is no state at the specified anchor, the default is bottom!
-/
def getLatticeValue (dfCtx : DataFlowContext) (anchor : LatticeAnchor) : ConstantValue :=
  match dfCtx.getState? anchor ConstantLatticeState with
  | some state =>
    state.value
  | none =>
    ConstantValue.bottom

/--
Join a new fact into the value's lattice state and propagate updates when it changes.
Bottom is kept sparse (no inserted map entry). This is because an anchor with no entry is by default bottom.
-/
def propagateConstant (value : ValuePtr) (constant : ConstantValue)
    (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let anchor : LatticeAnchor := .ValuePtr value
  let oldValue := getLatticeValue dfCtx anchor
  let newValue := Join.join oldValue constant
  -- No change
  if newValue == oldValue then
    dfCtx
  -- Join result updates the lattice element
  else
    let state := match dfCtx.getState? anchor ConstantLatticeState with
    | some oldState => AnalysisState.new { oldState with value := newValue } 
    | none => ConstantLatticeState.new value newValue
    let mut dfCtx := dfCtx.insertState anchor state
    dfCtx := state.onUpdate dfCtx irCtx
    dfCtx

/-- Mark all provided SSA values as unknown (top). -/
def setAllToUnknownConstants (values : Array ValuePtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  for value in values do
    dfCtx := propagateConstant value ConstantValue.unknown dfCtx irCtx
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

/-- Get a constant for a value if one is known in the lattice. -/
def getKnownConstant? (value : ValuePtr) (dfCtx : DataFlowContext) : Option KnownConstant := do
  let anchor : LatticeAnchor := .ValuePtr value
  match getLatticeValue dfCtx anchor with
  | .constant value =>
    some value
  | _ =>
    none

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
    : Option ConstantValue :=
  if op.getNumResults! irCtx == 0 then
    none
  else if op.getNumOperands! irCtx != 2 then
    none
  else
    let lhsValue := op.getOperand! irCtx 0
    let rhsValue := op.getOperand! irCtx 1
    match getKnownConstant? lhsValue dfCtx, getKnownConstant? rhsValue dfCtx with
    | some lhs, some rhs =>
      match foldKnownBinary? lhs rhs f with
      | some folded => some (.constant folded)
      | none => none
    | _, _ => none

/--
Transfer function for constant propagation.
Known foldable ops propagate constants; otherwise outputs/region args become unknown.
-/
def visit (point : ProgramPoint) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  match point with
  | .OperationPtr op =>
    match (op.get! irCtx).opType with
    | .arith_constant =>
      if op.getNumResults! irCtx > 0 then
        -- Read the `arith.constant` attribute and convert it into the lattice domain.
        -- Then propagate it
        let intAttr := (op.getProperties! irCtx .arith_constant).value
        let constant := ConstantValue.ofInt intAttr.type.bitwidth intAttr.value
        propagateConstant (ValuePtr.opResult (op.getResult 0)) constant dfCtx irCtx
      else
        dfCtx
    | .arith_addi =>
      let flags := op.getProperties! irCtx .arith_addi
      match foldBinaryOp? op dfCtx irCtx (fun lhs rhs =>
          match Data.LLVM.Int.add lhs rhs flags.nsw flags.nuw with
          | .val v => some (.val v)
          | .poison => none) with
      | some constant =>
        propagateConstant (ValuePtr.opResult (op.getResult 0)) constant dfCtx irCtx
      | none =>
        setOpAndRegionValuesToUnknown op dfCtx irCtx
    | .arith_muli =>
      let flags := op.getProperties! irCtx .arith_muli
      match foldBinaryOp? op dfCtx irCtx (fun lhs rhs =>
          match Data.LLVM.Int.mul lhs rhs flags.nsw flags.nuw with
          | .val v => some (.val v)
          | .poison => none) with
      | some constant =>
        propagateConstant (ValuePtr.opResult (op.getResult 0)) constant dfCtx irCtx
      | none =>
        setOpAndRegionValuesToUnknown op dfCtx irCtx
    | .arith_andi =>
      match foldBinaryOp? op dfCtx irCtx (fun lhs rhs =>
          match lhs, rhs with
          | .val lhs', .val rhs' => some (.val (BitVec.and lhs' rhs'))
          | _, _ => none) with
      | some constant =>
        propagateConstant (ValuePtr.opResult (op.getResult 0)) constant dfCtx irCtx
      | none =>
        setOpAndRegionValuesToUnknown op dfCtx irCtx
    | .arith_subi =>
      let flags := op.getProperties! irCtx .arith_subi
      match foldBinaryOp? op dfCtx irCtx (fun lhs rhs =>
          match Data.LLVM.Int.sub lhs rhs flags.nsw flags.nuw with
          | .val v => some (.val v)
          | .poison => none) with
      | some constant =>
        propagateConstant (ValuePtr.opResult (op.getResult 0)) constant dfCtx irCtx
      | none =>
        setOpAndRegionValuesToUnknown op dfCtx irCtx
    | _ =>
      setOpAndRegionValuesToUnknown op dfCtx irCtx

-- Enqueue one operation after recursively enqueueing everything nested in its regions.
mutual
/-- Post-order traversal helper: visit nested regions before the current operation. -/
partial def enqueueOpPostOrder
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  for i in [0:op.getNumRegions! irCtx] do
    let region := (op.getRegion! irCtx i).get! irCtx
    if h : region.firstBlock.isSome then
      let firstBlock := region.firstBlock.get h
      dfCtx := enqueueBlockList firstBlock dfCtx irCtx
  visit (.OperationPtr op) dfCtx irCtx

/-- Traverse sibling operations in a block list. -/
partial def enqueueOpList
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  let dfCtx := enqueueOpPostOrder op dfCtx irCtx
  if h : (op.get! irCtx).next.isSome then
    let nextOp := (op.get! irCtx).next.get h
    enqueueOpList nextOp dfCtx irCtx
  else
    dfCtx

/-- Traverse sibling blocks and enqueue each block's operation list. -/
partial def enqueueBlockList
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  let dfCtx :=
    if h : (block.get! irCtx).firstOp.isSome then
      let firstOp := (block.get! irCtx).firstOp.get h
      enqueueOpList firstOp dfCtx irCtx
    else
      dfCtx
  if h : (block.get! irCtx).next.isSome then
    let nextBlock := (block.get! irCtx).next.get h
    enqueueBlockList nextBlock dfCtx irCtx
  else
    dfCtx

end

/-- Analysis initialization: seed the solver by traversing from the top op. -/
def init (top : OperationPtr) (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext :=
  enqueueOpPostOrder top dfCtx irCtx

end ConstantAnalysis

/-- Pack the constant analysis transfer/init functions into a `DataFlowAnalysis`. -/
def ConstantAnalysis :=
  DataFlowAnalysis.new
  ConstantAnalysis.init
  ConstantAnalysis.visit
-- =============================================================================== --

end Veir
