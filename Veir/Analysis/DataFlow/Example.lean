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

inductive ConstantValue where
  | top
  | bottom
  | constant (value : KnownConstant)
deriving BEq

def ConstantValue.unknown : ConstantValue :=
  .top

def ConstantValue.uninitialized : ConstantValue :=
  .bottom

def ConstantValue.ofInt (bitwidth : Nat) (value : Int) : ConstantValue :=
  .constant { bitwidth := bitwidth
              value := .val (BitVec.ofInt bitwidth value) }

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

def ConstantLatticeState.new (value : ValuePtr) (constant : ConstantValue) : AnalysisState :=
  AnalysisState.new
    ({ anchor := .ValuePtr value
       dependents := #[]
       useDefSubscribers := #[]
       value := constant } : ConstantLatticeState)

-- =============================================================================== --

-- ===================== Example `DataFlowAnalysis` Children ===================== --
namespace ConstantAnalysis

def getLatticeValue (dfCtx : DataFlowContext) (anchor : LatticeAnchor) : ConstantValue :=
  match dfCtx.getState? anchor ConstantLatticeState with
  | some state =>
    state.value
  | none =>
    if dfCtx.lattice[anchor]?.isSome then
      -- Another analysis owns this anchor in the current single-map representation.
      -- TODO: DataFlowContext.lattice should be a map of maps, where each map is for a specific type.
      -- FIX: Then we wouldn't have this issue!
      ConstantValue.top
    else
      ConstantValue.bottom

def fromOperationProperty (op : OperationPtr) (irCtx : IRContext OpCode) : ConstantValue :=
  let intAttr := (op.getProperties! irCtx .arith_constant).value
  ConstantValue.ofInt intAttr.type.bitwidth intAttr.value

def propagateConstant (value : ValuePtr) (constant : ConstantValue)
    (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let anchor : LatticeAnchor := .ValuePtr value
  let oldValue := getLatticeValue dfCtx anchor
  let joined := Join.join oldValue constant
  if joined == oldValue then
    dfCtx
  else
    match dfCtx.getState? anchor ConstantLatticeState with
    | some oldState =>
      let nextState : ConstantLatticeState := { oldState with value := joined }
      let state := AnalysisState.new nextState
      let mut dfCtx := { dfCtx with lattice := dfCtx.lattice.insert anchor state }
      dfCtx := state.onUpdate dfCtx irCtx
      dfCtx
    | none =>
      if dfCtx.lattice[anchor]?.isSome || joined == .bottom then
        -- Do not clobber another analysis entry; also keep bottom sparse.
        -- TODO: Like said previously, this should be handled by having DataFlowContext.lattice be a map of maps
        dfCtx
      else
        let state := ConstantLatticeState.new value joined
        let mut dfCtx := { dfCtx with lattice := dfCtx.lattice.insert anchor state }
        dfCtx := state.onUpdate dfCtx irCtx
        dfCtx

def setAllToUnknownConstants (values : Array ValuePtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  for value in values do
    dfCtx := propagateConstant value ConstantValue.unknown dfCtx irCtx
  dfCtx

def opResults (op : OperationPtr) (irCtx : IRContext OpCode) : Array ValuePtr := Id.run do
  let mut values : Array ValuePtr := #[]
  for i in [0:op.getNumResults! irCtx] do
    values := values.push (ValuePtr.opResult (op.getResult i))
  values

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

def regionArguments (region : RegionPtr) (irCtx : IRContext OpCode) : Array ValuePtr :=
  match (region.get! irCtx).firstBlock with
  | some firstBlock =>
    blockArguments firstBlock irCtx
  | none =>
    #[]

def setOpAndRegionValuesToUnknown (op : OperationPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := setAllToUnknownConstants (opResults op irCtx) dfCtx irCtx
  for i in [0:op.getNumRegions! irCtx] do
    let region := op.getRegion! irCtx i
    dfCtx := setAllToUnknownConstants (regionArguments region irCtx) dfCtx irCtx
  dfCtx

def getKnownConstant? (value : ValuePtr) (dfCtx : DataFlowContext) : Option KnownConstant := do
  let anchor : LatticeAnchor := .ValuePtr value
  match getLatticeValue dfCtx anchor with
  | .constant value =>
    some value
  | _ =>
    none

def foldKnownBinary?
    (lhs rhs : KnownConstant)
    (f : {w : Nat} -> Data.LLVM.Int w -> Data.LLVM.Int w -> Option (Data.LLVM.Int w))
    : Option KnownConstant :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsValue : Data.LLVM.Int lhs.bitwidth := Data.LLVM.Int.cast rhs.value (Eq.symm h)
    match f lhs.value rhsValue with
    | some folded =>
      some { bitwidth := lhs.bitwidth, value := folded }
    | none =>
      none
  else
    none

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

def visit (point : ProgramPoint) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  match point with
  | .OperationPtr op =>
    match (op.get! irCtx).opType with
    | .arith_constant =>
      if op.getNumResults! irCtx > 0 then
        propagateConstant (ValuePtr.opResult (op.getResult 0)) (fromOperationProperty op irCtx) dfCtx irCtx
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

def init (top : OperationPtr) (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext :=
  enqueueOpPostOrder top dfCtx irCtx

end ConstantAnalysis

def ConstantAnalysis :=
  DataFlowAnalysis.new
  ConstantAnalysis.init
  ConstantAnalysis.visit
-- =============================================================================== --

end Veir
