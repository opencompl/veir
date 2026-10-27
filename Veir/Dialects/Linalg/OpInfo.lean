module

public import Veir.IR.OpInfo
public import Veir.Dialects.Linalg.Properties
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Linalg where
| generic
| yield
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Linalg.propertiesOf (op : Linalg) : Type :=
match op with
| .generic => LinalgGenericProperties
| .yield => Unit

def Linalg.fromAttrDict
    (op : Linalg) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Linalg.propertiesOf op) := by
  cases op
  case generic => exact LinalgGenericProperties.fromAttrDict attrDict
  case yield =>
    exact if attrDict.size > 0 then
      let plural := if attrDict.size = 1 then "property" else "properties"
      .error s!"linalg.yield: expected no properties, but got {attrDict.size} {plural}"
    else .ok ()

def Linalg.toAttrDict
    (op : Linalg) (props : Linalg.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .generic => props.toAttrDict
  | .yield => Std.HashMap.emptyWithCapacity 0

/-- `linalg` operations have no memory effects of their own, as in MLIR. -/
@[get_effects]
def Linalg.getEffects
    (_op : Linalg) (_props : Linalg.propertiesOf _op) : MemoryEffects :=
  .none

def Linalg.isConstantLike (_op : Linalg) : Bool :=
  false

def Linalg.hasSSADominance (_op : Linalg) (_index : Nat) : Bool :=
  true

@[is_terminator]
def Linalg.isTerminator (op : Linalg) : Bool :=
  match op with
  | .yield => true
  | .generic => false

#generate_dialect Linalg

instance : IsOpCode Linalg where
  fromName := Linalg.fromName
  name := Linalg.name
  propertiesOf := Linalg.propertiesOf
  fromAttrDict := Linalg.fromAttrDict
  toAttrDict := Linalg.toAttrDict

/--
  The shape and element type of a `linalg.generic` operand. A tensor is indexed by
  its shape and yields its elements; any other type is a scalar, which has rank 0
  and is passed to the body as is. As in MLIR, this includes vectors.
-/
def Linalg.operandShapeAndElementType (type : Attribute) : Array Nat × Attribute :=
  match type with
  | .tensorType tensor => (tensor.shape, tensor.elementType)
  | type => (#[], type)

/-- Verify a `linalg.generic` operation, following MLIR's `LinalgOp` verifier. -/
def Linalg.verifyGeneric {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo Linalg]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) :
    Except String PUnit := do
  let instrName := "linalg.generic"
  let props := op.getProperties! ctx.raw Linalg.generic
  let operandTypes := op.getOperandTypes! ctx.raw
  let segments ← op.verifyOperandSegmentSizes ctx opIn props.operandSegmentSizes 2
  let numInputs := segments[0]!
  -- This also checks that there is one indexing map per operand.
  let operands := operandTypes.map (Linalg.operandShapeAndElementType ·.val)
  props.verifyIndexingMaps (operands.map (·.1))
  if op.getNumSuccessors ctx.raw opIn ≠ 0 then
    throw s!"{instrName}: expected 0 successors"
  -- The outputs are tensors, and each one is returned as the result of the same type.
  let outputTypes := operandTypes.extract numInputs
  for h : i in [0:outputTypes.size] do
    let _ ← outputTypes[i].verifyTensorType
      s!"{instrName}: expected operand {numInputs + i} to be a tensor"
  let resultTypes := op.getResultTypes! ctx.raw
  if resultTypes.size ≠ outputTypes.size then
    throw s!"{instrName}: expected the number of tensor results ({resultTypes.size}) to be \
      equal to the number of output tensors ({outputTypes.size})"
  for h : i in [0:resultTypes.size] do
    if resultTypes[i].val ≠ outputTypes[i]!.val then
      throw s!"{instrName}: expected type of operand #{numInputs + i} \
        ({outputTypes[i]!}) to match type of corresponding result ({resultTypes[i]})"
  -- The body is a single block with one argument per operand, holding its element.
  let regionErr := s!"{instrName}: expects to have 1 region with 1 block"
  if op.getNumRegions ctx.raw opIn ≠ 1 then
    throw regionErr
  let block ← (op.getRegion! ctx.raw 0).getSingleBlock ctx regionErr
  if block.getNumArguments! ctx.raw ≠ operands.size then
    throw s!"{instrName}: expected as many non-induction variable region arguments as \
      the number of input/output operands"
  for h : i in [0:operands.size] do
    let argType := (block.getArgument i).getType! ctx.raw
    if argType.val ≠ operands[i].2 then
      throw s!"{instrName}: expected type of bb argument #{i} ({argType}) to match element \
        or self type of the corresponding operand ({operands[i].2})"
  -- The operands of the `linalg.yield` are checked by its own verifier.
  block.verifyImplicitTerminator ctx Linalg.yield

/--
  Verify a `linalg.yield` operation: it terminates the body of a `linalg.generic`
  and yields one element per output.
-/
def Linalg.verifyYield {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo Linalg]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) :
    Except String PUnit := do
  let instrName := "linalg.yield"
  op.verifyTerminatorCounts ctx opIn 0
  let some parent := op.getParentOp! ctx.raw
    | throw s!"{instrName}: expected the parent operation to be linalg.generic"
  if toDialect? Linalg (parent.getOpType! ctx.raw) ≠ some Linalg.generic then
    throw s!"{instrName}: expected the parent operation to be linalg.generic"
  -- The parent may be verified after this operation, so its segment sizes are not
  -- trusted, and its operands only as far as its indexing maps describe them.
  let props := parent.getProperties! ctx.raw Linalg.generic
  let outputTypes :=
    (parent.getOperandTypes! ctx.raw).extract props.numInputs props.indexingMaps.size
  let yieldTypes := op.getOperandTypes! ctx.raw
  if yieldTypes.size ≠ outputTypes.size then
    throw s!"{instrName}: expected {outputTypes.size} operand(s), one per output, \
      but found {yieldTypes.size}"
  for h : i in [0:yieldTypes.size] do
    let elementType := (Linalg.operandShapeAndElementType outputTypes[i]!.val).2
    if yieldTypes[i].val ≠ elementType then
      throw s!"{instrName}: expected operand {i} to have the output element type \
        {elementType}, but found {yieldTypes[i]}"

/-- Verify the local invariants of a `linalg` operation. -/
def Linalg.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Linalg] (opType : Linalg) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .generic => Linalg.verifyGeneric op ctx opIn
  | .yield => Linalg.verifyYield op ctx opIn

instance : HasOpInfo Linalg where
  verifyLocalInvariants := Linalg.verifyLocalInvariants
  getEffects := Linalg.getEffects
  isConstantLike := Linalg.isConstantLike
  hasSSADominance := Linalg.hasSSADominance
  isTerminator := Linalg.isTerminator

end
