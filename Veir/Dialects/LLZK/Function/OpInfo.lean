module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Function.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes, dialect_name "function"]
inductive Function_ where
| «def»
| return
| call
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Function_.propertiesOf (op : Function_) : Type :=
match op with
| .«def» => FunctionDefProperties
| .return => Unit
| .call => FunctionCallProperties

/-- Reject properties on an operation whose schema has none. -/
private def noProperties (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Unit :=
  if attrDict.size > 0 then
    let plural := if attrDict.size = 1 then "property" else "properties"
    .error s!"{opName}: expected no properties, but got {attrDict.size} {plural}"
  else
    .ok ()

def Function_.fromAttrDict
    (op : Function_) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Function_.propertiesOf op) :=
  match op with
  | .«def» => FunctionDefProperties.fromAttrDict attrDict
  | .return => noProperties "function.return" attrDict
  | .call => FunctionCallProperties.fromAttrDict attrDict

def Function_.toAttrDict
    (op : Function_) (props : Function_.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .«def» => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)
    dict := dict.insert "function_type".toUTF8 (Attribute.functionType props.function_type)
    dict
  | .return => Std.HashMap.emptyWithCapacity 0
  | .call => props.toAttrDict

/--
`function.call` is reported with unknown effects: the callee may be a
`constrain` function (whose emitted constraints must not be DCE'd away)
or a `compute` function writing struct members.
-/
@[get_effects]
def Function_.getEffects
    (op : Function_) (_props : Function_.propertiesOf op) : MemoryEffects :=
  match op with
  | .call => .unknown
  | _ => .none

def Function_.isConstantLike (_op : Function_) : Bool := false

/-- A `function.def` body cannot reference SSA values from enclosing regions. -/
def Function_.isIsolatedFromAbove (op : Function_) : Bool :=
  match op with
  | .«def» => true
  | _ => false

def Function_.hasSSADominance (_op : Function_) (_index : Nat) : Bool :=
  true

@[is_terminator]
def Function_.isTerminator (op : Function_) : Bool :=
  match op with
  | .return => true
  | .«def» | .call => false

#generate_dialect Function_

instance : IsOpCode Function_ where
  fromName := Function_.fromName
  name := Function_.name
  propertiesOf := Function_.propertiesOf
  fromAttrDict := Function_.fromAttrDict
  toAttrDict := Function_.toAttrDict

def Function_.functionInterface? (op : Function_) :
    Option (FunctionOpInterface (Function_.propertiesOf op)) :=
  match op with
  | .«def» =>
    some
      { getSymName := fun props => props.sym_name
        getFunctionType := fun props => props.function_type
        setFunctionType := fun props functionType =>
          { props with function_type := functionType } }
  | .return | .call => none

/-- Check that `function.return` matches its enclosing `function.def` result types. -/
def OperationPtr.verifyLLZKFunctionReturnTypes {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Function_] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let funcOp ← op.getEnclosingFunctionOp ctx "function.return"
  let some .«def» := toDialect? Function_ (funcOp.getOpType! ctx.raw)
    | throw "Expected function.return to be enclosed by function.def"
  let props : Function_.propertiesOf .«def» :=
    funcOp.getProperties! ctx.raw Function_.«def»
  let outputs := props.function_type.outputs
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected function.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if !Attribute.branchArgCompatible (opTypes[i]!).val outputs[i]! then
      throw s!"function.return operand {i} type does not match the function's declared result type"

def Function_.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Function_] (opType : Function_) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .«def» => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "function.def: Expected 0 operand(s)"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "function.def: Expected 0 result(s)"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "function.def: Expected 1 region (the function body)"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "function.def: Expected 0 successors"
    let props : Function_.propertiesOf .«def» :=
      op.getProperties! ctx.raw Function_.«def»
    let body := op.getRegion! ctx.raw 0
    match (body.get! ctx.raw).firstBlock with
    | none => pure ()
    | some entry =>
      let inputs := props.function_type.inputs
      if entry.getNumArguments! ctx.raw ≠ inputs.size then
        throw s!"function.def: entry block expected {inputs.size} argument(s), got {entry.getNumArguments! ctx.raw}"
      for i in [0:inputs.size] do
        let argType := ((entry.getArgument i).get! ctx.raw).type
        if !Attribute.branchArgCompatible inputs[i]! argType.val then
          throw s!"function.def: entry block argument {i} type does not match the function's declared input type"
  | .return => do
    op.verifyTerminatorCounts ctx opIn 0
    op.verifyLLZKFunctionReturnTypes ctx opIn
  -- Variadic operands *and* results: only region/successor counts checked.
  | .call => do
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "function.call: Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "function.call: Expected 0 successors"
    let props : Function_.propertiesOf .call :=
      op.getProperties! ctx.raw Function_.call
    let segments ←
      op.verifyOperandSegmentSizes ctx opIn props.operandSegmentSizes 2
    let mapOperandCount := segments[1]!
    let mut mapGroupSizes : Array Nat := #[]
    for size in props.mapOpGroupSizes.values do
      if size < 0 then
        throw s!"function.call: mapOpGroupSizes contains negative size {size}"
      mapGroupSizes := mapGroupSizes.push size.toNat
    let groupedOperandCount :=
      mapGroupSizes.foldl (init := 0) fun acc size => acc + size
    if groupedOperandCount ≠ mapOperandCount then
      throw s!"function.call: mapOpGroupSizes describes {groupedOperandCount} map operands, got {mapOperandCount}"
    let numDimsPerMap := props.numDimsPerMap.map (·.values) |>.getD #[]
    if numDimsPerMap.size ≠ mapGroupSizes.size then
      throw s!"function.call: numDimsPerMap expected {mapGroupSizes.size} entries, got {numDimsPerMap.size}"
    for i in [0:mapGroupSizes.size] do
      let numDims := numDimsPerMap[i]!
      if numDims < 0 then
        throw s!"function.call: numDimsPerMap contains negative size {numDims}"
      if numDims.toNat > mapGroupSizes[i]! then
        throw s!"function.call: map group {i} has {mapGroupSizes[i]!} operand(s), fewer than its {numDims} dimension(s)"

instance : HasOpInfo Function_ where
  verifyLocalInvariants := Function_.verifyLocalInvariants
  getEffects := Function_.getEffects
  isConstantLike := Function_.isConstantLike
  functionInterface? := Function_.functionInterface?
  hasSSADominance := Function_.hasSSADominance
  isTerminator := Function_.isTerminator
  isIsolatedFromAbove := Function_.isIsolatedFromAbove

end

end Veir
