module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Function.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Function where
| «def»
| return
| call
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Function.propertiesOf (op : LLZK.Function) : Type :=
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

def LLZK.Function.fromAttrDict
    (op : LLZK.Function) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Function.propertiesOf op) :=
  match op with
  | .«def» => FunctionDefProperties.fromAttrDict attrDict
  | .return => noProperties "function.return" attrDict
  | .call => FunctionCallProperties.fromAttrDict attrDict

def LLZK.Function.toAttrDict
    (op : LLZK.Function) (props : LLZK.Function.propertiesOf op) :
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
def LLZK.Function.getEffects
    (op : LLZK.Function) (_props : LLZK.Function.propertiesOf op) : MemoryEffects :=
  match op with
  | .call => .unknown
  | _ => .none

def LLZK.Function.isConstantLike (_op : LLZK.Function) : Bool := false

/-- A `function.def` body cannot reference SSA values from enclosing regions. -/
def LLZK.Function.isIsolatedFromAbove (op : LLZK.Function) : Bool :=
  match op with
  | .«def» => true
  | _ => false

def LLZK.Function.hasSSADominance (_op : LLZK.Function) (_index : Nat) : Bool :=
  true

@[is_terminator]
def LLZK.Function.isTerminator (op : LLZK.Function) : Bool :=
  match op with
  | .return => true
  | .«def» | .call => false

#generate_dialect LLZK.Function

instance : IsOpCode LLZK.Function where
  fromName := LLZK.Function.fromName
  name := LLZK.Function.name
  propertiesOf := LLZK.Function.propertiesOf
  fromAttrDict := LLZK.Function.fromAttrDict
  toAttrDict := LLZK.Function.toAttrDict

def LLZK.Function.functionInterface? (op : LLZK.Function) :
    Option (FunctionOpInterface (LLZK.Function.propertiesOf op)) :=
  match op with
  | .«def» =>
    some
      { getSymName := fun props => props.sym_name
        getFunctionType := fun props => props.function_type
        setFunctionType := fun props functionType =>
          { props with function_type := functionType } }
  | .return | .call => none

/-- The currently representable subset of the types checked by LLZK's `FuncDefOp::verify`:
https://github.com/project-llzk/llzk-lib/blob/265d68f678ab15018e3f6253b85557fbaeac9c0d/lib/Dialect/Function/IR/Ops.cpp#L338-L383

This is deliberately narrower until VeIR ports LLZK's aggregate and polymorphic types. -/
def Attribute.isSupportedLLZKFunctionType (type : Attribute) : Bool :=
  match type with
  | .integerType intType => intType.bitwidth = 1
  | .indexType _ | .feltType _ => true
  | _ => false

private partial def OperationPtr.getEnclosingBuiltinModule? {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Option OperationPtr :=
  match op.getParentOp! ctx with
  | none => none
  | some parent =>
    if IsOpCode.name (parent.getOpType! ctx) = "builtin.module".toUTF8 then
      some parent
    else
      parent.getEnclosingBuiltinModule? ctx

private def OperationPtr.verifyModuleFunctionCall {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Function] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (props : FunctionCallProperties) (argumentCount : Nat) : Except String PUnit := do
  -- Verify calls to module-level function definitions.
  -- https://github.com/project-llzk/llzk-lib/blob/265d68f678ab15018e3f6253b85557fbaeac9c0d/lib/Dialect/Function/IR/Ops.cpp#L938-L954
  -- https://github.com/project-llzk/llzk-lib/blob/265d68f678ab15018e3f6253b85557fbaeac9c0d/lib/Dialect/Function/IR/Ops.cpp#L1103-L1141
  let some moduleOp := op.getEnclosingBuiltinModule? ctx.raw
    | throw "function.call: expected an enclosing builtin.module"
  let mut target : Option OperationPtr := none
  for candidate in ctx.raw.operations.keys do
    if candidate.getParentOp! ctx.raw = some moduleOp then
      match toDialect? LLZK.Function (candidate.getOpType! ctx.raw) with
      | some .«def» =>
        let candidateProps : LLZK.Function.propertiesOf .«def» :=
          candidate.getProperties! ctx.raw LLZK.Function.«def»
        let candidateName := "@" ++ String.fromUTF8! candidateProps.sym_name.value
        if candidateName = props.callee.value then
          if target.isSome then
            throw s!"function.call: callee '{props.callee}' is ambiguous because the symbol is defined more than once"
          target := some candidate
      | _ => pure ()
  let some targetOp := target
    | throw s!"function.call: callee '{props.callee}' does not name a function.def"
  let targetProps : LLZK.Function.propertiesOf .«def» :=
    targetOp.getProperties! ctx.raw LLZK.Function.«def»
  let targetType := targetProps.function_type
  if argumentCount != targetType.inputs.size then
    throw s!"function.call: incorrect number of operands for callee, expected {targetType.inputs.size}, got {argumentCount}"
  let operandTypes := op.getOperandTypes! ctx.raw
  for i in [0:argumentCount] do
    if !Attribute.branchArgCompatible operandTypes[i]!.val targetType.inputs[i]! then
      throw s!"function.call: operand {i} type does not match the callee's input type"
  let resultTypes := op.getResultTypes! ctx.raw
  if resultTypes.size != targetType.outputs.size then
    throw s!"function.call: incorrect number of results for callee, expected {targetType.outputs.size}, got {resultTypes.size}"
  for i in [0:resultTypes.size] do
    if !Attribute.branchArgCompatible resultTypes[i]!.val targetType.outputs[i]! then
      throw s!"function.call: result {i} type does not match the callee's result type"

/-- Check that `function.return` matches its enclosing `function.def` result types. -/
def OperationPtr.verifyLLZKFunctionReturnTypes {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Function] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let funcOp ← op.getEnclosingFunctionOp ctx "function.return"
  let some .«def» := toDialect? LLZK.Function (funcOp.getOpType! ctx.raw)
    | throw "Expected function.return to be enclosed by function.def"
  let props : LLZK.Function.propertiesOf .«def» :=
    funcOp.getProperties! ctx.raw LLZK.Function.«def»
  let outputs := props.function_type.outputs
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected function.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if !Attribute.branchArgCompatible (opTypes[i]!).val outputs[i]! then
      throw s!"function.return operand {i} type does not match the function's declared result type"

def LLZK.Function.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Function] (opType : LLZK.Function) (op : OperationPtr)
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
    -- LLZK allows module, struct, and polymorphic-template parents. VeIR only supports the first
    -- until those other dialects are ported:
    -- https://github.com/project-llzk/llzk-lib/blob/265d68f678ab15018e3f6253b85557fbaeac9c0d/include/llzk/Dialect/Function/IR/Ops.td#L38-L45
    match op.getParentOp! ctx.raw with
    | some parent =>
      if IsOpCode.name (parent.getOpType! ctx.raw) != "builtin.module".toUTF8 then
        throw "function.def: expected parent to be builtin.module; struct.def and poly.template are not yet supported"
    | none =>
      throw "function.def: expected parent to be builtin.module"
    let props : LLZK.Function.propertiesOf .«def» :=
      op.getProperties! ctx.raw LLZK.Function.«def»
    if props.extra.entries.any fun (name, _) => name = "function.arg_name".toUTF8 then
      throw "function.def: 'function.arg_name' is only valid on function arguments"
    if props.extra.entries.any fun (name, _) => name = "function.res_name".toUTF8 then
      throw "function.def: 'function.res_name' is only valid on function results"
    for type in props.function_type.inputs ++ props.function_type.outputs do
      if !type.isSupportedLLZKFunctionType then
        throw s!"function.def: expected a supported LLZK type, got {type}"
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
    let props : LLZK.Function.propertiesOf .call :=
      op.getProperties! ctx.raw LLZK.Function.call
    let segments ←
      op.verifyOperandSegmentSizes ctx opIn props.operandSegmentSizes 2
    let argumentCount := segments[0]!
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
    for i in [argumentCount:op.getNumOperands ctx.raw opIn] do
      let mapType := (op.getOperandTypes! ctx.raw)[i]!.val
      match mapType with
      | .indexType _ => pure ()
      | _ => throw s!"function.call: map operand {i - argumentCount} must have index type"
    op.verifyModuleFunctionCall ctx props argumentCount

instance : HasOpInfo LLZK.Function where
  verifyLocalInvariants := LLZK.Function.verifyLocalInvariants
  getEffects := LLZK.Function.getEffects
  isConstantLike := LLZK.Function.isConstantLike
  functionInterface? := LLZK.Function.functionInterface?
  hasSSADominance := LLZK.Function.hasSSADominance
  isTerminator := LLZK.Function.isTerminator
  isIsolatedFromAbove := LLZK.Function.isIsolatedFromAbove

end

end Veir
