module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Function.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
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

def Function_.fromAttrDict
    (op : Function_) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Function_.propertiesOf op) := by
  cases op
  case «def» => exact FunctionDefProperties.fromAttrDict attrDict
  case «return» => exact .ok ()
  case call => exact FunctionCallProperties.fromAttrDict attrDict

def Function_.toAttrDict
    (op : Function_) (props : Function_.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .«def» =>
    ((Std.HashMap.emptyWithCapacity 2).insert
      "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)).insert
      "function_type".toUTF8 (Attribute.functionType props.function_type)
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
  | .return => do
    op.verifyTerminatorCounts ctx opIn 0
    op.verifyLLZKFunctionReturnTypes ctx opIn
  -- Variadic operands *and* results: only region/successor counts checked.
  | .call => do
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "function.call: Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "function.call: Expected 0 successors"

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
