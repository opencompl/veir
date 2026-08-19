module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.Func.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Func where
| func
| call
| return
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Func.propertiesOf (op : Func) : Type :=
match op with
| .func => FuncFuncProperties
| .call => FuncCallProperties
| _ => Unit

def Func.fromAttrDict
    (op : Func) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Func.propertiesOf op) := by
  cases op
  case func => exact FuncFuncProperties.fromAttrDict attrDict
  case call => exact FuncCallProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Func.toAttrDict
    (op : Func) (props : Func.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .call => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "callee".toUTF8 (.flatSymbolRefAttr props.callee)
    dict
  | .func => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    dict := dict.insert "function_type".toUTF8 (.functionType props.function_type)
    dict
  | _ => Std.HashMap.emptyWithCapacity 0

def Func.getEffects
    (op : Func) (_props : Func.propertiesOf op) : MemoryEffects :=
  match op with
  | .call => .unknown
  | .func | .return => .none

def Func.isConstantLike (_op : Func) : Bool :=
  false

def Func.isFunctionLike (op : Func) : Bool :=
  match op with
  | .func => true
  | .call | .return => false

def Func.hasSSADominance (_op : Func) (_index : Nat) : Bool :=
  true

def Func.isTerminator (op : Func) : Bool :=
  match op with
  | .return => true
  | .func | .call => false

#generate_dialect Func

instance : IsOpCode Func where
  fromName := Func.fromName
  name := Func.name
  propertiesOf := Func.propertiesOf
  fromAttrDict := Func.fromAttrDict
  toAttrDict := Func.toAttrDict

/--
Check that a `func.return` returns the declared result types of its enclosing
`func.func`.
-/
def OperationPtr.verifyFuncReturnTypes {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Func] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let funcOp ← op.getEnclosingFunctionOp ctx "func.return"
  let some .func := toDialect? Func (funcOp.getOpType! ctx.raw)
    | throw "Expected func.return to be enclosed by func.func"
  let props : Func.propertiesOf .func := funcOp.getProperties! ctx.raw Func.func
  let functionType := props.function_type
  let outputs := functionType.outputs
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected func.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if !Attribute.branchArgCompatible (opTypes[i]!).val outputs[i]! then
      throw s!"func.return operand {i} type does not match the function's declared result type"

/--
Verify the local invariants of a `func` operation in any operation-info type
containing the `func` dialect.
-/
@[expose]
def Func.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Func] (opType : Func) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .func => do
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
  | .call => do
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .return => do
    op.verifyTerminatorCounts ctx opIn 0
    op.verifyFuncReturnTypes ctx opIn

instance : HasOpInfo Func where
  verifyLocalInvariants := Func.verifyLocalInvariants
  getEffects := Func.getEffects
  isConstantLike := Func.isConstantLike
  isFunctionLike := Func.isFunctionLike
  hasSSADominance := Func.hasSSADominance
  isTerminator := Func.isTerminator

end

end Veir
