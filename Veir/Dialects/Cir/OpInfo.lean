module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.Cir.Properties
meta import Veir.Meta.OpCode

/-!
# The `cir` dialect

The integer core of ClangIR (https://llvm.github.io/clangir/): signed and unsigned integer
scalars, booleans, and flat control flow. Structured control flow, pointers, records and
floating point are not modelled; their operations remain unregistered.
-/

namespace Veir

public section

@[opcodes]
inductive Cir where
| func
| return
| const
| add
| sub
| mul
| div
| rem
| and
| or
| xor
| shift
| not
| minus
| min
| max
| cmp
| select
| cast
| br
| brcond
| unreachable
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Cir.propertiesOf (op : Cir) : Type :=
match op with
| .func => CirFuncProperties
| .const => CirConstProperties
| .add | .sub | .minus => CirOverflowFlagsProperties
| .shift => CirShiftProperties
| .cmp => CirCmpProperties
| .cast => CirCastProperties
| .brcond => CirBrCondProperties
| _ => Unit

def Cir.fromAttrDict
    (op : Cir) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Cir.propertiesOf op) :=
  match op with
  | .func => CirFuncProperties.fromAttrDict attrDict
  | .const => CirConstProperties.fromAttrDict attrDict
  | .add | .sub | .minus => CirOverflowFlagsProperties.fromAttrDict attrDict
  | .shift => CirShiftProperties.fromAttrDict attrDict
  | .cmp => CirCmpProperties.fromAttrDict attrDict
  | .cast => CirCastProperties.fromAttrDict attrDict
  | .brcond => CirBrCondProperties.fromAttrDict attrDict
  | .return | .mul | .div | .rem | .and | .or | .xor | .not | .min | .max
  | .select | .br | .unreachable => Cir.noProperties attrDict

def Cir.toAttrDict
    (op : Cir) (props : Cir.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .func => props.toAttrDict
  | .const => props.toAttrDict
  | .add | .sub | .minus => props.toAttrDict
  | .shift => props.toAttrDict
  | .cmp => props.toAttrDict
  | .cast => props.toAttrDict
  | .brcond => props.toAttrDict
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Cir.getEffects
    (_op : Cir) (_props : Cir.propertiesOf _op) : MemoryEffects :=
  .none

def Cir.isConstantLike (op : Cir) : Bool :=
  match op with
  | .const => true
  | _ => false

def Cir.hasSSADominance (_op : Cir) (_index : Nat) : Bool :=
  true

@[is_terminator]
def Cir.isTerminator (op : Cir) : Bool :=
  match op with
  | .return | .br | .brcond | .unreachable => true
  | _ => false

def Cir.isIsolatedFromAbove (op : Cir) : Bool :=
  match op with
  | .func => true
  | _ => false

#generate_dialect Cir

instance : IsOpCode Cir where
  fromName := Cir.fromName
  name := Cir.name
  propertiesOf := Cir.propertiesOf
  fromAttrDict := Cir.fromAttrDict
  toAttrDict := Cir.toAttrDict

def Cir.functionInterface? (op : Cir) : Option (FunctionOpInterface (Cir.propertiesOf op)) :=
  match op with
  | .func =>
    some
      { getSymName := fun props => props.sym_name
        getFunctionType := fun props => props.function_type.functionType
        setFunctionType := fun props functionType =>
          { props with function_type := { functionType } } }
  | _ => none

/-! ## Verifier -/

/-- Verify that a type is a ClangIR integer type. -/
def TypeAttr.verifyCirIntType (ty : TypeAttr) (msg : String) : Except String CirIntType :=
  match ty.val with
  | .cirIntType type => pure type
  | type => throw s!"{msg}, but found {type} instead"

/-- Verify that a type is the ClangIR boolean type. -/
def TypeAttr.verifyCirBoolType (ty : TypeAttr) (msg : String) : Except String PUnit :=
  match ty.val with
  | .cirBoolType _ => pure ()
  | type => throw s!"{msg}, but found {type} instead"

/-- Verify that a type is a ClangIR integer or boolean type. -/
def TypeAttr.verifyCirIntOrBoolType (ty : TypeAttr) (msg : String) : Except String PUnit :=
  match ty.val with
  | .cirIntType _ | .cirBoolType _ => pure ()
  | type => throw s!"{msg}, but found {type} instead"

/-- Verify a binary integer operation: two operands of one `!cir.int` type and a like result. -/
def OperationPtr.verifyCirBinOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  let _ ← operandType.verifyCirIntType s!"{instrName}: Expected operands to have !cir.int type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"

/-- Verify `cir.shift`: the amount may have a different integer type than the value. -/
def OperationPtr.verifyCirShiftOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let valueType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  let _ ← valueType.verifyCirIntType
    s!"{instrName}: Expected the shifted value to have !cir.int type"
  let _ ← ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyCirIntType
    s!"{instrName}: Expected the shift amount to have !cir.int type"
  op.verifyResultTypeMatches ctx valueType
    s!"{instrName}: Expected result type to match the shifted value's type"

/-- Verify a unary operation whose result has the operand's type. -/
def OperationPtr.verifyCirUnaryOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (allowBool : Bool) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  if allowBool then
    operandType.verifyCirIntOrBoolType
      s!"{instrName}: Expected operand to have !cir.int or !cir.bool type"
  else
    let _ ← operandType.verifyCirIntType s!"{instrName}: Expected operand to have !cir.int type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"

/-- Verify `cir.cmp`: two operands of one integer or boolean type and a `!cir.bool` result. -/
def OperationPtr.verifyCirCmpOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  operandType.verifyCirIntOrBoolType
    s!"{instrName}: Expected operands to have !cir.int or !cir.bool type"
  ((op.getResult 0).get! ctx.raw).type.verifyCirBoolType
    s!"{instrName}: Expected result to have !cir.bool type"

/-- Verify `cir.select`: a `!cir.bool` condition and two values of one type. -/
def OperationPtr.verifyCirSelectOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 3 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyCirBoolType
    s!"{instrName}: Expected condition to have !cir.bool type"
  let valueType ← op.verifyOperandTypesMatch ctx 1 2
    s!"{instrName}: Expected the selected values to have the same type"
  op.verifyResultTypeMatches ctx valueType
    s!"{instrName}: Expected result type to match the selected values' type"

/-- Verify `cir.cast` against its kind. Unmodelled kinds are only checked for arity. -/
def OperationPtr.verifyCirCastOp {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Cir] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let props := op.getProperties! ctx.raw Cir.cast
  let srcType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  let resultType := ((op.getResult 0).get! ctx.raw).type
  match props.kind with
  | .integral =>
    let _ ← srcType.verifyCirIntType
      s!"{instrName}: Expected integral cast source to have !cir.int type"
    let _ ← resultType.verifyCirIntType
      s!"{instrName}: Expected integral cast result to have !cir.int type"
  | .int_to_bool =>
    let _ ← srcType.verifyCirIntType
      s!"{instrName}: Expected int_to_bool cast source to have !cir.int type"
    resultType.verifyCirBoolType
      s!"{instrName}: Expected int_to_bool cast result to have !cir.bool type"
  | .bool_to_int =>
    srcType.verifyCirBoolType
      s!"{instrName}: Expected bool_to_int cast source to have !cir.bool type"
    let _ ← resultType.verifyCirIntType
      s!"{instrName}: Expected bool_to_int cast result to have !cir.int type"
  | .other _ => pure ()

/-- Verify `cir.const`: the constant's type is the result type and its value fits. -/
def OperationPtr.verifyCirConstOp {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Cir] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 0 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let props := op.getProperties! ctx.raw Cir.const
  let resultType := ((op.getResult 0).get! ctx.raw).type
  if props.value.type ≠ resultType.val then
    throw s!"{instrName}: Expected result type to match the constant's type"
  if let .int attr := props.value then
    let width := attr.type.width
    let (lo, hi) : Int × Int :=
      if attr.type.isSigned then (-(2 ^ (width - 1)), 2 ^ (width - 1)) else (0, 2 ^ width)
    if attr.value < lo ∨ hi ≤ attr.value then
      throw s!"{instrName}: constant value {attr.value} does not fit in {attr.type}"

/-- Verify `cir.brcond`: a `!cir.bool` condition, then the forwarded operand segments. -/
def OperationPtr.verifyCirBrCondOp {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Cir] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyTerminatorCounts ctx opIn 2
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let props := op.getProperties! ctx.raw Cir.brcond
  op.verifyCondBranchOperandSegmentSizes ctx opIn props.operandSegmentSizes 1
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyCirBoolType
    s!"{instrName}: Expected condition to have !cir.bool type"

/-- Check that a `cir.return` returns the declared result types of its enclosing `cir.func`. -/
def OperationPtr.verifyCirReturnTypes {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Cir] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let funcOp ← op.getEnclosingFunctionOp ctx "cir.return"
  let some .func := toDialect? Cir (funcOp.getOpType! ctx.raw)
    | throw "Expected cir.return to be enclosed by cir.func"
  let props : Cir.propertiesOf .func := funcOp.getProperties! ctx.raw Cir.func
  let outputs := props.function_type.functionType.outputs
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected cir.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if (opTypes[i]!).val ≠ outputs[i]! then
      throw s!"cir.return operand {i} type does not match the function's declared result type"

/--
Verify the local invariants of a `cir` operation in any operation-info type
containing the `cir` dialect.
-/
@[expose]
def Cir.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Cir] (opType : Cir) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .func => do
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "cir.func: Expected 1 region"
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "cir.func: Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "cir.func: Expected 0 results"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "cir.func: Expected 0 successors"
  | .return => do
    op.verifyTerminatorCounts ctx opIn 0
    op.verifyCirReturnTypes ctx opIn
  | .const => op.verifyCirConstOp ctx opIn
  | .add | .sub | .mul | .div | .rem | .and | .or | .xor | .min | .max =>
    op.verifyCirBinOp ctx opIn
  | .shift => op.verifyCirShiftOp ctx opIn
  | .not => op.verifyCirUnaryOp ctx opIn true
  | .minus => op.verifyCirUnaryOp ctx opIn false
  | .cmp => op.verifyCirCmpOp ctx opIn
  | .select => op.verifyCirSelectOp ctx opIn
  | .cast => op.verifyCirCastOp ctx opIn
  | .br => op.verifyUnconditionalBranch ctx opIn
  | .brcond => op.verifyCirBrCondOp ctx opIn
  | .unreachable => op.verifyPlainOpCounts ctx opIn 0 0

instance : HasOpInfo Cir where
  verifyLocalInvariants := Cir.verifyLocalInvariants
  getEffects := Cir.getEffects
  isConstantLike := Cir.isConstantLike
  functionInterface? := Cir.functionInterface?
  hasSSADominance := Cir.hasSSADominance
  isTerminator := Cir.isTerminator
  isIsolatedFromAbove := Cir.isIsolatedFromAbove

end

end Veir
