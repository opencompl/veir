module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Interfaces.ControlFlowInterfaces
public import Veir.Dialects.RISCV_Cf.Properties
public import Veir.Dialects.RISCV.OpInfo
public import Veir.Verifier.Basic
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Riscv_Cf where
| func
| branch
| beqz
| bnez
| beq
| bne
| blt
| bge
| bltu
| bgeu
| unreachable
| call
| return
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Riscv_Cf.propertiesOf (op : Riscv_Cf) : Type :=
match op with
| .func => RISCVFuncProperties
| .call => RISCVCallProperties
| .beq => RISCVBrProperties
| .bne => RISCVBrProperties
| .blt => RISCVBrProperties
| .bge => RISCVBrProperties
| .bltu => RISCVBrProperties
| .bgeu => RISCVBrProperties
| .beqz => RISCVBrProperties
| .bnez => RISCVBrProperties
| _ => Unit

def Riscv_Cf.fromAttrDict
    (op : Riscv_Cf) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Riscv_Cf.propertiesOf op) := by
  cases op
  case func => exact RISCVFuncProperties.fromAttrDict attrDict
  case call => exact RISCVCallProperties.fromAttrDict attrDict
  case «return» =>
    exact if attrDict.isEmpty then .ok ()
      else .error "riscv_cf.return: expected no properties"
  case beq | bne | blt | bge | bltu | bgeu | beqz | bnez =>
    exact RISCVBrProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Riscv_Cf.toAttrDict
    (op : Riscv_Cf) (props : Riscv_Cf.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .func => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    dict := dict.insert "function_type".toUTF8 (.functionType props.function_type)
    return dict
  | .call =>
    match props.callee with
    | some callee =>
      (Std.HashMap.emptyWithCapacity 1).insert "callee".toUTF8 (.flatSymbolRefAttr callee)
    | none => Std.HashMap.emptyWithCapacity 0
  | .beq | .bne | .blt | .bge | .bltu | .bgeu | .beqz | .bnez =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "operandSegmentSizes".toUTF8
      (Attribute.denseArrayAttr props.operandSegmentSizes)
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Riscv_Cf.getEffects
    (op : Riscv_Cf) (_props : Riscv_Cf.propertiesOf op) : MemoryEffects :=
  match op with
  | .call => .unknown
  | _ => .none

def Riscv_Cf.isConstantLike (_op : Riscv_Cf) : Bool :=
  false

def Riscv_Cf.hasSSADominance (_op : Riscv_Cf) (_index : Nat) : Bool :=
  true

def Riscv_Cf.isIsolatedFromAbove (op : Riscv_Cf) : Bool :=
  op == .func

/--
  Calls resume at the next operation. Branches, returns, and `unreachable`
  terminate their block.
-/
@[is_terminator]
def Riscv_Cf.isTerminator (op : Riscv_Cf) : Bool :=
  match op with
  | .func | .call => false
  | _ => true

#generate_dialect Riscv_Cf

instance : IsOpCode Riscv_Cf where
  fromName := Riscv_Cf.fromName
  name := Riscv_Cf.name
  propertiesOf := Riscv_Cf.propertiesOf
  fromAttrDict := Riscv_Cf.fromAttrDict
  toAttrDict := Riscv_Cf.toAttrDict

def Riscv_Cf.functionInterface? (op : Riscv_Cf) :
    Option (FunctionOpInterface (Riscv_Cf.propertiesOf op)) :=
  match op with
  | .func => some
      { getSymName := fun props => props.sym_name
        getFunctionType := fun props => props.function_type
        setFunctionType := fun props functionType => { props with function_type := functionType } }
  | _ => none

def Riscv_Cf.branchOpInterface?
    (op : Riscv_Cf) : Option (BranchOpInterface (Riscv_Cf.propertiesOf op)) :=
  match op with
  | .branch =>
    some {
      getSuccessorOperandsImpl? := fun _ operands successorIndex => do
        guard (successorIndex = 0)
        some { forwardedOperands := operands }
      getSuccessorIndexForOperandsImpl? := fun _ _ => some 0
    }
  | .beqz =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          1 props.operandSegmentSizes.values operands successorIndex
      getSuccessorIndexForOperandsImpl? := fun _ operands => do
        let some (.reg condition) ← operands[0]? | none
        some (BranchOpInterface.getConditionalSuccessorIndex (condition.val = 0#64))
    }
  | .bnez =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          1 props.operandSegmentSizes.values operands successorIndex
      getSuccessorIndexForOperandsImpl? := fun _ operands => do
        let some (.reg condition) ← operands[0]? | none
        some (BranchOpInterface.getConditionalSuccessorIndex (condition.val ≠ 0#64))
    }
  | .beq =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorIndexForOperandsImpl? := fun _ operands => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        some (BranchOpInterface.getConditionalSuccessorIndex (lhs = rhs))
    }
  | .bne =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorIndexForOperandsImpl? := fun _ operands => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        some (BranchOpInterface.getConditionalSuccessorIndex (lhs ≠ rhs))
    }
  | .blt =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorIndexForOperandsImpl? := fun _ operands => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        some (BranchOpInterface.getConditionalSuccessorIndex (BitVec.slt lhs.val rhs.val))
    }
  | .bge =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorIndexForOperandsImpl? := fun _ operands => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        some (BranchOpInterface.getConditionalSuccessorIndex (!BitVec.slt lhs.val rhs.val))
    }
  | .bltu =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorIndexForOperandsImpl? := fun _ operands => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        some (BranchOpInterface.getConditionalSuccessorIndex (BitVec.ult lhs.val rhs.val))
    }
  | .bgeu =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorIndexForOperandsImpl? := fun _ operands => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        some (BranchOpInterface.getConditionalSuccessorIndex (!BitVec.ult lhs.val rhs.val))
    }
  | .func | .unreachable | .call | .return => none

/--
  Check a `riscv_cf.return` against the signature of its enclosing
  function-like operation (e.g. `func.func` or `llvm.func`). An `llvm.func`
  returning `void` declares no results.
  Local verifiers only require `IsOpCode`, so the caller supplies the combined
  opcode set's `functionInterface?`; requiring `HasOpInfo` here would be circular.
-/
private def OperationPtr.verifyRISCVReturnTypes {OpInfo : Type} [IsOpCode OpInfo]
    (functionInterface? : (op : OpInfo) → Option (FunctionOpInterface (IsOpCode.propertiesOf op)))
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) :
    Except String PUnit := do
  let funcOp ← op.getEnclosingFunctionOp ctx "riscv_cf.return"
  let funcType := funcOp.getOpType! ctx.raw
  let some interface := functionInterface? funcType
    | throw "Expected riscv_cf.return to be enclosed by a function-like operation"
  let outputs := match (interface.getFunctionType (funcOp.getProperties! ctx.raw funcType)).outputs with
    | #[.llvmVoidType _] => #[]
    | outputs => outputs
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected riscv_cf.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if !Attribute.branchArgCompatible (opTypes[i]!).val outputs[i]! then
      throw s!"riscv_cf.return operand {i} type does not match the function's declared result type"

/--
Verify the local invariants of a `riscv_cf` operation in any operation-info
type containing the `riscv_cf` dialect. `functionInterface?` is that type's
function interface, used to check returns against their enclosing function.
-/
def Riscv_Cf.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Riscv_Cf]
    (functionInterface? : (op : OpInfo) → Option (FunctionOpInterface (IsOpCode.propertiesOf op)))
    (opType : Riscv_Cf) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .func => do
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "riscv_cf.func: Expected 1 region"
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "riscv_cf.func: Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "riscv_cf.func: Expected 0 results"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "riscv_cf.func: Expected 0 successors"
    let ft := (op.getProperties! ctx.raw Riscv_Cf.func).function_type
    for ty in ft.inputs ++ ft.outputs do
      let .registerType _ := ty
        | throw "riscv_cf.func: Expected register types in function signature"
    let body := op.getRegion! ctx.raw 0
    if let some entry := (body.get! ctx.raw).firstBlock then
      if entry.getNumArguments! ctx.raw ≠ ft.inputs.size then
        throw "riscv_cf.func: Entry block argument count does not match function signature"
      for i in [0:ft.inputs.size] do
        if ((entry.getArgument i).get! ctx.raw).type.val ≠ ft.inputs[i]! then
          throw s!"riscv_cf.func: Entry block argument {i} type does not match function signature"
  | .branch =>
    op.verifyUnconditionalBranch ctx opIn
  | .beq => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw Riscv_Cf.beq).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .bne => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw Riscv_Cf.bne).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .blt => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw Riscv_Cf.blt).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .bge => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw Riscv_Cf.bge).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .bltu => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw Riscv_Cf.bltu).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .bgeu => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw Riscv_Cf.bgeu).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 2
    pure ()
  | .beqz => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw Riscv_Cf.beqz).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 1
    pure ()
  | .bnez => do
    op.verifyTerminatorCounts ctx opIn 2
    let sizes := (op.getProperties! ctx.raw Riscv_Cf.bnez).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 1
    pure ()
  | .unreachable =>
    op.verifyPlainOpCounts ctx opIn 0 0
  -- Calls are variadic in their register arguments and results; control
  -- resumes at the next operation, so there are no successors.
  | .call => do
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "riscv_cf.call: Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "riscv_cf.call: Expected 0 successors"
    op.verifyRISCVRegisterTypes ctx opIn
    let props := op.getProperties! ctx.raw Riscv_Cf.call
    if props.callee.isNone && op.getNumOperands ctx.raw opIn == 0 then
      throw "riscv_cf.call: Expected an indirect call to have a target register operand"
  | .return => do
    op.verifyTerminatorCounts ctx opIn 0
    op.verifyRISCVRegisterTypes ctx opIn
    op.verifyRISCVReturnTypes functionInterface? ctx opIn

def Riscv_Cf.interpretOp' (opType : Veir.Riscv_Cf) (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    : Interp (Array RuntimeValue × Option ControlFlowAction) :=
  match opType with
  | .func =>
    Interp.fail none
  | .branch => do
    let [dest] := blockOperands.toList | none
    return (#[], some (.branch operands dest))
  | .beq => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if lhs == rhs then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bne => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if lhs != rhs then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .blt => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if BitVec.slt lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bge => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if !BitVec.slt lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bltu => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if BitVec.ult lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bgeu => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if !BitVec.ult lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .beqz => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg cond) := operands[0]? | none
    let some trueSize := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSize.toNat
    if cond.val = 0#64 then
      return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
  | .bnez => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg cond) := operands[0]? | none
    let some trueSize := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSize.toNat
    if cond.val ≠ 0#64 then
      return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
  -- Reaching `unreachable` is undefined behavior, as for `llvm.unreachable`, so
  -- that lowering the latter to the former is a refinement. The MIR printer
  -- lowers it to an instruction that traps.
  | .unreachable =>
    Interp.ub none
  | .return =>
    return (#[], some (.return operands))
  -- Calls require symbol resolution and an interpreter call stack.
  | .call =>
    Interp.fail none

instance : HasOpInfo Riscv_Cf where
  verifyLocalInvariants := Riscv_Cf.verifyLocalInvariants Riscv_Cf.functionInterface?
  getEffects := Riscv_Cf.getEffects
  isConstantLike := Riscv_Cf.isConstantLike
  branchOpInterface? := Riscv_Cf.branchOpInterface?
  functionInterface? := Riscv_Cf.functionInterface?
  hasSSADominance := Riscv_Cf.hasSSADominance
  isTerminator := Riscv_Cf.isTerminator
  isIsolatedFromAbove := Riscv_Cf.isIsolatedFromAbove

end

end Veir
