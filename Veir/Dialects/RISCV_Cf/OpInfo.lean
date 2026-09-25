module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.RISCV_Cf.Properties
public import Veir.Verifier.Basic
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Riscv_Cf where
| branch
| beqz
| bnez
| beq
| bne
| blt
| bge
| bltu
| bgeu
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Riscv_Cf.propertiesOf (op : Riscv_Cf) : Type :=
match op with
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
  case beq | bne | blt | bge | bltu | bgeu | beqz | bnez =>
    exact RISCVBrProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Riscv_Cf.toAttrDict
    (op : Riscv_Cf) (props : Riscv_Cf.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .beq | .bne | .blt | .bge | .bltu | .bgeu | .beqz | .bnez =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "operandSegmentSizes".toUTF8
      (Attribute.denseArrayAttr props.operandSegmentSizes)
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Riscv_Cf.getEffects
    (_op : Riscv_Cf) (_props : Riscv_Cf.propertiesOf _op) : MemoryEffects :=
  .none

def Riscv_Cf.isConstantLike (_op : Riscv_Cf) : Bool :=
  false

def Riscv_Cf.hasSSADominance (_op : Riscv_Cf) (_index : Nat) : Bool :=
  true

/-- Every `riscv_cf` operation is a branch, and so terminates its block. -/
@[is_terminator]
def Riscv_Cf.isTerminator (_op : Riscv_Cf) : Bool :=
  true

#generate_dialect Riscv_Cf

instance : IsOpCode Riscv_Cf where
  fromName := Riscv_Cf.fromName
  name := Riscv_Cf.name
  propertiesOf := Riscv_Cf.propertiesOf
  fromAttrDict := Riscv_Cf.fromAttrDict
  toAttrDict := Riscv_Cf.toAttrDict

def Riscv_Cf.branchOpInterface?
    (op : Riscv_Cf) : Option (BranchOpInterface (Riscv_Cf.propertiesOf op)) :=
  match op with
  | .branch =>
    some {
      getSuccessorOperandsImpl? := fun _ operands successorIndex => do
        guard (successorIndex = 0)
        some { forwardedOperands := operands }
      getSuccessorForOperandsImpl? := fun _ _ successors => successors[0]?
    }
  | .beqz =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          1 props.operandSegmentSizes.values operands successorIndex
      getSuccessorForOperandsImpl? := fun _ operands successors => do
        let some (.reg condition) ← operands[0]? | none
        BranchOpInterface.getConditionalSuccessor? successors (condition.val = 0#64)
    }
  | .bnez =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          1 props.operandSegmentSizes.values operands successorIndex
      getSuccessorForOperandsImpl? := fun _ operands successors => do
        let some (.reg condition) ← operands[0]? | none
        BranchOpInterface.getConditionalSuccessor? successors (condition.val ≠ 0#64)
    }
  | .beq =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorForOperandsImpl? := fun _ operands successors => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        BranchOpInterface.getConditionalSuccessor? successors (lhs = rhs)
    }
  | .bne =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorForOperandsImpl? := fun _ operands successors => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        BranchOpInterface.getConditionalSuccessor? successors (lhs ≠ rhs)
    }
  | .blt =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorForOperandsImpl? := fun _ operands successors => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        BranchOpInterface.getConditionalSuccessor? successors (BitVec.slt lhs.val rhs.val)
    }
  | .bge =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorForOperandsImpl? := fun _ operands successors => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        BranchOpInterface.getConditionalSuccessor? successors (!BitVec.slt lhs.val rhs.val)
    }
  | .bltu =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorForOperandsImpl? := fun _ operands successors => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        BranchOpInterface.getConditionalSuccessor? successors (BitVec.ult lhs.val rhs.val)
    }
  | .bgeu =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          2 props.operandSegmentSizes.values operands successorIndex
      getSuccessorForOperandsImpl? := fun _ operands successors => do
        let some (.reg lhs) ← operands[0]? | none
        let some (.reg rhs) ← operands[1]? | none
        BranchOpInterface.getConditionalSuccessor? successors (!BitVec.ult lhs.val rhs.val)
    }

/--
Verify the local invariants of a `riscv_cf` operation in any operation-info
type containing the `riscv_cf` dialect.
-/
def Riscv_Cf.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Riscv_Cf] (opType : Riscv_Cf) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
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

def Riscv_Cf.interpretOp' (opType : Veir.Riscv_Cf) (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    : Interp (Array RuntimeValue × Option ControlFlowAction) :=
  match opType with
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

instance : HasOpInfo Riscv_Cf where
  verifyLocalInvariants := Riscv_Cf.verifyLocalInvariants
  getEffects := Riscv_Cf.getEffects
  isConstantLike := Riscv_Cf.isConstantLike
  branchOpInterface? := Riscv_Cf.branchOpInterface?
  hasSSADominance := Riscv_Cf.hasSSADominance
  isTerminator := Riscv_Cf.isTerminator

end

end Veir
