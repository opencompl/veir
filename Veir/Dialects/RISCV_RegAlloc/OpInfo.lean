module

public import Veir.IR.OpInfo
public import Veir.IR.Simp
public import Veir.Verifier.Basic
public import Veir.Dialects.RISCV.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
Dialect for register allocation, only used during the register allocation passes.
-/
@[opcodes]
inductive Riscv_RegAlloc where
/-- spill value from register to stack: `(!riscv.reg)   -> !riscv.stack`
    riscv.stack is stack type register and models a stack slot for a spilled register,
    will be replaced with actual memory store in later pass -/
| spill
/-- load value from stack back to register `(!riscv.stack) -> !riscv.reg`
    will be replaced with actual memory load in later pass -/
| reload
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, implicit_reducible, properties_of]
def Riscv_RegAlloc.propertiesOf (op : Riscv_RegAlloc) : Type :=
match op with
| _ => Unit

def Riscv_RegAlloc.fromAttrDict
    (op : Riscv_RegAlloc) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Riscv_RegAlloc.propertiesOf op) := by
  cases op <;> exact .ok ()

def Riscv_RegAlloc.toAttrDict
    (_op : Riscv_RegAlloc) (_props : Riscv_RegAlloc.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Riscv_RegAlloc.getEffects
    (_op : Riscv_RegAlloc) (_props : Riscv_RegAlloc.propertiesOf _op) : MemoryEffects :=
  .none

def Riscv_RegAlloc.isConstantLike (_op : Riscv_RegAlloc) : Bool :=
  false

def Riscv_RegAlloc.hasSSADominance (_op : Riscv_RegAlloc) (_index : Nat) : Bool :=
  true

#generate_dialect Riscv_RegAlloc

instance : IsOpCode Riscv_RegAlloc where
  fromName := Riscv_RegAlloc.fromName
  name := Riscv_RegAlloc.name
  propertiesOf := Riscv_RegAlloc.propertiesOf
  fromAttrDict := Riscv_RegAlloc.fromAttrDict
  toAttrDict := Riscv_RegAlloc.toAttrDict

/--
Verify that a `riscv_regalloc` operation has exactly one operand of register class
`operandCls` and exactly one result of register class `resultCls`.
-/
def Riscv_RegAlloc.verifyOperationSignature {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw)
    (operandCls resultCls : RegisterClass) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let .registerType operand := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
    | throw "first operand should be a register type"
  if operand.cls != operandCls then
    throw s!"first operand should be {({ cls := operandCls } : RegisterType)} type"
  let .registerType result := ((op.getResult 0).getType! ctx.raw).val
    | throw "result should be a register type"
  if result.cls != resultCls then
    throw s!"result should be {({ cls := resultCls } : RegisterType)} type"

def Riscv_RegAlloc.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Riscv_RegAlloc] (opType : Riscv_RegAlloc) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .spill => Riscv_RegAlloc.verifyOperationSignature op ctx opIn .int .stack
  | .reload => Riscv_RegAlloc.verifyOperationSignature op ctx opIn .stack .int

def Riscv_RegAlloc.interpretOp' (opType : Veir.Riscv_RegAlloc) (_properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .spill | .reload => do
    let [.reg value] := operands.toList | none
    return (#[.reg value], none)


instance : HasOpInfo Riscv_RegAlloc where
  verifyLocalInvariants := Riscv_RegAlloc.verifyLocalInvariants
  getEffects := Riscv_RegAlloc.getEffects
  isConstantLike := Riscv_RegAlloc.isConstantLike
  hasSSADominance := Riscv_RegAlloc.hasSSADominance

end

end Veir
