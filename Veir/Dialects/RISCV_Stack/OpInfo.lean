module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.RISCV_Stack.Properties
public import Veir.Dialects.RISCV.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Riscv_Stack where
| alloca
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Riscv_Stack.propertiesOf (op : Riscv_Stack) : Type :=
match op with
| .alloca => RISCVStackAllocaProperties

def Riscv_Stack.fromAttrDict
    (op : Riscv_Stack) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Riscv_Stack.propertiesOf op) := by
  cases op
  exact RISCVStackAllocaProperties.fromAttrDict attrDict

def Riscv_Stack.toAttrDict
    (op : Riscv_Stack) (props : Riscv_Stack.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .alloca => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    dict := dict.insert "size".toUTF8 (Attribute.integerAttr props.size)
    dict.insert "alignment".toUTF8 (Attribute.integerAttr props.alignment)

@[get_effects]
def Riscv_Stack.getEffects
    (_op : Riscv_Stack) (_props : Riscv_Stack.propertiesOf _op) : MemoryEffects :=
  .allocate

def Riscv_Stack.isConstantLike (_op : Riscv_Stack) : Bool :=
  false

def Riscv_Stack.hasSSADominance (_op : Riscv_Stack) (_index : Nat) : Bool :=
  true

#generate_dialect Riscv_Stack

instance : IsOpCode Riscv_Stack where
  fromName := Riscv_Stack.fromName
  name := Riscv_Stack.name
  propertiesOf := Riscv_Stack.propertiesOf
  fromAttrDict := Riscv_Stack.fromAttrDict
  toAttrDict := Riscv_Stack.toAttrDict

/--
Verify the local invariants of a `riscv_stack` operation in any operation-info
type containing the `riscv_stack` dialect.
-/
def Riscv_Stack.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Riscv_Stack] (opType : Riscv_Stack) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .alloca => do
    op.verifyPlainOpCounts ctx opIn 0 1
    op.verifyRISCVRegisterTypes ctx opIn
    let properties := op.getProperties! ctx.raw Riscv_Stack.alloca
    if properties.size.type.bitwidth ≠ 64 then
      throw "attribute 'size' must be a 64-bit signless integer attribute"
    if properties.size.value < 0 then
      throw "size must be nonnegative"
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "attribute 'alignment' must be a 64-bit signless integer attribute"
    if properties.alignment.value ≤ 0 then
      throw "alignment must be a positive power of two"
    let alignment := properties.alignment.value.toNat
    if alignment &&& (alignment - 1) ≠ 0 then
      throw "alignment must be a positive power of two"
    pure ()

instance : HasOpInfo Riscv_Stack where
  verifyLocalInvariants := Riscv_Stack.verifyLocalInvariants
  getEffects := Riscv_Stack.getEffects
  isConstantLike := Riscv_Stack.isConstantLike
  hasSSADominance := Riscv_Stack.hasSSADominance

end

end Veir
