module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.RISCV_Stack.Properties
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

def Riscv_Stack.hasSideEffects
    (_op : Riscv_Stack) (_props : Riscv_Stack.propertiesOf _op) : Bool :=
  true

def Riscv_Stack.readsMemory
    (_op : Riscv_Stack) (_props : Riscv_Stack.propertiesOf _op) : Bool :=
  false

def Riscv_Stack.writesMemory
    (_op : Riscv_Stack) (_props : Riscv_Stack.propertiesOf _op) : Bool :=
  false

def Riscv_Stack.isConstantLike (_op : Riscv_Stack) : Bool :=
  false

def Riscv_Stack.hasSSADominance (_op : Riscv_Stack) (_index : Nat) : Bool :=
  true

#generate_dialect Riscv_Stack

instance : HasOpInfo Riscv_Stack where
  fromName := Riscv_Stack.fromName
  name := Riscv_Stack.name
  propertiesOf := Riscv_Stack.propertiesOf
  fromAttrDict := Riscv_Stack.fromAttrDict
  toAttrDict := Riscv_Stack.toAttrDict
  hasSideEffects := Riscv_Stack.hasSideEffects
  readsMemory := Riscv_Stack.readsMemory
  writesMemory := Riscv_Stack.writesMemory
  isConstantLike := Riscv_Stack.isConstantLike
  hasSSADominance := Riscv_Stack.hasSSADominance

end

end Veir
