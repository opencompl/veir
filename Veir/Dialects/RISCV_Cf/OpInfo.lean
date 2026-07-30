module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.RISCV_Cf.Properties
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

def Riscv_Cf.hasSideEffects
    (_op : Riscv_Cf) (_props : Riscv_Cf.propertiesOf _op) : Bool :=
  true

def Riscv_Cf.readsMemory (_op : Riscv_Cf) : Bool :=
  false

def Riscv_Cf.isConstantLike (_op : Riscv_Cf) : Bool :=
  false

def Riscv_Cf.hasSSADominance (_op : Riscv_Cf) (_index : Nat) : Bool :=
  true

#generate_dialect Riscv_Cf

instance : HasDialectOpInfo Riscv_Cf where
  fromName := Riscv_Cf.fromName
  name := Riscv_Cf.name
  propertiesOf := Riscv_Cf.propertiesOf
  fromAttrDict := Riscv_Cf.fromAttrDict
  toAttrDict := Riscv_Cf.toAttrDict
  hasSideEffects := Riscv_Cf.hasSideEffects
  readsMemory := Riscv_Cf.readsMemory
  isConstantLike := Riscv_Cf.isConstantLike
  hasSSADominance := Riscv_Cf.hasSSADominance

end

end Veir
