module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Arith.Properties
public import Veir.Dialects.LLVM.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Arith where
| addi
| addui_extended
| andi
| ceildivsi
| ceildivui
| cmpi
| constant
| divsi
| divui
| extsi
| extui
| floordivsi
| maxsi
| maxui
| minsi
| minui
| muli
| mulsi_extended
| mului_extended
| ori
| remsi
| remui
| select
| shli
| shrsi
| shrui
| subi
| subui_extended
| trunci
| xori
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Arith.propertiesOf (op : Arith) : Type :=
match op with
| .constant => ArithConstantProperties
| .addi => ArithIntegerOverflowFlagsProperties
| .subi => ArithIntegerOverflowFlagsProperties
| .muli => ArithIntegerOverflowFlagsProperties
| .divsi => ExactProperties
| .divui => ExactProperties
| .cmpi => IcmpProperties
| .shli => ArithIntegerOverflowFlagsProperties
| .shrsi => ExactProperties
| .shrui => ExactProperties
| .ori => DisjointProperties
| .trunci => ArithIntegerOverflowFlagsProperties
| .extui => NnegProperties
| _ => Unit

def Arith.hasSideEffects (_op : Arith) (_props : Arith.propertiesOf _op) : Bool :=
  false

def Arith.readsMemory (_op : Arith) : Bool :=
  false

def Arith.isConstantLike (op : Arith) : Bool :=
  match op with
  | .constant => true
  | _ => false

def Arith.hasSSADominance (_op : Arith) (_index : Nat) : Bool :=
  true

instance : HasDialectOpInfo Arith where
  propertiesOf := Arith.propertiesOf
  hasSideEffects := Arith.hasSideEffects
  readsMemory := Arith.readsMemory
  isConstantLike := Arith.isConstantLike
  hasSSADominance := Arith.hasSSADominance

end

end Veir
