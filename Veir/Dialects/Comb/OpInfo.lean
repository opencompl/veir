module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Comb.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Comb where
| add
| and
| concat
| divs
| divu
| extract
| icmp
| mods
| modu
| mul
| mux
| or
| parity
| replicate
| reverse
| shl
| shrs
| shru
| sub
| xor
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Comb.propertiesOf (op : Comb) : Type :=
match op with
| .extract => CombExtractProperties
| .icmp => CombIcmpProperties
| _ => Unit

def Comb.hasSideEffects (_op : Comb) (_props : Comb.propertiesOf _op) : Bool :=
  false

def Comb.readsMemory (_op : Comb) : Bool :=
  false

def Comb.isConstantLike (_op : Comb) : Bool :=
  false

def Comb.hasSSADominance (_op : Comb) (_index : Nat) : Bool :=
  true

instance : HasDialectOpInfo Comb where
  propertiesOf := Comb.propertiesOf
  hasSideEffects := Comb.hasSideEffects
  readsMemory := Comb.readsMemory
  isConstantLike := Comb.isConstantLike
  hasSSADominance := Comb.hasSSADominance

end

end Veir
