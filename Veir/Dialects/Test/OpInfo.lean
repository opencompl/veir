module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Test where
| test
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Test.propertiesOf (_op : Test) : Type :=
  Unit

def Test.hasSideEffects (_op : Test) (_props : Test.propertiesOf _op) : Bool :=
  true

def Test.readsMemory (_op : Test) : Bool :=
  false

def Test.isConstantLike (_op : Test) : Bool :=
  false

def Test.hasSSADominance (_op : Test) (_index : Nat) : Bool :=
  false

instance : HasDialectOpInfo Test where
  propertiesOf := Test.propertiesOf
  hasSideEffects := Test.hasSideEffects
  readsMemory := Test.readsMemory
  isConstantLike := Test.isConstantLike
  hasSSADominance := Test.hasSSADominance

end

end Veir
