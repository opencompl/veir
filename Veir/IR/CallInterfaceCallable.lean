module

public import Veir.IR.Attribute

namespace Veir

public section

/-- The callee of a call: a symbol, or one of its operands. -/
inductive CallInterfaceCallable (α : Type) where
  | symbol (ref : FlatSymbolRefAttr)
  | value (value : α)
deriving Inhabited, Repr, DecidableEq

end

end Veir
