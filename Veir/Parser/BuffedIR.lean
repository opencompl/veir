module

public import Veir.Parser.IRContext

/-!
Parser construction requires erased pointer-bounds proofs and returns preservation
certificates. These aliases retain the construction namespace; there is no address registry
or permissive runtime-validation adapter.
-/
public section
namespace Veir.Parser.IR

export StaticIR (createOp createBlock createRegion insertBlock setAttributes replaceValue
  eraseOp eraseBlock replaceBlockUses)

end Veir.Parser.IR
