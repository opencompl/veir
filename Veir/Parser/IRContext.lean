module

public import Veir.Parser.StaticIR

/-! Compatibility name for the registry-free, well-formed parser context. -/
public section
namespace Veir.Parser.IR

abbrev Context := StaticIR.Context
abbrev empty := StaticIR.empty

end Veir.Parser.IR
