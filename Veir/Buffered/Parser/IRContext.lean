module

public import Veir.Buffered.Parser.StaticIR

/-! Compatibility name for the registry-free, well-formed parser context. -/
public section
namespace Veir.Buffered.Parser.IR

abbrev Context := StaticIR.Context
abbrev empty := StaticIR.empty

end Veir.Buffered.Parser.IR
