module

public import Veir.Buffered.Parser.MlirParser

/-!
Compatibility exports for the buffered parser's original entry point and safety theorem.
The upstream parser remains in `Veir.Parser.MlirParser`, with its public source-input API in
`Veir.Input`. The two APIs return different IR representations.
-/
public section
namespace Veir.Parser

export Veir.Buffered.Parser (SourceInfo parseSourceString parseSourceString_safe)

end Veir.Parser
