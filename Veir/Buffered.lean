module

public import Veir.Buffered.Parser.MlirParser
public import Veir.Buffered.Parser.PrintIR
public import Veir.Buffered.Rewriter.WellFormed

/-!
The buffered backend has a capacity-aware logical model, simulated pointers, and a verified
construction parser. Its declarations are separate from the upstream `Veir` IR and rewriter,
so both backends can be imported in the same environment. See `Veir/Buffered/README.md`.
-/
