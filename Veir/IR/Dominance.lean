module

public import Veir.Analysis.DataFlow.DominanceAnalysis

public section

namespace Veir

namespace BlockPtr

/--
Immediate dominator for the block entry, if the dominance analysis has
initialized this block.
-/
def immediateDominator?
    [FactSpec .dominator]
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  block.getIDom? dfCtx irCtx

end BlockPtr

end Veir
