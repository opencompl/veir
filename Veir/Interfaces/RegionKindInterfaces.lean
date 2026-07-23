module

public import Veir.IR.WellFormed

/-!
# RegionKindInterface

This file provides region-kind queries derived from the operation information
of a region's owning operation.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
Whether `region` uses SSA dominance according to its owning operation. Root
regions use SSA dominance, while other regions inherit the setting of their
position in the owning operation.
-/
@[expose]
def RegionPtr.hasSSADominance (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Bool :=
  match (region.get! ctx.raw).parent with
  | none => true
  | some parent =>
      HasOpInfo.hasSSADominance (parent.getOpType! ctx.raw)
        ((parent.get! ctx.raw).regions.idxOf region)

end Veir
