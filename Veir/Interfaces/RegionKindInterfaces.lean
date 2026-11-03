module

public import Veir.IR.WellFormed
public import Veir.IR.OpInfo

/-!
# RegionKindInterface

This file provides region-kind queries derived from the operation information
of a region's owning operation.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
The region kind `region` is declared to have by its owning operation. A root
region has no owner and is an SSACFG region.
-/
@[expose]
def RegionPtr.getRegionKind (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : RegionKind :=
  match region.getParent! ctx.raw with
  | none => .SSACFG
  | some parent =>
      HasOpInfo.getRegionKind (parent.getOpType! ctx.raw)
        ((parent.getRegions! ctx.raw).idxOf region)

/--
Whether `region` uses SSA dominance according to its owning operation. Root
regions use SSA dominance, while other regions inherit the setting of their
position in the owning operation.

A region that does not hold exactly one block always uses SSA dominance,
whatever its owner declares: only a CFG gives the blocks an order, and an
operation that declares a graph region is separately required to keep it to a
single block.
-/
@[expose]
def RegionPtr.hasSSADominance (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Bool :=
  match region.getFirstBlock! ctx.raw, region.getParent! ctx.raw with
  | some first, some parent =>
      if region.getLastBlock! ctx.raw ≠ some first then true
      else
        HasOpInfo.hasSSADominance (parent.getOpType! ctx.raw)
          ((parent.getRegions! ctx.raw).idxOf region)
  | _, _ => true

/-- Every block in a region without SSA dominance is its entry block. -/
theorem RegionPtr.firstBlock_of_not_hasSSADominance
    {region : RegionPtr} {block : BlockPtr} {ctx : WfIRContext OpInfo}
    (noSSA : region.hasSSADominance ctx = false)
    (parent : block.getParent! ctx.raw = some region) :
    region.getFirstBlock! ctx.raw = some block := by
  cases first : region.getFirstBlock! ctx.raw with
  | none => simp [hasSSADominance, first] at noSSA
  | some entry =>
    have last : region.getLastBlock! ctx.raw = some entry := by
      cases owner : region.getParent! ctx.raw <;>
        grind [hasSSADominance]
    have same := region.block_eq_of_first_eq_last ctx.wellFormed parent first last
    grind

grind_pattern RegionPtr.firstBlock_of_not_hasSSADominance =>
    region.hasSSADominance ctx, block.getParent! ctx.raw, some region where
  guard region.hasSSADominance ctx = false
  guard block.getParent! ctx.raw = some region

end Veir
