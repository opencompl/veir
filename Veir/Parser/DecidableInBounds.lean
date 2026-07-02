import Veir.Parser.Parser
import Veir.IR.Basic
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSet

/-!
  Runtime decidable InBounds checks for the MLIR parser.

  All `InBounds` predicates are decidable (array membership checks), so we can
  check them at runtime and obtain proofs. This uses `PLift` to lift proofs
  into `Type`, enabling flat `let ⟨h⟩ ←` syntax instead of nested dependent `if`.
-/

namespace Veir.Parser

open Veir.Parser.ParserError

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {m : Type → Type} [Monad m] [MonadExcept ParserError m]

/-! ## Option.maybe decidability

For `ip.maybe P ctx` where `P` is decidable, the whole thing is decidable.
-/

instance instDecidableMaybe (p : α → β → Prop) [inst : ∀ a b, Decidable (p a b)] (x : Option α) (y : β) :
    Decidable (x.maybe p y) :=
  match x with
  | none => isTrue Option.maybe_none
  | some _ => decidable_of_iff _ Option.maybe_some.symm

/-- Check that a block is in bounds, returning the proof wrapped in PLift. -/
def checkBlockInBounds (block : BlockPtr) (ctx : IRContext OpInfo) :
    m (PLift (block.InBounds ctx)) :=
  if h : block.InBounds ctx then pure ⟨h⟩
  else throwString s!"internal error: block is not in bounds"

/-- Check that a block insertion point is in bounds. -/
def checkBlockInsertPointInBounds (ip : BlockInsertPoint) (ctx : IRContext OpInfo) :
    m (PLift (ip.InBounds ctx)) :=
  if h : ip.InBounds ctx then pure ⟨h⟩
  else throwString s!"internal error: block insertion point is not in bounds"

/-- Check that an optional insertion point satisfies maybe-InBounds. -/
def checkMaybeInsertPointInBounds (ip : Option InsertPoint) (ctx : IRContext OpInfo) :
    m (PLift (ip.maybe InsertPoint.InBounds ctx)) :=
  if h : ip.maybe InsertPoint.InBounds ctx then pure ⟨h⟩
  else throwString s!"internal error: optional insertion point is not in bounds"

/-- Check that a block has no arguments. -/
def checkBlockHasNoArgs (block : BlockPtr) (ctx : IRContext OpInfo) :
    m (PLift (block.getNumArguments! ctx = 0)) :=
  if h : block.getNumArguments! ctx = 0 then pure ⟨h⟩
  else throwString s!"internal error: block has {block.getNumArguments! ctx} arguments, expected 0"

/-- Check that an operation is in bounds. -/
def checkOpInBounds (op : OperationPtr) (ctx : IRContext OpInfo) :
    m (PLift (op.InBounds ctx)) :=
  if h : op.InBounds ctx then pure ⟨h⟩
  else throwString s!"internal error: operation is not in bounds"

/-- Check that a value is in bounds. -/
def checkValueInBounds (value : ValuePtr) (ctx : IRContext OpInfo) :
    m (PLift (value.InBounds ctx)) :=
  if h : value.InBounds ctx then pure ⟨h⟩
  else throwString s!"internal error: value is not in bounds"

/-- Check that two values are distinct. -/
def checkValuesNe (v₁ v₂ : ValuePtr) :
    m (PLift (v₁ ≠ v₂)) :=
  if h : v₁ ≠ v₂ then pure ⟨h⟩
  else throwString s!"internal error: values are unexpectedly equal"

/-- Check that an operation has no regions. -/
def checkOpNoRegions (op : OperationPtr) (ctx : IRContext OpInfo) :
    m (PLift (op.getNumRegions! ctx = 0)) :=
  if h : op.getNumRegions! ctx = 0 then pure ⟨h⟩
  else throwString s!"internal error: operation unexpectedly has regions"

/-- Check that an operation has no uses. -/
def checkOpNoUses (op : OperationPtr) (ctx : IRContext OpInfo) :
    m (PLift (op.hasUses! ctx = false)) :=
  if h : op.hasUses! ctx = false then pure ⟨h⟩
  else throwString s!"internal error: operation unexpectedly has uses"

/-- Check that a region is in bounds. -/
def checkRegionInBounds (region : RegionPtr) (ctx : IRContext OpInfo) :
    m (PLift (region.InBounds ctx)) :=
  if h : region.InBounds ctx then pure ⟨h⟩
  else throwString s!"internal error: region is not in bounds"

/-- Check that all values in an array are in bounds. -/
def checkAllValuesInBounds (values : Array ValuePtr) (ctx : IRContext OpInfo) :
    m (PLift (∀ v, v ∈ values → v.InBounds ctx)) :=
  if h : ∀ v, v ∈ values → v.InBounds ctx then pure ⟨h⟩
  else throwString s!"internal error: not all values are in bounds"

/-- Check that all blocks in an array are in bounds. -/
def checkAllBlocksInBounds (blocks : Array BlockPtr) (ctx : IRContext OpInfo) :
    m (PLift (∀ b, b ∈ blocks → b.InBounds ctx)) :=
  if h : ∀ b, b ∈ blocks → b.InBounds ctx then pure ⟨h⟩
  else throwString s!"internal error: not all blocks are in bounds"

/-- Check that all regions in an array are in bounds. -/
def checkAllRegionsInBounds (regions : Array RegionPtr) (ctx : IRContext OpInfo) :
    m (PLift (∀ r, r ∈ regions → r.InBounds ctx)) :=
  if h : ∀ r, r ∈ regions → r.InBounds ctx then pure ⟨h⟩
  else throwString s!"internal error: not all regions are in bounds"

end Veir.Parser
