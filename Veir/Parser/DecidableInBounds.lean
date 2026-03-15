/-
  Runtime decidable InBounds checks for the MLIR parser.

  All `InBounds` predicates are decidable (array membership checks), so we can
  check them at runtime and obtain proofs. This uses `PLift` to lift proofs
  into `Type`, enabling flat `let ⟨h⟩ ←` syntax instead of nested dependent `if`.
-/
import Veir.Parser.Parser
import Veir.IR.Basic
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSetInBounds

namespace Veir.Parser

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-! ## Decidable instances for InsertPoint types

InsertPoint.InBounds and BlockInsertPoint.InBounds reduce to underlying pointer
InBounds checks, so they are also decidable.
-/

instance : Decidable (InsertPoint.InBounds ip (ctx : IRContext OpInfo)) := by
  cases ip <;> simp only [InsertPoint.InBounds] <;> infer_instance

instance : Decidable (BlockInsertPoint.InBounds bip (ctx : IRContext OpInfo)) := by
  cases bip <;> simp only [BlockInsertPoint.InBounds] <;> infer_instance

/-! ## Option.maybe decidability

For `ip.maybe P ctx` where `P` is decidable, the whole thing is decidable.
-/

instance instDecidableMaybe (p : α → β → Prop) [inst : ∀ a b, Decidable (p a b)] (x : Option α) (y : β) :
    Decidable (x.maybe p y) := by
  cases x with
  | none =>
    apply isTrue
    intro z hz
    cases hz -- none = some z is impossible
  | some a =>
    simp only [Option.maybe]
    cases inst a y with
    | isTrue h =>
      apply isTrue
      intro z hz
      cases hz
      exact h
    | isFalse h =>
      apply isFalse
      intro hcontra
      exact h (hcontra a rfl)

/-! ## Flat proof checking with PLift

The key insight: use `PLift` to lift `Prop` into `Type`, enabling the flat
`let ... | ...` pattern instead of nested `if h : P then ... else ...`.
-/

/-- Check that a block is in bounds, returning the proof wrapped in PLift. -/
def checkBlockInBounds (block : BlockPtr) (ctx : IRContext OpInfo) :
    Except String (PLift (block.InBounds ctx)) :=
  if h : block.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: block is not in bounds"

/-- Check that a block insertion point is in bounds. -/
def checkBlockInsertPointInBounds (ip : BlockInsertPoint) (ctx : IRContext OpInfo) :
    Except String (PLift (ip.InBounds ctx)) :=
  if h : ip.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: block insertion point is not in bounds"

/-- Check that an optional block insertion point satisfies maybe-InBounds. -/
def checkMaybeBlockInsertPointInBounds (ip : Option BlockInsertPoint) (ctx : IRContext OpInfo) :
    Except String (PLift (ip.maybe BlockInsertPoint.InBounds ctx)) :=
  if h : ip.maybe BlockInsertPoint.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: optional block insertion point is not in bounds"

/-- Check that an optional insertion point satisfies maybe-InBounds. -/
def checkMaybeInsertPointInBounds (ip : Option InsertPoint) (ctx : IRContext OpInfo) :
    Except String (PLift (ip.maybe InsertPoint.InBounds ctx)) :=
  if h : ip.maybe InsertPoint.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: optional insertion point is not in bounds"

/-- Check that a block has no arguments. -/
def checkBlockHasNoArgs (block : BlockPtr) (ctx : IRContext OpInfo) :
    Except String (PLift (block.getNumArguments! ctx = 0)) :=
  if h : block.getNumArguments! ctx = 0 then .ok ⟨h⟩
  else .error s!"internal error: block has {block.getNumArguments! ctx} arguments, expected 0"

/-- Check that an operation is in bounds. -/
def checkOpInBounds (op : OperationPtr) (ctx : IRContext OpInfo) :
    Except String (PLift (op.InBounds ctx)) :=
  if h : op.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: operation is not in bounds"

/-- Check that a value is in bounds. -/
def checkValueInBounds (value : ValuePtr) (ctx : IRContext OpInfo) :
    Except String (PLift (value.InBounds ctx)) :=
  if h : value.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: value is not in bounds"

/-- Check that a region is in bounds. -/
def checkRegionInBounds (region : RegionPtr) (ctx : IRContext OpInfo) :
    Except String (PLift (region.InBounds ctx)) :=
  if h : region.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: region is not in bounds"

/-- Check that all values in an array are in bounds. -/
def checkAllValuesInBounds (values : Array ValuePtr) (ctx : IRContext OpInfo) :
    Except String (PLift (∀ v, v ∈ values → v.InBounds ctx)) :=
  if h : ∀ v, v ∈ values → v.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: not all values are in bounds"

/-- Check that all blocks in an array are in bounds. -/
def checkAllBlocksInBounds (blocks : Array BlockPtr) (ctx : IRContext OpInfo) :
    Except String (PLift (∀ b, b ∈ blocks → b.InBounds ctx)) :=
  if h : ∀ b, b ∈ blocks → b.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: not all blocks are in bounds"

/-- Check that all regions in an array are in bounds. -/
def checkAllRegionsInBounds (regions : Array RegionPtr) (ctx : IRContext OpInfo) :
    Except String (PLift (∀ r, r ∈ regions → r.InBounds ctx)) :=
  if h : ∀ r, r ∈ regions → r.InBounds ctx then .ok ⟨h⟩
  else .error s!"internal error: not all regions are in bounds"

/-! ## Lifting to Monads -/

/-- Lift an Except computation to any MonadExcept. -/
def liftExcept [Monad m] [MonadExcept String m] (e : Except String α) : m α :=
  match e with
  | .ok a => pure a
  | .error err => throw err

end Veir.Parser
