/-
  Containment relationships for the IR tree.

  The IR tree hierarchy is: Operation → Region → Block → Operation → ...
  Parent pointers go upward: Block.parent → Region, Region.parent → Operation, Operation.parent → Block.

  This file defines an inductive `IRNode` type representing operations, blocks, or regions,
  and a `contains` function that determines whether one node is an ancestor of another by
  walking parent pointers.
-/
import Veir.IR.Basic

open Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- An IR node is an operation, block, or region. -/
inductive IRNode where
  | op (ptr : OperationPtr)
  | block (ptr : BlockPtr)
  | region (ptr : RegionPtr)
deriving DecidableEq, Repr

namespace IRNode

/-- Get the parent of an IR node, if it exists. -/
def parent! (node : IRNode) (ctx : IRContext OpInfo) : Option IRNode :=
  match node with
  | .op ptr => (ptr.get! ctx).parent |>.map (.block ·)
  | .block ptr => (ptr.get! ctx).parent |>.map (.region ·)
  | .region ptr => (ptr.get! ctx).parent |>.map (.op ·)

/--
  Check whether `ancestor` contains `descendant` in the IR tree by walking
  up from `descendant` through parent pointers.

  Uses fuel-based recursion for termination. The fuel parameter defaults to
  `ctx.nextID`, which is an upper bound on the number of nodes in the context.
  Returns `true` if `ancestor` is found on the path from `descendant` to the root,
  or if fuel is exhausted (conservative approximation).
-/
def contains! (ancestor descendant : IRNode) (ctx : IRContext OpInfo)
    (fuel : Nat := ctx.nextID) : Bool :=
  match fuel with
  | 0 => true  -- conservative: assume containment if we can't determine
  | n + 1 =>
    match descendant.parent! ctx with
    | none => false
    | some parentNode =>
      if parentNode == ancestor then true
      else contains! ancestor parentNode ctx n

/-- `ancestor.contains! descendant` with zero fuel is always true (conservative). -/
theorem contains!_fuel_zero (ancestor descendant : IRNode) (ctx : IRContext OpInfo) :
    contains! ancestor descendant ctx 0 = true := by
  rfl

/-- If `descendant` has no parent, it is not contained in any node. -/
theorem contains!_no_parent (ancestor descendant : IRNode) (ctx : IRContext OpInfo)
    {n : Nat} (h : descendant.parent! ctx = none) :
    contains! ancestor descendant ctx (n + 1) = false := by
  simp [contains!, h]

/-- If `descendant`'s parent is `ancestor`, then `ancestor` contains `descendant`. -/
theorem contains!_parent_eq (ancestor descendant : IRNode) (ctx : IRContext OpInfo)
    {n : Nat} (h : descendant.parent! ctx = some ancestor) :
    contains! ancestor descendant ctx (n + 1) = true := by
  simp [contains!, h]

end IRNode
