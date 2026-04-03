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

/-- An IR node is in bounds if its pointer is in bounds in the context. -/
def InBounds (node : IRNode) (ctx : IRContext OpInfo) : Prop :=
  match node with
  | .op ptr => ptr.InBounds ctx
  | .block ptr => ptr.InBounds ctx
  | .region ptr => ptr.InBounds ctx

instance : Decidable (InBounds node (ctx : IRContext OpInfo)) := by
  unfold InBounds; cases node <;> infer_instance

theorem InBounds.op {ptr : OperationPtr} (h : ptr.InBounds (ctx : IRContext OpInfo)) :
    InBounds (.op ptr) ctx := h

theorem InBounds.block {ptr : BlockPtr} (h : ptr.InBounds (ctx : IRContext OpInfo)) :
    InBounds (.block ptr) ctx := h

theorem InBounds.region {ptr : RegionPtr} (h : ptr.InBounds (ctx : IRContext OpInfo)) :
    InBounds (.region ptr) ctx := h

/-- Get the parent of an IR node, if it exists. -/
def parent! (node : IRNode) (ctx : IRContext OpInfo) : Option IRNode :=
  match node with
  | .op ptr => (ptr.get! ctx).parent |>.map (.block ·)
  | .block ptr => (ptr.get! ctx).parent |>.map (.region ·)
  | .region ptr => (ptr.get! ctx).parent |>.map (.op ·)

/-- Get the parent of an IR node (safe version with InBounds proof). -/
def parent (node : IRNode) (ctx : IRContext OpInfo) (h : node.InBounds ctx := by grind) : Option IRNode :=
  match node, h with
  | .op ptr, h => (ptr.get ctx h).parent |>.map (.block ·)
  | .block ptr, h => (ptr.get ctx h).parent |>.map (.region ·)
  | .region ptr, h => (ptr.get ctx h).parent |>.map (.op ·)

/-- `parent!` agrees with `parent` when the node is in bounds. -/
theorem parent!_eq_parent (node : IRNode) (ctx : IRContext OpInfo) (h : node.InBounds ctx) :
    node.parent! ctx = node.parent ctx h := by
  cases node <;> simp [parent!, parent] <;> grind

/--
  Check whether `ancestor` contains `descendant` in the IR tree by walking
  up from `descendant` through parent pointers.

  Uses fuel-based recursion for termination. The fuel parameter defaults to
  `ctx.nextID`, which is an upper bound on the number of nodes in the context.
  Returns `some true` if `ancestor` is found, `some false` if the root is reached
  without finding it, or `none` if fuel is exhausted.
-/
def contains! (ancestor descendant : IRNode) (ctx : IRContext OpInfo)
    (fuel : Nat := ctx.nextID) : Option Bool :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match descendant.parent! ctx with
    | none => some false
    | some parentNode =>
      if parentNode == ancestor then some true
      else contains! ancestor parentNode ctx n

/-- If `descendant` has no parent, it is not contained in any node. -/
theorem contains!_no_parent (ancestor descendant : IRNode) (ctx : IRContext OpInfo)
    {n : Nat} (h : descendant.parent! ctx = none) :
    contains! ancestor descendant ctx (n + 1) = some false := by
  simp [contains!, h]

/-- If `descendant`'s parent is `ancestor`, then `ancestor` contains `descendant`. -/
theorem contains!_parent_eq (ancestor descendant : IRNode) (ctx : IRContext OpInfo)
    {n : Nat} (h : descendant.parent! ctx = some ancestor) :
    contains! ancestor descendant ctx (n + 1) = some true := by
  simp [contains!, h]

/-- Unfolding lemma: if `descendant` has parent `p ≠ ancestor`, then containment
    reduces to checking `ancestor` against `p` with one less fuel. -/
theorem contains!_step (ancestor descendant : IRNode) (ctx : IRContext OpInfo)
    {n : Nat} {p : IRNode} (hp : descendant.parent! ctx = some p) (hne : (p == ancestor) = false) :
    contains! ancestor descendant ctx (n + 1) = contains! ancestor p ctx n := by
  simp [contains!, hp, hne]

/--
  Safe version of `contains!` that uses `parent` (with InBounds proof) instead of `parent!`.
-/
def contains (ancestor descendant : IRNode) (ctx : IRContext OpInfo)
    (h : descendant.InBounds ctx) (fuel : Nat := ctx.nextID) : Option Bool :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match descendant.parent ctx h with
    | none => some false
    | some parentNode =>
      if parentNode == ancestor then some true
      else if hb : parentNode.InBounds ctx then
        contains ancestor parentNode ctx hb n
      else none

end IRNode
