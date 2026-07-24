module

public import Veir.IR.WellFormed

/-!
# Operation, Block, and Region Nesting

Heterogeneous nesting propositions between operations, blocks, and regions, such as
parents, ancestors, and parent paths, are defined in this file.

The nesting API is defined in terms of the `IRNode` type, which is a sum type of `OperationPtr`,
`BlockPtr`, and `RegionPtr`. `IRNode.Ancestor` is defined by the existence of an explicit
`IRNode.ParentPath` witness.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {rawCtx : IRContext OpInfo}
variable {ctx : WfIRContext OpInfo}

/-! ## `IRNode` -/

/-- The three kind of nodes that exist in the IR: operations, blocks, and regions. -/
inductive IRNodeKind where
  | operation
  | block
  | region
deriving DecidableEq

/-- An IR node, either an operation, block, or region. -/
inductive IRNode where
  | operation (ptr : OperationPtr)
  | block (ptr : BlockPtr)
  | region (ptr : RegionPtr)
deriving DecidableEq

namespace IRNode

/-- The kind of an IR node. -/
@[expose]
def kind : IRNode → IRNodeKind
  | .operation _ => .operation
  | .block _ => .block
  | .region _ => .region

/-- Whether the underlying pointer of an IRNode is in bounds. -/
def InBounds (ptr : IRNode) (ctx : IRContext OpInfo) : Prop :=
  match ptr with
  | .operation ptr => ptr.InBounds ctx
  | .block ptr => ptr.InBounds ctx
  | .region ptr => ptr.InBounds ctx

@[simp, grind =]
theorem inBounds_operation : (IRNode.operation ptr).InBounds rawCtx ↔ ptr.InBounds rawCtx := by rfl

@[simp, grind =]
theorem inBounds_block : (IRNode.block ptr).InBounds rawCtx ↔ ptr.InBounds rawCtx := by rfl

@[simp, grind =]
theorem inBounds_region : (IRNode.region ptr).InBounds rawCtx ↔ ptr.InBounds rawCtx := by rfl

/-- The parent of an IR node. -/
@[expose]
def parent! (ptr : IRNode) (ctx : WfIRContext OpInfo) : Option IRNode :=
  match ptr with
  | .operation ptr => (ptr.get! ctx.raw).parent.map .block
  | .block ptr => (ptr.get! ctx.raw).parent.map .region
  | .region ptr => (ptr.get! ctx.raw).parent.map .operation

@[simp, grind =]
theorem parent!_operation :
  (IRNode.operation ptr).parent! ctx = (ptr.get! ctx.raw).parent.map .block := by rfl

@[simp, grind =]
theorem parent!_block :
  (IRNode.block ptr).parent! ctx = (ptr.get! ctx.raw).parent.map .region := by rfl

@[simp, grind =]
theorem parent!_region :
  (IRNode.region ptr).parent! ctx = (ptr.get! ctx.raw).parent.map .operation := by rfl

/-- An IR node is different from its immediate parent. -/
theorem child_ne_parent {child parent : IRNode}
    (immediate : child.parent! ctx = some parent) :
    child ≠ parent := by
  cases child <;> cases parent <;> simp [IRNode.parent!] at immediate ⊢

/-! ## `ParentPath` -/

/--
A path following nesting parent edges, witnessed by its IR nodes. A path has as first element
its descendant and as a last element its ancestor. A path can be from a node to itself.
-/
inductive ParentPath (ctx : WfIRContext OpInfo) :
    IRNode → IRNode → List IRNode → Prop where
  | single {ptr : IRNode} :
      ParentPath ctx ptr ptr [ptr]
  | cons {ancestor child parent : IRNode} {nodes : List IRNode}
      (immediate : child.parent! ctx = some parent)
      (tail : ParentPath ctx ancestor parent nodes) :
      ParentPath ctx ancestor child (child :: nodes)

namespace ParentPath

variable {ancestor ancestor₁ ancestor₂ middle descendant : IRNode}
variable {nodes nodes₁ nodes₂ upperNodes lowerNodes : List IRNode}

/-- A parent path's node list is not nil. -/
@[simp]
theorem ne_nil (path : ParentPath ctx ancestor descendant nodes) :
    nodes ≠ [] := by
  cases path <;> grind

/-- The first node in a parent path is its descendant. -/
@[simp]
theorem head?_eq (path : ParentPath ctx ancestor descendant nodes) :
    nodes.head? = some descendant := by
  cases path <;> grind

/-- The last node in a parent path is its ancestor. -/
@[simp]
theorem getLast?_eq (path : ParentPath ctx ancestor descendant nodes) :
    nodes.getLast? = some ancestor := by
  induction path <;> grind

/-- The ancestor reached by a fixed-length parent path is unique. -/
theorem unique_ancestor_of_eq_length
    (left : ParentPath ctx ancestor₁ descendant nodes₁)
    (right : ParentPath ctx ancestor₂ descendant nodes₂)
    (lengthEq : nodes₁.length = nodes₂.length) :
    ancestor₁ = ancestor₂ := by
  induction left generalizing nodes₂ <;>
    grind [ne_nil, cases ParentPath]

/-- Concatenate two parent paths that meet at `middle`. -/
theorem trans
    (upper : ParentPath ctx ancestor middle upperNodes)
    (lower : ParentPath ctx middle descendant lowerNodes) :
    ParentPath ctx ancestor descendant (lowerNodes ++ upperNodes.tail) := by
  induction lower with
  | single =>
      cases upper with
      | single => exact .single
      | cons immediate tail => exact .cons immediate tail
  | cons immediate _ ih =>
      exact ParentPath.cons immediate ih

end ParentPath

/-! ## `Ancestor` -/

/-- Reflexive, finite ancestry through nesting parent edges. -/
def Ancestor (ancestor descendant : IRNode)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ nodes, ParentPath ctx ancestor descendant nodes

/-- Non-reflexive, finite ancestry through nesting parent edges. -/
@[expose]
def ProperAncestor (ancestor descendant : IRNode)
    (ctx : WfIRContext OpInfo) : Prop :=
  ancestor.Ancestor descendant ctx ∧ ancestor ≠ descendant

/-- Definition of proper ancestry. -/
theorem properAncestor_def {ancestor descendant : IRNode} :
    ancestor.ProperAncestor descendant ctx ↔
      ancestor.Ancestor descendant ctx ∧ ancestor ≠ descendant := by
  rfl

namespace Ancestor

variable {ancestor middle descendant parent child : IRNode}
variable {nodes : List IRNode}

/-- A parent path witnesses ancestry. -/
@[grind →]
theorem of_parentPath
    (path : ParentPath ctx ancestor descendant nodes) :
    ancestor.Ancestor descendant ctx := by
  grind [Ancestor]

/-- An ancestry proof has an explicit parent-path witness. -/
theorem exists_parentPath
    (ancestry : ancestor.Ancestor descendant ctx) :
    ∃ nodes, ParentPath ctx ancestor descendant nodes := by
  grind [Ancestor]

/-- Every IR node is its own ancestor. -/
@[simp, grind .]
theorem refl : ancestor.Ancestor ancestor ctx :=
  .of_parentPath .single

/-- A parent is an ancestor. -/
theorem of_parent (immediate : child.parent! ctx = some parent) :
    parent.Ancestor child ctx :=
  .of_parentPath (.cons immediate .single)

/-- Ancestry is transitive. -/
theorem trans
    (upper : ancestor.Ancestor middle ctx)
    (lower : middle.Ancestor descendant ctx) :
    ancestor.Ancestor descendant ctx := by
  have ⟨_, upper⟩ := upper.exists_parentPath
  have ⟨_, lower⟩ := lower.exists_parentPath
  exact .of_parentPath (upper.trans lower)

/-- A parent of an ancestor is an ancestor. -/
theorem trans_parent_ancestor
    (immediate : middle.parent! ctx = some parent)
    (ancestry : middle.Ancestor descendant ctx) :
    parent.Ancestor descendant ctx := by
  apply Ancestor.trans (middle := middle) <;> grind [Ancestor.of_parent]

/-- The ancestor of a parent is an ancestor. -/
theorem trans_ancestor_parent
    (immediate : child.parent! ctx = some parent)
    (ancestry : ancestor.Ancestor parent ctx) :
    ancestor.Ancestor child ctx := by
  apply Ancestor.trans (middle := parent) <;> grind [Ancestor.of_parent]

/-- A computed operation parent is an ancestor through one complete nesting cycle. -/
theorem of_getParentOp!_eq_some {child parent : OperationPtr}
    (immediate : child.getParentOp! ctx.raw = some parent) :
    IRNode.Ancestor (.operation parent) (.operation child) ctx := by
  have ⟨bl, reg, childParent, blockParent, regionParent⟩ :=
    (OperationPtr.getParentOp!_eq_some_iff.mp immediate)
  apply IRNode.Ancestor.trans_parent_ancestor (middle := .region reg); grind
  apply IRNode.Ancestor.trans_parent_ancestor (middle := .block bl); grind
  apply IRNode.Ancestor.trans_parent_ancestor (middle := .operation child); grind
  grind

/-- An ancestry relation is either proper or relates a node to itself. -/
theorem proper_or_eq
    (ancestry : ancestor.Ancestor descendant ctx) :
    ancestor.ProperAncestor descendant ctx ∨ ancestor = descendant := by
  by_cases ancestorEq : ancestor = descendant
  · exact Or.inr ancestorEq
  · exact Or.inl ⟨ancestry, ancestorEq⟩

end Ancestor

namespace ProperAncestor

variable {ancestor descendant parent child : IRNode}

/-- An ancestry proof with distinct endpoints is proper ancestry. -/
theorem of_ancestor_ne
    (ancestry : ancestor.Ancestor descendant ctx)
    (ancestorNeDescendant : ancestor ≠ descendant) :
    ancestor.ProperAncestor descendant ctx :=
  ⟨ancestry, ancestorNeDescendant⟩

/-- Proper ancestry implies ancestry. -/
@[grind →]
theorem toAncestor
    (ancestry : ancestor.ProperAncestor descendant ctx) :
    ancestor.Ancestor descendant ctx :=
  ancestry.1

/-- The endpoints of proper ancestry are distinct. -/
@[grind →]
theorem ne
    (ancestry : ancestor.ProperAncestor descendant ctx) :
    ancestor ≠ descendant :=
  ancestry.2

/-- No IR node is its own proper ancestor. -/
@[simp]
theorem irrefl : ¬ancestor.ProperAncestor ancestor ctx := by
  simp [ProperAncestor]

/-- An immediate parent is a proper ancestor. -/
theorem of_parent (immediate : child.parent! ctx = some parent) :
    parent.ProperAncestor child ctx :=
  ⟨Ancestor.of_parent immediate, (child_ne_parent immediate).symm⟩

end ProperAncestor

end IRNode

end Veir
