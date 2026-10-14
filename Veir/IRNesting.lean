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

variable {OpInfo : Type} [IsOpCode OpInfo]
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

instance : Coe OperationPtr IRNode where
  coe ptr := IRNode.operation ptr
instance : Coe BlockPtr IRNode where
  coe ptr := IRNode.block ptr
instance : Coe RegionPtr IRNode where
  coe ptr := IRNode.region ptr

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
  | .operation ptr => (ptr.getParent! ctx.raw).map .block
  | .block ptr => (ptr.getParent! ctx.raw).map .region
  | .region ptr => (ptr.getParent! ctx.raw).map .operation

@[simp, grind =]
theorem parent!_operation :
  (IRNode.operation ptr).parent! ctx = (ptr.getParent! ctx.raw).map .block := by rfl

@[simp, grind =]
theorem parent!_block :
  (IRNode.block ptr).parent! ctx = (ptr.getParent! ctx.raw).map .region := by rfl

@[simp, grind =]
theorem parent!_region :
  (IRNode.region ptr).parent! ctx = (ptr.getParent! ctx.raw).map .operation := by rfl

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
      (tail : ParentPath ctx parent ancestor nodes) :
      ParentPath ctx child ancestor (child :: nodes)

namespace ParentPath

variable {ancestor ancestor₁ ancestor₂ middle descendant : IRNode}
variable {nodes nodes₁ nodes₂ upperNodes lowerNodes : List IRNode}

/-- A parent path's node list is not nil. -/
@[simp]
theorem ne_nil (path : ParentPath ctx descendant ancestor nodes) :
    nodes ≠ [] := by
  cases path <;> grind

/-- The first node in a parent path is its descendant. -/
@[simp]
theorem head?_eq (path : ParentPath ctx descendant ancestor nodes) :
    nodes.head? = some descendant := by
  cases path <;> grind

/-- The last node in a parent path is its ancestor. -/
@[simp]
theorem getLast?_eq (path : ParentPath ctx descendant ancestor nodes) :
    nodes.getLast? = some ancestor := by
  induction path <;> grind

/-- The ancestor reached by a fixed-length parent path is unique. -/
theorem unique_ancestor_of_eq_length
    (left : ParentPath ctx descendant ancestor₁ nodes₁)
    (right : ParentPath ctx descendant ancestor₂ nodes₂)
    (lengthEq : nodes₁.length = nodes₂.length) :
    ancestor₁ = ancestor₂ := by
  induction left generalizing nodes₂ <;>
    grind [ne_nil, cases ParentPath]

/-- Concatenate two parent paths that meet at `middle`. -/
theorem trans
    (lower : ParentPath ctx descendant middle lowerNodes)
    (upper : ParentPath ctx middle ancestor upperNodes) :
    ParentPath ctx descendant ancestor (lowerNodes ++ upperNodes.tail) := by
  induction lower with
  | single => grind [cases ParentPath]
  | cons immediate _ ih => exact ParentPath.cons immediate (ih upper)

/-- Split a parent path at the descendant parent node. -/
theorem split_of_parent
    (path : ParentPath ctx descendant ancestor nodes)
    (hparent : descendant.parent! ctx = some parent)
    (hne : descendant ≠ ancestor)
    : ParentPath ctx parent ancestor nodes.tail := by
  cases path <;> grind

grind_pattern split_of_parent =>
    ParentPath ctx descendant ancestor nodes, descendant.parent! ctx, some parent where
  guard descendant.parent! ctx = some parent

end ParentPath

/-! ## `Ancestor` -/

/-- Reflexive, finite ancestry through nesting parent edges. -/
def Ancestor (ancestor descendant : IRNode)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ nodes, ParentPath ctx descendant ancestor nodes

/-- Non-reflexive, finite ancestry through nesting parent edges. -/
def ProperAncestor (ancestor descendant : IRNode)
    (ctx : WfIRContext OpInfo) : Prop :=
  ancestor.Ancestor descendant ctx ∧ ancestor ≠ descendant

/-- Definition of proper ancestry. -/
theorem properAncestor_def {ancestor descendant : IRNode} :
    ancestor.ProperAncestor descendant ctx ↔
      ancestor.Ancestor descendant ctx ∧ ancestor ≠ descendant := by
  rfl

/-! Conversions between Ancestor and ProperAncestor. -/

/-- A distinct ancestor is a proper ancestor. -/
theorem Ancestor.toProperAncestor {ancestor : IRNode}
    (ancestry : ancestor.Ancestor descendant ctx)
    (ancestorNeDescendant : ancestor ≠ descendant) :
    ancestor.ProperAncestor descendant ctx :=
  ⟨ancestry, ancestorNeDescendant⟩

/-- Proper ancestry implies ancestry. -/
@[grind →]
theorem ProperAncestor.toAncestor {ancestor : IRNode}
    (ancestry : ancestor.ProperAncestor descendant ctx) :
    ancestor.Ancestor descendant ctx :=
  ancestry.1

namespace Ancestor

variable {ancestor middle descendant parent child : IRNode}
variable {nodes : List IRNode}

/-- A parent path witnesses ancestry. -/
@[grind →]
theorem of_parentPath
    (path : ParentPath ctx descendant ancestor nodes) :
    ancestor.Ancestor descendant ctx := by
  grind [Ancestor]

/-- An ancestry proof has an explicit parent-path witness. -/
theorem exists_parentPath
    (ancestry : ancestor.Ancestor descendant ctx) :
    ∃ nodes, ParentPath ctx descendant ancestor nodes := by
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
  exact .of_parentPath (lower.trans upper)

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

theorem proper_of_ne
    (ancestry : ancestor.Ancestor descendant ctx)
    (ancestorNeDescendant : ancestor ≠ descendant) :
    ancestor.ProperAncestor descendant ctx :=
  ⟨ancestry, ancestorNeDescendant⟩

end Ancestor

namespace ProperAncestor

variable {ancestor descendant parent child child₁ child₂ : IRNode}

/-- A proper ancestor is distinct. -/
@[grind →]
theorem ne
    (ancestry : ancestor.ProperAncestor descendant ctx) :
    ancestor ≠ descendant :=
  ancestry.2

/-- No IR node is its own proper ancestor. -/
@[simp, grind .]
theorem irrefl : ¬ancestor.ProperAncestor ancestor ctx := by
  simp [ProperAncestor]

/-- An immediate parent is a proper ancestor. -/
@[grind →]
theorem of_parent (immediate : child.parent! ctx = some parent) :
    parent.ProperAncestor child ctx :=
  ⟨Ancestor.of_parent immediate, (child_ne_parent immediate).symm⟩

theorem ancestor_of_parent_descendant
    (hAncestor : ancestor.ProperAncestor descendant ctx)
    (hParent : descendant.parent! ctx = some parent) :
    ancestor.Ancestor parent ctx := by
  obtain ⟨nodes, path⟩ := hAncestor.toAncestor.exists_parentPath
  grind

grind_pattern ancestor_of_parent_descendant =>
    IRNode.ProperAncestor ancestor descendant ctx, descendant.parent! ctx, some parent where
  guard descendant.parent! ctx = some parent

end ProperAncestor

@[grind →]
theorem Ancestor.of_ancestor_parent_of_parent_descendant {ancestor : IRNode}
    (hAncestor : ancestor.Ancestor parent ctx)
    (hParent : descendant.parent! ctx = some parent) :
    ancestor.Ancestor descendant ctx := by
  obtain ⟨nodes, path⟩ := hAncestor.exists_parentPath
  apply Ancestor.of_parentPath (nodes := descendant::nodes)
  grind [ParentPath.cons]

grind_pattern Ancestor.of_ancestor_parent_of_parent_descendant =>
    ancestor.Ancestor parent ctx, descendant.parent! ctx, some parent where
  guard descendant.parent! ctx = some parent

/--
A proper block ancestor of one block is an ancestor of every block in the same region.
-/
theorem Ancestor.of_same_parent_of_properAncestor {ancestor : IRNode}
    (hAncestor : ancestor.ProperAncestor child₁ ctx)
    (hParent₁ : child₁.parent! ctx = some parent)
    (hParent₂ : child₂.parent! ctx = some parent) :
    ancestor.Ancestor child₂ ctx := by
  grind

/-- `node` is rooted at `root` if `root` is an ancestor of `node` and `root` has no parent. -/
def RootedAt (node root : IRNode) (ctx : WfIRContext OpInfo) : Prop :=
  root.Ancestor node ctx ∧ root.parent! ctx = none

@[grind →]
theorem RootedAt.ancestor {node root: IRNode} (hRooted : node.RootedAt root ctx) :
    root.Ancestor node ctx :=
  hRooted.1

theorem RootedAt.root_parent_eq {node root: IRNode} (hRooted : node.RootedAt root ctx) :
    root.parent! ctx = none :=
  hRooted.2

/-- An ancestor of a rooted node is rooted at the same root. -/
theorem RootedAt.of_ancestor {node ancestor : IRNode}
    (hRooted : node.RootedAt root ctx) (hAncestor : ancestor.Ancestor node ctx) :
    ancestor.RootedAt root ctx := by
  obtain ⟨nodes, path⟩ := hAncestor.exists_parentPath
  clear hAncestor
  induction path with
  | single => exact hRooted
  | @cons ancestor descendant parent nodes immediate tail ih =>
    apply ih
    refine ⟨?_, hRooted.2⟩
    have hNe : root ≠ descendant := by grind [RootedAt]
    exact (hRooted.1.toProperAncestor hNe).ancestor_of_parent_descendant immediate

/-- Nodes with the same parent share a root. -/
theorem RootedAt.of_same_parent {node sibling parent : IRNode}
    (hRooted : node.RootedAt root ctx)
    (hParent : node.parent! ctx = some parent)
    (hSiblingParent : sibling.parent! ctx = some parent) :
    sibling.RootedAt root ctx := by
  have parentRooted := hRooted.of_ancestor (Ancestor.of_parent hParent)
  exact ⟨Ancestor.of_ancestor_parent_of_parent_descendant parentRooted.1 hSiblingParent,
    parentRooted.2⟩

/-- A child of a rooted node is rooted at the same root. -/
theorem RootedAt.of_parent {node parent : IRNode}
    (hRooted : parent.RootedAt root ctx) (hParent : node.parent! ctx = some parent) :
    node.RootedAt root ctx :=
  ⟨Ancestor.of_ancestor_parent_of_parent_descendant hRooted.1 hParent, hRooted.2⟩

grind_pattern RootedAt.of_parent =>
    parent.RootedAt root ctx, node.parent! ctx where
  guard node.parent! ctx = some parent

end IRNode

@[simp, grind]
abbrev OperationPtr.Ancestor (ancestor : OperationPtr) (descendant : IRNode) (ctx : WfIRContext OpInfo) : Prop :=
  IRNode.Ancestor (.operation ancestor) descendant ctx

abbrev BlockPtr.Ancestor (ancestor : BlockPtr) (descendant : IRNode) (ctx : WfIRContext OpInfo) : Prop :=
  IRNode.Ancestor (.block ancestor) descendant ctx

abbrev RegionPtr.Ancestor (ancestor : RegionPtr) (descendant : IRNode) (ctx : WfIRContext OpInfo) : Prop :=
  IRNode.Ancestor (.region ancestor) descendant ctx

@[simp, grind]
abbrev OperationPtr.RootedAt (op : OperationPtr) (root : IRNode) (ctx : WfIRContext OpInfo) : Prop :=
  IRNode.RootedAt (.operation op) root ctx

@[simp, grind]
abbrev BlockPtr.RootedAt (block : BlockPtr) (root : IRNode) (ctx : WfIRContext OpInfo) : Prop :=
  IRNode.RootedAt (.block block) root ctx

@[simp, grind]
abbrev RegionPtr.RootedAt (region : RegionPtr) (root : IRNode) (ctx : WfIRContext OpInfo) : Prop :=
  IRNode.RootedAt (.region region) root ctx


/-! ## Executable nesting queries -/

/--
Whether `ancestor` is `descendant` or one of its enclosing regions. This is the
executable counterpart of MLIR's `Region::isAncestor` query.
-/
partial def RegionPtr.isAncestorOf
    (ancestor descendant : RegionPtr) (ctx : WfIRContext OpInfo) : Bool :=
  ancestor = descendant ||
    match (descendant.getParent! ctx.raw).bind (·.getParentRegion! ctx.raw) with
    | none => false
    | some parentRegion => ancestor.isAncestorOf parentRegion ctx

end Veir
