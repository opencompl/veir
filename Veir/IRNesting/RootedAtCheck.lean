module

public import Veir.IRNesting
import all Veir.IRNesting
import all Veir.IR.Basic

public section
namespace Veir

variable {OpInfo : Type} [IsOpCode OpInfo]

/-- Follow at most `fuel` nesting edges. The equality test precedes the fuel
check, so a node is its own ancestor even with no remaining edges. -/
def IRNode.hasAncestorWithin? (node ancestor : IRNode) (ctx : WfIRContext OpInfo) : Nat → Bool
  | 0 => node == ancestor
  | fuel + 1 =>
    if node == ancestor then true
    else match node.parent! ctx with
      | none => false
      | some parent => parent.hasAncestorWithin? ancestor ctx fuel

/-- Successful bounded parent traversal supplies an actual finite ancestry path. -/
theorem IRNode.hasAncestorWithin?_sound {node ancestor : IRNode} {ctx : WfIRContext OpInfo}
    {fuel : Nat} (checked : node.hasAncestorWithin? ancestor ctx fuel = true) :
    ancestor.Ancestor node ctx := by
  induction fuel generalizing node with
  | zero =>
    simp only [IRNode.hasAncestorWithin?, beq_iff_eq] at checked
    subst node
    exact .refl
  | succ fuel ih =>
    simp only [IRNode.hasAncestorWithin?] at checked
    split at checked
    · rename_i equal
      have equal : node = ancestor := by simpa using equal
      subst node
      exact .refl
    · split at checked
      · contradiction
      · rename_i parent parentEq
        exact (ih checked).trans_ancestor_parent parentEq

/-- Any explicit ancestry path is accepted once its edge count fits the budget. -/
theorem IRNode.hasAncestorWithin?_complete_of_path
    {node ancestor : IRNode} {ctx : WfIRContext OpInfo} {nodes : List IRNode}
    (path : IRNode.ParentPath ctx node ancestor nodes) {fuel : Nat}
    (enough : nodes.length ≤ fuel + 1) : node.hasAncestorWithin? ancestor ctx fuel = true := by
  induction path generalizing fuel with
  | single => cases fuel <;> simp [IRNode.hasAncestorWithin?]
  | @cons ancestor child parent nodes immediate tail ih =>
    cases fuel with
    | zero => have := tail.ne_nil; simp at enough; cases nodes <;> simp_all
    | succ fuel =>
      simp only [IRNode.hasAncestorWithin?]
      split
      · rfl
      · rw [immediate]
        exact ih (by simpa using enough)

private theorem path_member_ancestor {node ancestor member : IRNode} {ctx : WfIRContext OpInfo}
    {nodes : List IRNode} (path : IRNode.ParentPath ctx node ancestor nodes)
    (mem : member ∈ nodes) : member.Ancestor node ctx := by
  induction path with
  | single => simp only [List.mem_singleton] at mem; subst member; exact .refl
  | cons immediate tail ih =>
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact .refl
    · exact (ih mem).trans_ancestor_parent immediate

private theorem rooted_path_nodup {node root : IRNode} {ctx : WfIRContext OpInfo}
    {nodes : List IRNode} (path : IRNode.ParentPath ctx node root nodes)
    (detached : root.parent! ctx = none) : nodes.Nodup := by
  induction path with
  | single => simp
  | @cons root child parent nodes immediate tail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih detached⟩
    intro member
    have reverse := path_member_ancestor tail member
    have forward : parent.Ancestor child ctx := .of_parent immediate
    have rooted : child.RootedAt root ctx := ⟨.of_parentPath (.cons immediate tail), detached⟩
    have equal := forward.antisymm_of_rooted reverse rooted
    exact IRNode.child_ne_parent immediate equal.symm

private theorem parent_inBounds {node parent : IRNode} {ctx : WfIRContext OpInfo}
    (inside : node.InBounds ctx.raw) (immediate : node.parent! ctx = some parent) :
    parent.InBounds ctx.raw := by
  cases node <;> cases parent <;> simp only [IRNode.parent!, Option.map_eq_some_iff] at immediate <;>
    grind

private theorem path_member_inBounds {node ancestor member : IRNode} {ctx : WfIRContext OpInfo}
    {nodes : List IRNode} (path : IRNode.ParentPath ctx node ancestor nodes)
    (inside : node.InBounds ctx.raw) (mem : member ∈ nodes) : member.InBounds ctx.raw := by
  induction path with
  | single => simp only [List.mem_singleton] at mem; subst member; exact inside
  | cons immediate tail ih =>
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact inside
    · exact ih (parent_inBounds inside immediate) mem

private def contextNodes (ctx : WfIRContext OpInfo) : List IRNode :=
  ctx.raw.operations.keys.map IRNode.operation ++ ctx.raw.blocks.keys.map IRNode.block ++
    ctx.raw.regions.keys.map IRNode.region

private theorem mem_contextNodes {node : IRNode} {ctx : WfIRContext OpInfo}
    (inside : node.InBounds ctx.raw) : node ∈ contextNodes ctx := by
  cases node <;> simp_all [contextNodes, IRNode.InBounds, OperationPtr.InBounds,
    BlockPtr.InBounds, RegionPtr.InBounds, Std.HashMap.mem_keys]

private theorem rooted_path_length_le {node root : IRNode} {ctx : WfIRContext OpInfo}
    {nodes : List IRNode} (path : IRNode.ParentPath ctx node root nodes)
    (inside : node.InBounds ctx.raw) (detached : root.parent! ctx = none) :
    nodes.length ≤ ctx.raw.operations.size + ctx.raw.blocks.size + ctx.raw.regions.size := by
  have subset : nodes ⊆ contextNodes ctx := fun member mem =>
    mem_contextNodes (path_member_inBounds path inside mem)
  have bound := (rooted_path_nodup path detached).length_le_of_subset subset
  simpa [contextNodes, Std.HashMap.length_keys, Nat.add_assoc] using bound

/-- A bounded, executable certificate that a node belongs to the tree rooted at
`root`. A detached root is required even when `node = root`. -/
def IRNode.rootedAtWithin? (node root : IRNode) (ctx : WfIRContext OpInfo) (fuel : Nat) : Bool :=
  (root.parent! ctx).isNone && node.hasAncestorWithin? root ctx fuel

theorem IRNode.rootedAtWithin?_sound {node root : IRNode} {ctx : WfIRContext OpInfo}
    {fuel : Nat} (checked : node.rootedAtWithin? root ctx fuel = true) :
    node.RootedAt root ctx := by
  simp only [IRNode.rootedAtWithin?, Bool.and_eq_true] at checked
  obtain ⟨detached, ancestry⟩ := checked
  exact ⟨IRNode.hasAncestorWithin?_sound ancestry, by simpa using detached⟩

/-- Bound traversal by the number of allocated IR nodes; malformed parent cycles
cannot make this check diverge. -/
def OperationPtr.rootedAt? (op root : OperationPtr) (ctx : WfIRContext OpInfo) : Bool :=
  (IRNode.operation op).rootedAtWithin? (.operation root) ctx
    (ctx.raw.operations.size + ctx.raw.blocks.size + ctx.raw.regions.size)

theorem OperationPtr.rootedAt?_sound {op root : OperationPtr} {ctx : WfIRContext OpInfo}
    (checked : op.rootedAt? root ctx = true) : op.RootedAt root ctx :=
  IRNode.rootedAtWithin?_sound checked

/-- The default budget accepts every genuinely rooted, allocated operation. -/
theorem OperationPtr.rootedAt?_complete {op root : OperationPtr} {ctx : WfIRContext OpInfo}
    (inside : op.InBounds ctx.raw) (rooted : op.RootedAt root ctx) :
    op.rootedAt? root ctx = true := by
  obtain ⟨nodes, path⟩ := rooted.1
  have length := rooted_path_length_le path inside rooted.2
  have accepted := IRNode.hasAncestorWithin?_complete_of_path path (by omega :
    nodes.length ≤ ctx.raw.operations.size + ctx.raw.blocks.size + ctx.raw.regions.size + 1)
  simp only [OperationPtr.rootedAt?, IRNode.rootedAtWithin?, rooted.2, Option.isNone_none,
    Bool.true_and]
  exact accepted

theorem OperationPtr.rootedAt?_iff {op root : OperationPtr} {ctx : WfIRContext OpInfo}
    (inside : op.InBounds ctx.raw) : op.rootedAt? root ctx = true ↔ op.RootedAt root ctx :=
  ⟨OperationPtr.rootedAt?_sound, OperationPtr.rootedAt?_complete inside⟩

end Veir
