module

public import Veir.Verifier
import all Init.Internal.Order.Basic
import all Veir.Verifier
import all Veir.Verifier.Basic
import all Veir.GlobalOpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.IR.Basic
import all Veir.IRNesting

public section
namespace Veir

variable {OpInfo : Type} [IsOpCode OpInfo]

/-- A positive ancestry check witnesses a finite parent path. -/
theorem IRNode.isAncestorOf_sound {ancestor : IRNode} {ctx : WfIRContext OpInfo} :
    ∀ {node : IRNode}, ancestor.isAncestorOf node ctx = true → ancestor.Ancestor node ctx := by
  apply IRNode.isAncestorOf.fixpoint_induct ancestor ctx
    (fun walk => ∀ {node : IRNode}, walk node = true → ancestor.Ancestor node ctx)
  · apply Lean.Order.admissible_pi_apply (β := fun _ : IRNode => Lean.Order.FlatOrder false)
      (fun node result => result = true → ancestor.Ancestor node ctx)
    intro node
    exact Lean.Order.admissible_flatOrder _ (by change false = true → _; simp)
  · intro walk ih node checked
    dsimp only at checked
    split at checked
    · rename_i equal
      subst node
      exact .refl
    · split at checked
      · contradiction
      · rename_i parent edge
        exact (ih checked).trans_ancestor_parent edge

/-- The ancestry walk recognizes every finite parent path. -/
theorem IRNode.isAncestorOf_complete_of_path
    {node ancestor : IRNode} {ctx : WfIRContext OpInfo} {nodes : List IRNode}
    (path : IRNode.ParentPath ctx node ancestor nodes) : ancestor.isAncestorOf node ctx = true := by
  induction path with
  | single => rw [IRNode.isAncestorOf.eq_1, ite_eq_left rfl]
  | cons edge tail ih =>
    rw [IRNode.isAncestorOf.eq_1]
    split
    · rfl
    · simpa only [edge] using ih

private def OperationPtr.regionsUnder (root : OperationPtr) (ctx : WfIRContext OpInfo) : Std.HashSet RegionPtr :=
  .ofList (ctx.raw.regions.keys.filter fun region => (IRNode.operation root).isAncestorOf (.region region) ctx)

private theorem OperationPtr.mem_regionsUnder_iff {root : OperationPtr} {ctx : WfIRContext OpInfo}
    {region : RegionPtr} (detached : root.getParent! ctx.raw = none) :
    region ∈ root.regionsUnder ctx ↔
      region.InBounds ctx.raw ∧ region.RootedAt root ctx := by
  simp only [regionsUnder, Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_filter, Std.HashMap.mem_keys]
  have noParent : (IRNode.operation root).parent! ctx = none := by simp [IRNode.parent!, detached]
  constructor
  · rintro ⟨inside, checked⟩
    exact ⟨inside, IRNode.isAncestorOf_sound checked, noParent⟩
  · rintro ⟨inside, ⟨nodes, path⟩, _⟩
    exact ⟨inside, IRNode.isAncestorOf_complete_of_path path⟩

private theorem OperationPtr.parentRegion_mem_iff {root op : OperationPtr} {ctx : WfIRContext OpInfo}
    (opIn : op.InBounds ctx.raw) (detached : root.getParent! ctx.raw = none) (distinct : op ≠ root) :
    (op.getParentRegion! ctx.raw).any (root.regionsUnder ctx).contains ↔ op.RootedAt root ctx := by
  constructor
  · intro found
    cases parent : op.getParentRegion! ctx.raw with
    | none => simp [parent] at found
    | some r =>
      have mem : r ∈ root.regionsUnder ctx := by simpa [parent] using found
      exact (IRNode.Ancestor.of_getParentRegion!_eq_some parent).rootedAt_iff.mp
        ((mem_regionsUnder_iff detached).mp mem).2
  intro rooted
  have ⟨nodes, path⟩ := rooted.1
  cases path with
  | single => contradiction
  | cons immediate tail =>
    simp only [IRNode.parent!_operation, Option.map_eq_some_iff] at immediate
    obtain ⟨block, opParent, rfl⟩ := immediate
    cases tail with
    | cons immediate tail =>
      simp only [IRNode.parent!_block, Option.map_eq_some_iff] at immediate
      obtain ⟨region, blockParent, rfl⟩ := immediate
      have member := (OperationPtr.mem_regionsUnder_iff (region := region) detached).mpr
        ⟨by grind, ⟨_, tail⟩, rooted.2⟩
      simp [OperationPtr.getParentRegion!_eq_some_of_parent_of_parent opParent blockParent,
        member]

/-- A value belongs to the tree containing its defining operation or block. -/
def ValuePtr.definitionNode : ValuePtr → IRNode
  | .opResult result => .operation result.op
  | .blockArgument argument => .block argument.block

private theorem ValuePtr.parentRegion_mem_iff {ctx : WfIRContext OpInfo} {value : ValuePtr} {root : OperationPtr}
    (inside : value.InBounds ctx.raw) (detached : root.getParent! ctx.raw = none)
    (distinct : value.definitionNode ≠ .operation root) :
    (value.getParentRegion! ctx.raw).any (root.regionsUnder ctx).contains ↔ value.definitionNode.RootedAt root ctx := by
  cases value with
  | opResult r =>
    exact OperationPtr.parentRegion_mem_iff (by grind [ValuePtr.InBounds, OpResultPtr.InBounds]) detached
      (fun eq => distinct (congrArg IRNode.operation eq))
  | blockArgument a =>
    change (a.block.getParent! ctx.raw).any _ = true ↔ a.block.RootedAt root ctx
    constructor
    · intro checked
      cases parent : a.block.getParent! ctx.raw with
      | none => simp [parent] at checked
      | some r =>
        have mem : r ∈ root.regionsUnder ctx := by simpa [parent] using checked
        exact IRNode.RootedAt.of_parent ((OperationPtr.mem_regionsUnder_iff detached).mp mem).2
          (by simp [parent])
    · rintro ⟨⟨_, path⟩, noParent⟩
      cases path with
      | cons edge tail =>
        simp only [IRNode.parent!_block, Option.map_eq_some_iff] at edge
        obtain ⟨r, parent, rfl⟩ := edge
        have mem := (OperationPtr.mem_regionsUnder_iff (region := r) detached).mpr
          ⟨by grind [ValuePtr.InBounds, BlockArgumentPtr.InBounds], ⟨_, tail⟩, noParent⟩
        simp [parent, mem]

private theorem OperationPtr.Verified.module_counts {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn}
    (verified : op.Verified ctx opIn) (code : op.getOpType! ctx.raw = .builtin .module) :
    op.getNumOperands! ctx.raw = 0 ∧ op.getNumResults! ctx.raw = 0 := by
  simp only [Verified, verifyLocalInvariants, HasOpInfo.verifyLocalInvariants,
    OpCode.verifyLocalInvariants, Builtin.verifyLocalInvariants, verifyOpCounts, verifyNonOperandCounts,
    ← getOpType!_eq_getOpType, code, ne_eq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    pure, Except.pure, ite_not] at verified
  grind

/-- Neither following an operand nor following a use can leave a verified top-level module. -/
theorem WfIRContext.Verified.operand_rootedAt_iff {ctx : WfIRContext OpCode}
    {root op : OperationPtr} {value : ValuePtr} (verified : ctx.Verified root)
    (moduleCode : root.getOpType! ctx.raw = .builtin .module) (detached : root.getParent! ctx.raw = none)
    (opIn : op.InBounds ctx.raw) (operand : value ∈ op.getOperands! ctx.raw) :
    value.definitionNode.RootedAt root ctx ↔ op.RootedAt root ctx := by
  have useCheck : op.verifyModuleOperands ctx (some (root.regionsUnder ctx)) = .ok () := by
    simp only [Verified, verify, moduleCode, ↓reduceIte] at verified
    split at verified <;> try contradiction
    split at verified <;> try contradiction
    obtain ⟨_, ops, _⟩ := Except.bind_eq_ok.mp verified
    have checked := Except.eq_ok_of_mapError_eq_ok (IRContext.forOpsDepM_except_ok ops op opIn)
    obtain ⟨_, _, checked⟩ := Except.bind_eq_ok.mp checked
    split at checked <;> repeat obtain ⟨_, _, checked⟩ := Except.bind_eq_ok.mp checked
    all_goals
      split at checked
      · obtain ⟨_, _, checked⟩ := Except.bind_eq_ok.mp checked
        exact checked
      · exact checked
  simp only [OperationPtr.verifyModuleOperands] at useCheck
  split at useCheck <;> try contradiction
  rename_i allOperands
  have counts (rootIn : root.InBounds ctx.raw) :=
    (OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants verified rootIn).module_counts moduleCode
  have valueIn : value.InBounds ctx.raw := by grind
  have useNe : op ≠ root := by
    rintro rfl
    have zero := (counts opIn).1
    obtain ⟨i, hi, _⟩ := Array.getElem_of_mem operand
    grind
  have defNe : value.definitionNode ≠ .operation root := by
    cases value with
    | blockArgument => simp [ValuePtr.definitionNode]
    | opResult r =>
      intro eq
      obtain rfl : r.op = root := IRNode.operation.inj eq
      have resultIn : r.InBounds ctx.raw := by simpa using valueIn
      have zero := (counts (by grind [OpResultPtr.InBounds])).2
      grind
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem operand
  have equal := of_decide_eq_true ((Array.all_eq_true.mp allOperands) i hi)
  rw [← ValuePtr.parentRegion_mem_iff valueIn detached defNe, ← OperationPtr.parentRegion_mem_iff opIn detached useNe,
    equal]

/-- Check that `root` is a detached ancestor of `node`. -/
def IRNode.rootedAtWithin? (node root : IRNode) (ctx : WfIRContext OpInfo) : Bool :=
  (root.parent! ctx).isNone && root.isAncestorOf node ctx

theorem IRNode.rootedAtWithin?_sound {node root : IRNode} {ctx : WfIRContext OpInfo}
    (checked : node.rootedAtWithin? root ctx = true) : node.RootedAt root ctx := by
  simp only [IRNode.rootedAtWithin?, Bool.and_eq_true] at checked
  obtain ⟨detached, ancestry⟩ := checked
  exact ⟨IRNode.isAncestorOf_sound ancestry, by simpa using detached⟩

/-- Check whether an operation belongs to a detached root. -/
def OperationPtr.rootedAt? (op root : OperationPtr) (ctx : WfIRContext OpInfo) : Bool :=
  (IRNode.operation op).rootedAtWithin? root ctx

theorem OperationPtr.rootedAt?_sound {op root : OperationPtr} {ctx : WfIRContext OpInfo}
    (checked : op.rootedAt? root ctx = true) : op.RootedAt root ctx :=
  IRNode.rootedAtWithin?_sound checked

theorem OperationPtr.rootedAt?_complete {op root : OperationPtr} {ctx : WfIRContext OpInfo}
    (_inside : op.InBounds ctx.raw) (rooted : op.RootedAt root ctx) : op.rootedAt? root ctx = true := by
  obtain ⟨nodes, path⟩ := rooted.1
  simp only [OperationPtr.rootedAt?, IRNode.rootedAtWithin?, rooted.2, Option.isNone_none, Bool.true_and]
  exact IRNode.isAncestorOf_complete_of_path path

theorem OperationPtr.rootedAt?_iff {op root : OperationPtr} {ctx : WfIRContext OpInfo}
    (inside : op.InBounds ctx.raw) : op.rootedAt? root ctx = true ↔ op.RootedAt root ctx :=
  ⟨OperationPtr.rootedAt?_sound, OperationPtr.rootedAt?_complete inside⟩

end Veir
