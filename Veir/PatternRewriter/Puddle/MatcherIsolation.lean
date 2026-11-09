module
public import Veir.PatternRewriter.Puddle.MatcherRegionScope
public import Veir.Interfaces.RegionIsolationInterfaces
public import Veir.Verifier
import all Veir.Interfaces.RegionIsolationInterfaces
import all Veir.IRNesting
import all Veir.Verifier
import all Veir.Interpreter.CTreeEntryInvariant
import all Veir.IR.Basic
import all Veir.Dominance.Basic
import all Veir.Dialects.Arith.OpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Dialects.Func.OpInfo
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.RISCV_Stack.OpInfo
import all Veir.Dialects.RV64.OpInfo
import all Veir.Dialects.ModArith.OpInfo
import all Veir.Dialects.Datapath.OpInfo
import all Veir.Dialects.Comb.OpInfo
import all Veir.Dialects.HW.OpInfo
import all Veir.Dialects.Verif.OpInfo
import all Veir.Dialects.PDL.OpInfo
import all Veir.Dialects.IO.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Dialects.Test.OpInfo
import all Veir.Dialects.LLZK.Felt.OpInfo
import all Veir.Dialects.LLZK.Include.OpInfo
import all Veir.Dialects.LLZK.Function.OpInfo
import all Veir.Dialects.Cir.OpInfo
import all Veir.Dialects.Seq.OpInfo
import all Veir.Dialects.Tensor.OpInfo
import all Veir.Dialects.SMT.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Interfaces.RegionKindInterfaces
import all Veir.Interfaces.FunctionInterfaces
namespace Veir
public section

private theorem parentPath_parent_shorter {ctx : WfIRContext OpCode}
    {child parent root : IRNode} {nodes : List IRNode}
    (path : IRNode.ParentPath ctx child root nodes) (rootNone : root.parent! ctx = none)
    (hp : child.parent! ctx = some parent) :
    ∃ upper, IRNode.ParentPath ctx parent root upper ∧ upper.length < nodes.length := by
  cases path with
  | single => simp_all
  | cons immediate tail =>
      have heq := Option.some.inj (immediate.symm.trans hp)
      subst parent
      exact ⟨_, tail, by simp⟩

/-- A successful finite nesting query on a rooted region witnesses actual ancestry. -/
theorem RegionPtr.ancestor_of_isAncestorOf {ctx : WfIRContext OpCode}
    {ancestor descendant : RegionPtr} {root : IRNode}
    (rooted : descendant.RootedAt root ctx)
    (query : ancestor.isAncestorOf descendant ctx = true) : ancestor.Ancestor descendant ctx := by
  obtain ⟨nodes, path⟩ := rooted.1.exists_parentPath
  have general : ∀ n (descendant : RegionPtr) (nodes : List IRNode), nodes.length = n →
      IRNode.ParentPath ctx descendant root nodes →
      ancestor.isAncestorOf descendant ctx = true → ancestor.Ancestor descendant ctx := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro descendant nodes size path query
      rw [RegionPtr.isAncestorOf.eq_1] at query
      split at query
      · rename_i same
        subst descendant
        exact .refl
      · split at query
        · contradiction
        · rename_i parentRegion hparent
          simp only [Option.bind_eq_some_iff] at hparent
          obtain ⟨parentOp, hparentOp, hparentRegion⟩ := hparent
          obtain ⟨block, hopBlock, hblockRegion⟩ :=
            OperationPtr.getParentRegion!_eq_some_iff.mp hparentRegion
          obtain ⟨upper₁, path₁, length₁⟩ := parentPath_parent_shorter (parent := .operation parentOp) path rooted.2 (by simp [IRNode.parent!, hparentOp])
          obtain ⟨upper₂, path₂, length₂⟩ := parentPath_parent_shorter (parent := .block block) path₁ rooted.2 (by simp [IRNode.parent!, hopBlock])
          obtain ⟨upper₃, path₃, length₃⟩ := parentPath_parent_shorter (parent := .region parentRegion) path₂ rooted.2 (by simp [IRNode.parent!, hblockRegion])
          have ha := ih upper₃.length (by omega) parentRegion upper₃ rfl path₃ query
          exact IRNode.Ancestor.trans ha
            (IRNode.Ancestor.trans_ancestor_parent
              (show (IRNode.region descendant).parent! ctx = some (.operation parentOp) by
                simp [IRNode.parent!, hparentOp])
              (IRNode.Ancestor.of_getParentRegion!_eq_some hparentRegion))
  exact general nodes.length descendant nodes rfl path query

/-- An immediate isolated owner establishes exactly this region's isolation scope. -/
theorem RegionPtr.nearestIsolatedScope?_eq_self {ctx : IRContext OpCode}
    {region : RegionPtr} {owner : OperationPtr}
    (parent : region.getParent! ctx = some owner)
    (isolated : HasOpInfo.isIsolatedFromAbove (owner.getOpType! ctx) = true) :
    region.nearestIsolatedScope? ctx = some region := by
  rw [RegionPtr.nearestIsolatedScope?.eq_1]
  simp [parent, isolated]

/-- Full context verification includes the operand-isolation check for every operation. -/
private theorem OperationPtr.verifyOperandIsolation_of_contextVerified
    {ctx : WfIRContext OpCode} {op root : OperationPtr}
    (verified : ctx.Verified root) (inBounds : op.InBounds ctx.raw) :
    op.verifyOperandIsolation ctx inBounds = .ok () := by
  simp only [WfIRContext.Verified, WfIRContext.verify] at verified
  split at verified
  · cases verified
  split at verified
  · cases verified
  obtain ⟨_, hOps, -⟩ := Except.bind_eq_ok.mp verified
  have hop := IRContext.forOpsDepM_except_ok hOps op inBounds
  obtain ⟨_, _, hrest⟩ := Except.bind_eq_ok.mp (Except.eq_ok_of_mapError_eq_ok hop)
  split at hrest
  · obtain ⟨_, _, hrest⟩ := Except.bind_eq_ok.mp hrest
    obtain ⟨_, hisolation, _⟩ := Except.bind_eq_ok.mp hrest
    exact hisolation
  · obtain ⟨_, hisolation, _⟩ := Except.bind_eq_ok.mp hrest
    exact hisolation

private theorem list_forIn_checks {α : Type} (items : List α) (check : α → Except String PUnit)
    (success : forIn items PUnit.unit (fun x _ => do check x; pure (.yield PUnit.unit)) = .ok PUnit.unit) :
    ∀ item ∈ items, check item = .ok PUnit.unit := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.forIn_cons] at success
      cases hhead : check head with
      | error message => simp [hhead, Bind.bind, Except.bind] at success
      | ok value =>
          cases value
          simp only [hhead, Bind.bind, Pure.pure, Except.bind, Except.pure] at success
          intro item member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact hhead
          · exact ih success item member

private theorem array_forIn_checks {α : Type} (items : Array α) (check : α → Except String PUnit)
    (success : forIn items PUnit.unit (fun x _ => do check x; pure (.yield PUnit.unit)) = .ok PUnit.unit) :
    ∀ item ∈ items, check item = .ok PUnit.unit := by
  intro item member
  exact list_forIn_checks items.toList check (by simpa only [Array.forIn_toList] using success)
    item (by simpa using member)

/-- Verified uses in an isolated direct region cannot refer to a definition outside that region's subtree. -/
theorem OperationPtr.operand_region_ancestor_of_contextVerified
    {ctx : WfIRContext OpCode} {op root : OperationPtr} {region : RegionPtr}
    {value : ValuePtr} (verified : ctx.Verified root) (inBounds : op.InBounds ctx.raw)
    (parent : op.getParentRegion! ctx.raw = some region)
    (scope : region.nearestIsolatedScope? ctx.raw = some region)
    (member : value ∈ op.getOperands! ctx.raw) :
    ∃ definitionRegion, value.getParentRegion! ctx.raw = some definitionRegion ∧
      region.isAncestorOf definitionRegion ctx = true := by
  have checked := op.verifyOperandIsolation_of_contextVerified verified inBounds
  by_cases empty : op.getNumOperands ctx.raw inBounds = 0
  · have hsize : (op.getOperands! ctx.raw).size = 0 := by grind
    have : False := by simp [Array.size_eq_zero_iff.mp hsize] at member
    contradiction
  unfold OperationPtr.verifyOperandIsolation at checked
  simp [empty, parent, scope] at checked
  split at checked
  · rename_i hempty
    have hsame : value.getParentRegion! ctx.raw = some region := by
      grind
    exact ⟨region, hsame, by rw [RegionPtr.isAncestorOf.eq_1]; simp⟩
  · let check : ValuePtr → Except String PUnit := fun pointer =>
      match pointer.getParentRegion! ctx.raw with
      | none => .error "operand is unlinked from any region"
      | some definitionRegion =>
        if region.isAncestorOf definitionRegion ctx = false then
          .error "operand uses a value defined outside the isolated region that encloses its use"
        else .ok PUnit.unit
    let escaping := (op.getOperands ctx.raw inBounds).filter
      (fun pointer => pointer.getParentRegion! ctx.raw != some region)
    have checkAll := array_forIn_checks escaping check (by
      apply Eq.trans ?_ checked
      congr 1
      funext pointer loopState
      cases hp : pointer.getParentRegion! ctx.raw with
      | none => simp only [check, hp]; rfl
      | some definitionRegion =>
        simp only [check, hp]
        split <;> rfl)
    by_cases hsame : value.getParentRegion! ctx.raw = some region
    · exact ⟨region, hsame, by rw [RegionPtr.isAncestorOf.eq_1]; simp⟩
    · have hitem := checkAll value (by simpa [escaping, OperationPtr.getOperands!_eq_getOperands inBounds] using And.intro member hsame)
      dsimp only [check] at hitem
      split at hitem
      · contradiction
      · rename_i definitionRegion hp
        split at hitem
        · contradiction
        · rename_i htrue
          exact ⟨definitionRegion, hp, by simpa using htrue⟩

/-- A dominating value's defining region encloses the use's direct region. -/
theorem ValuePtr.parentRegion_ancestor_of_properlyDominates
    {ctx : WfIRContext OpCode} {value : ValuePtr} {op : OperationPtr}
    {definitionRegion useRegion : RegionPtr}
    (dominates : value.ProperlyDominates op ctx)
    (definition : value.getParentRegion! ctx.raw = some definitionRegion)
    (use : op.getParentRegion! ctx.raw = some useRegion) :
    definitionRegion.Ancestor useRegion ctx := by
  cases value with
  | opResult result =>
      have parent : result.op.getParentRegion! ctx.raw = some definitionRegion := definition
      have ancestor := OperationPtr.Dominates.parentRegion_ancestor (Or.inr dominates) parent
      obtain ⟨block, opParent, blockParent⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp use
      have ancestorBlock := (ancestor.toProperAncestor (by simp)).ancestor_of_parent_descendant
        (show (IRNode.operation op).parent! ctx = some (.block block) by simp [IRNode.parent!, opParent])
      exact (ancestorBlock.toProperAncestor (by simp)).ancestor_of_parent_descendant
        (show (IRNode.block block).parent! ctx = some (.region useRegion) by simp [IRNode.parent!, blockParent])
  | blockArgument argument =>
      obtain ⟨block, opParent, blockParent⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp use
      obtain ⟨otherBlock, otherParent, blockDom⟩ := dominates
      have same : otherBlock = block := by grind
      subst otherBlock
      have argParent : argument.block.getParent! ctx.raw = some definitionRegion := definition
      have ancestor : definitionRegion.Ancestor block ctx := blockDom.ancestor_parent
        ⟨.of_parent (by simp [IRNode.parent!, argParent]), by simp⟩
      exact (ancestor.toProperAncestor (by simp)).ancestor_of_parent_descendant
        (show (IRNode.block block).parent! ctx = some (.region useRegion) by simp [IRNode.parent!, blockParent])

/-- Verification and SSA dominance force every operand of a reachable use in an isolated
region to be defined directly in that region. -/
theorem OperationPtr.operands_definedInRegion_of_contextVerified
    {ctx : WfIRContext OpCode} {op verifyRoot : OperationPtr} {region : RegionPtr} {irRoot : IRNode}
    (verified : ctx.Verified verifyRoot) (inBounds : op.InBounds ctx.raw)
    (dom : ctx.Dom irRoot) (rooted : op.RootedAt irRoot ctx)
    (reachable : op.LocallyReachable region ctx)
    (parent : op.getParentRegion! ctx.raw = some region)
    (scope : region.nearestIsolatedScope? ctx.raw = some region) :
    ∀ value ∈ op.getOperands! ctx.raw, value.DefinedInRegion region ctx := by
  intro value member
  have dominance := dom.operand_properlyDominates rooted.1 reachable member
  obtain ⟨definitionRegion, definition, query⟩ :=
    op.operand_region_ancestor_of_contextVerified verified inBounds parent scope member
  have outside := ValuePtr.parentRegion_ancestor_of_properlyDominates dominance definition parent
  have regionRooted : region.RootedAt irRoot ctx :=
    rooted.of_ancestor (IRNode.Ancestor.of_getParentRegion!_eq_some parent)
  have definitionRooted := regionRooted.of_ancestor outside
  have inside := RegionPtr.ancestor_of_isAncestorOf definitionRooted query
  have same : definitionRegion = region := by
    have eq := outside.antisymm_of_rooted inside regionRooted
    simpa using eq
  subst definitionRegion
  cases value <;> exact definition

/-- Every registered function interface establishes an isolated SSA body. -/
theorem FunctionOp.isolated_ssa_metadata {ctx : IRContext OpCode} {op : OperationPtr}
    (function : FunctionOp ctx op) (index : Nat) :
    HasOpInfo.isIsolatedFromAbove (op.getOpType! ctx) = true ∧
      HasOpInfo.hasSSADominance (op.getOpType! ctx) index = true := by
  have existsInterface : (HasOpInfo.functionInterface? (op.getOpType! ctx)).isSome = true := by
    rw [function.functionInterface?_eq]
    rfl
  generalize codeEq : op.getOpType! ctx = code at existsInterface ⊢
  cases code <;> rename_i dialectCode <;> cases dialectCode
  all_goals first
    | exact ⟨rfl, rfl⟩
    | change false = true at existsInterface; contradiction

/-- Regions owned by a registered function are isolated SSA regions. -/
theorem FunctionOp.owned_region_scope {ctx : WfIRContext OpCode} {op : OperationPtr}
    (function : FunctionOp ctx.raw op) {region : RegionPtr}
    (parent : region.getParent! ctx.raw = some op) :
    region.nearestIsolatedScope? ctx.raw = some region ∧ region.hasSSADominance ctx = true := by
  have isolated := (function.isolated_ssa_metadata 0).1
  have ssa : ∀ index, HasOpInfo.hasSSADominance (op.getOpType! ctx.raw) index = true :=
    fun index => (function.isolated_ssa_metadata index).2
  refine ⟨RegionPtr.nearestIsolatedScope?_eq_self parent isolated, ?_⟩
  cases first : region.getFirstBlock! ctx.raw <;> simp [RegionPtr.hasSSADominance, first, parent, ssa]

/-- The body returned by the function interface has the function as its owner. -/
theorem FunctionOp.getFunctionBody!_parent {ctx : WfIRContext OpCode} {op : OperationPtr}
    (function : FunctionOp ctx.raw op) (opIn : op.InBounds ctx.raw)
    (hasRegion : 0 < op.getNumRegions! ctx.raw) :
    function.getFunctionBody!.getParent! ctx.raw = some op := by
  have regionIn := function.getFunctionBody!_inBounds ctx.wellFormed.inBounds opIn hasRegion
  apply ((ctx.wellFormed.operations op opIn).region_parent function.getFunctionBody! regionIn).mp
  exact ⟨0, hasRegion, rfl⟩

/-- The concrete function body supplies both entry-invariant metadata conditions. -/
theorem FunctionOp.body_scope {ctx : WfIRContext OpCode} {op : OperationPtr}
    (function : FunctionOp ctx.raw op) (opIn : op.InBounds ctx.raw)
    (hasRegion : 0 < op.getNumRegions! ctx.raw) :
    function.getFunctionBody!.nearestIsolatedScope? ctx.raw = some function.getFunctionBody! ∧
      function.getFunctionBody!.hasSSADominance ctx = true :=
  function.owned_region_scope (function.getFunctionBody!_parent opIn hasRegion)

namespace Puddle
/-- Actual matching in a verified isolated region binds only definitions in that direct region.
Only reachable matched operations use dominance; unreachable blocks impose no closure premise. -/
theorem CTree.Pattern.Valid.regionScope_of_run_verified {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx : WfIRContext OpCode}
    {root verifyRoot : OperationPtr} {irRoot : IRNode} {region : RegionPtr} {assignment : Assignment OpCode}
    (verified : ctx.Verified verifyRoot) (dom : ctx.Dom irRoot)
    (rootRooted : root.RootedAt irRoot ctx) (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (scope : region.nearestIsolatedScope? ctx.raw = some region)
    (hmatch : rule.matcher.run ctx.raw root = some assignment) : assignment.RegionScope ctx region := by
  obtain ⟨rootResults, _, matcherScope⟩ := valid.matcherScope_of_run
    dom rootRooted rootRegion rootReachable rootIn hmatch
  have regionRooted : region.RootedAt irRoot ctx :=
    rootRooted.of_ancestor (IRNode.Ancestor.of_getParentRegion!_eq_some rootRegion)
  apply rule.matcher.regionScope_of_run_reachable (region := region) ?_ ?_ rootRegion rootIn hmatch
  · intro op opIn opRegion opReachable
    have opRooted : op.RootedAt irRoot ctx :=
      ⟨regionRooted.1.trans (IRNode.Ancestor.of_getParentRegion!_eq_some opRegion), regionRooted.2⟩
    obtain ⟨localRegion, localReachable⟩ := opReachable.exists_locallyReachable opRegion
    have same : localRegion = region := by grind
    subst localRegion
    exact op.operands_definedInRegion_of_contextVerified verified opIn dom opRooted
      localReachable opRegion scope
  · intro handle op hbound
    rcases matcherScope.getOp hbound with ⟨rfl, _⟩ | dominates
    · exact rootReachable
    · grind
end Puddle

end
end Veir
