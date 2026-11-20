module
public import Veir.PatternRewriter.Puddle.MatcherIsolation
public import Veir.Interpreter.Refinement.Basic
import all Veir.IRNesting
import all Veir.Dominance.Basic
import all Veir.IR.Basic
import all Veir.IR.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Interfaces.RegionKindInterfaces
import all Veir.Interpreter.Refinement.Basic

namespace Veir.Puddle.CTree
public section

private theorem ancestor_eq_of_parent_none {ctx : WfIRContext OpCode} {ancestor root : IRNode}
    (ancestry : ancestor.Ancestor root ctx) (noParent : root.parent! ctx = none) : ancestor = root := by
  obtain ⟨nodes, path⟩ := ancestry.exists_parentPath
  cases path with
  | single => rfl
  | cons immediate tail => simp_all

/-- A named function directly inside a verified builtin module, and the entry of its
body, are rooted at that module. The body entry is hierarchically reachable. -/
theorem module_function_entry_placement
    {ctx : WfIRContext OpCode} {moduleOp function : OperationPtr} {name : StringAttr}
    (verified : ctx.Verified moduleOp)
    (moduleCode : moduleOp.getOpType! ctx.raw = .builtin .module)
    (moduleNoParent : moduleOp.getParent! ctx.raw = none)
    (functionIn : function.InBounds ctx.raw)
    (named : function.IsTopLevelFuncWithName moduleOp ctx.raw name)
    (functionView : FunctionOp ctx.raw function)
    (hasBody : 0 < function.getNumRegions! ctx.raw)
    {region : RegionPtr} (body : functionView.getFunctionBody! = region)
    {entry : BlockPtr} (first : region.getFirstBlock! ctx.raw = some entry) :
    function.RootedAt moduleOp ctx ∧ entry.RootedAt moduleOp ctx ∧ entry.HierarchicallyReachable ctx := by
  obtain ⟨moduleBlock, moduleRegion, functionParent, blockParent, regionParent⟩ :=
    OperationPtr.getParentOp!_eq_some_iff.mp named.isTopLevel
  have rootNone : (IRNode.operation moduleOp).parent! ctx = none := by
    simp [IRNode.parent!, moduleNoParent]
  have functionRooted : function.RootedAt moduleOp ctx :=
    ⟨IRNode.Ancestor.of_getParentOp!_eq_some named.isTopLevel, rootNone⟩
  have bodyParent : region.getParent! ctx.raw = some function := by
    simpa only [body] using functionView.getFunctionBody!_parent functionIn hasBody
  have entryParent : entry.getParent! ctx.raw = some region := by grind
  have entryBody : region.Ancestor entry ctx := .of_parent (by simp [IRNode.parent!, entryParent])
  have functionEntry : function.Ancestor entry ctx :=
    IRNode.Ancestor.trans_parent_ancestor (by simp [IRNode.parent!, bodyParent]) entryBody
  have entryRooted : entry.RootedAt moduleOp ctx := ⟨functionRooted.1.trans functionEntry, rootNone⟩
  have regionIn : moduleRegion.InBounds ctx.raw := by grind
  have graph : moduleRegion.getRegionKind ctx = .Graph := by
    simp only [RegionPtr.getRegionKind, regionParent, moduleCode]
    rfl
  have sameEnds := verified.graph_region_firstBlock_eq_lastBlock regionIn regionParent
    (by simp [moduleCode]) graph
  have moduleFirst : moduleRegion.getFirstBlock! ctx.raw = some moduleBlock := by
    cases get : moduleRegion.getFirstBlock! ctx.raw with
    | none =>
      obtain ⟨blocks, chain⟩ := ctx.wellFormed.blockChain moduleRegion regionIn
      grind [RegionPtr.BlockChain]
    | some firstBlock =>
      have equal : moduleBlock = firstBlock := RegionPtr.block_eq_of_first_eq_last ctx.wellFormed
        blockParent get (sameEnds.symm.trans get)
      simp only [← equal]
  refine ⟨functionRooted, entryRooted, ?_⟩
  intro ancestor ancestry ancestorRegion ancestorParent
  have sameBlock : ancestor = entry ∨ ancestor = moduleBlock := by
    by_cases same : ancestor = entry
    · exact Or.inl same
    · have aboveBody := (ancestry.toProperAncestor (by simpa using same)).ancestor_of_parent_descendant
        (show (IRNode.block entry).parent! ctx = some (.region region) by simp [IRNode.parent!, entryParent])
      have aboveFunction := (aboveBody.toProperAncestor (by simp)).ancestor_of_parent_descendant
        (show (IRNode.region region).parent! ctx = some (.operation function) by simp [IRNode.parent!, bodyParent])
      have aboveBlock := (aboveFunction.toProperAncestor (by simp)).ancestor_of_parent_descendant
        (show (IRNode.operation function).parent! ctx = some (.block moduleBlock) by simp [IRNode.parent!, functionParent])
      by_cases same : ancestor = moduleBlock
      · exact Or.inr same
      · have aboveModuleRegion := (aboveBlock.toProperAncestor (by simpa using same)).ancestor_of_parent_descendant
          (show (IRNode.block moduleBlock).parent! ctx = some (.region moduleRegion) by simp [IRNode.parent!, blockParent])
        have aboveModule := (aboveModuleRegion.toProperAncestor (by simp)).ancestor_of_parent_descendant
          (show (IRNode.region moduleRegion).parent! ctx = some (.operation moduleOp) by simp [IRNode.parent!, regionParent])
        have impossible := ancestor_eq_of_parent_none aboveModule rootNone
        simp at impossible
  rcases sameBlock with same | same
  · subst ancestor
    have same : ancestorRegion = region := by grind
    subst ancestorRegion
    exact ⟨entry, [entry], first, .Single entryParent⟩
  · subst ancestor
    have same : ancestorRegion = moduleRegion := by grind
    subst ancestorRegion
    exact ⟨moduleBlock, [moduleBlock], moduleFirst, .Single blockParent⟩

end
end Veir.Puddle.CTree
