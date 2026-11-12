module

import all Veir.Verifier

public import Veir.PatternRewriter.Puddle.MatcherRegionScope
import all Veir.PatternRewriter.Puddle.MatcherScope
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.CTreeEntryInvariant
import all Veir.Interpreter.CTreeEquationLemma
import all Veir.Dominance.Basic

public section

namespace Veir.Puddle

/-- Available function-local values, expressed without assigning the resolver an IR context.
This lets the rewritten program supply values while the matcher refers to the original IR. -/
def ValueResolver.DefinesDominatingIn (resolve : ValueResolver) (ctx : WfIRContext OpCode)
    (region : RegionPtr) (rewriteRoot : OperationPtr) (point : InsertPoint) : Prop :=
  ∀ value, value.InBounds ctx.raw → value.DefinedInRegion region ctx →
    value.DominatesIp (.before rewriteRoot) ctx → value.DominatesIp point ctx → ∃ runtime,
      resolve value = some runtime ∧ runtime.Conforms (value.getType! ctx.raw)

/-- A historical primitive return attached to the original IR and a context-independent resolver. -/
def ValueResolver.CTreeEquationHolds (resolve : ValueResolver) (ctx : WfIRContext OpCode)
    (op : OperationPtr) : Prop :=
  ∃ operands results before after,
    (op.getOperands! ctx.raw).mapM resolve = some operands ∧
    (op.getResults! ctx.raw).mapM resolve = some results ∧
    PureOrErr.CanInterpretTo
      (Veir.CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
        operands (op.getSuccessors! ctx.raw) before (op.getRegions! ctx.raw))
      (.ok (results, after, none))

/-- History needed by this matcher: only original operations dominating the rewrite root
and the current execution point are tracked. Their operands are unaffected by replacement. -/
def ValueResolver.CTreeEquationLemmaIn (resolve : ValueResolver) (ctx : WfIRContext OpCode)
    (region : RegionPtr) (rewriteRoot : OperationPtr) (point : InsertPoint) : Prop :=
  ∀ (op : OperationPtr), op.InBounds ctx.raw → region.Ancestor op ctx →
    HasOpInfo.isTerminator (op.getOpType! ctx.raw) = false →
    op.DominatesIp (.before rewriteRoot) ctx → op.DominatesIp point ctx →
    resolve.CTreeEquationHolds ctx op

/-- Typed source states supply the corresponding resolver invariant. -/
theorem ValueResolver.definesDominatingIn_of_state {ctx : WfIRContext OpCode}
    {state : InterpreterState ctx} {region : RegionPtr} {point : InsertPoint}
    (rewriteRoot : OperationPtr)
    (defined : state.DefinesDominatingIn region point) :
    ValueResolver.DefinesDominatingIn state.variables.getVar? ctx region rewriteRoot point := by
  intro pointer bounds inside _ dominance
  obtain ⟨runtime, lookup⟩ := Option.isSome_iff_exists.mp
    (defined pointer bounds inside dominance)
  exact ⟨runtime, lookup, VariableState.getVar?_conforms lookup⟩

theorem ValueResolver.ctreeEquationLemmaIn_of_state {ctx : WfIRContext OpCode}
    {state : VariableState ctx} {region : RegionPtr} {point : InsertPoint}
    (excluded : OperationPtr) (history : state.CTreeEquationLemmaIn region point) :
    ValueResolver.CTreeEquationLemmaIn state.getVar? ctx region excluded point := by
  intro op bounds inside nonterm _ dominance
  exact history op bounds inside nonterm dominance

/-- Fresh writes preserve a historical equation whenever its operand and result lookups survive. -/
theorem ValueResolver.CTreeEquationHolds.of_lookup_eq
    {resolve updated : ValueResolver} {ctx : WfIRContext OpCode} {op : OperationPtr}
    (history : resolve.CTreeEquationHolds ctx op)
    (operands : ∀ value ∈ op.getOperands! ctx.raw, updated value = resolve value)
    (results : ∀ value ∈ op.getResults! ctx.raw, updated value = resolve value) :
    updated.CTreeEquationHolds ctx op := by
  obtain ⟨args, values, before, after, argsGet, valuesGet, outcome⟩ := history
  refine ⟨args, values, before, after, ?_, ?_, outcome⟩
  · have eq : (op.getOperands! ctx.raw).mapM updated = (op.getOperands! ctx.raw).mapM resolve := by
      exact Veir.mapM_eq_of_mem _ _ _ operands
    exact eq.trans argsGet
  · have eq : (op.getResults! ctx.raw).mapM updated = (op.getResults! ctx.raw).mapM resolve := by
      exact Veir.mapM_eq_of_mem _ _ _ results
    exact eq.trans valuesGet

/-- Preserving the original slots preserves the matcher's available inputs. -/
theorem ValueResolver.DefinesDominatingIn.of_lookup_eq
    {resolve updated : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot : OperationPtr} {point : InsertPoint}
    (defined : resolve.DefinesDominatingIn ctx region rewriteRoot point)
    (preserved : ∀ pointer, pointer.InBounds ctx.raw → updated pointer = resolve pointer) :
    updated.DefinesDominatingIn ctx region rewriteRoot point := by
  intro pointer bounds inside static dynamic
  obtain ⟨runtime, lookup, conforms⟩ := defined pointer bounds inside static dynamic
  exact ⟨runtime, (preserved pointer bounds).trans lookup, conforms⟩

/-- Preserving all original slots preserves the original matcher history, regardless of
additional fresh values held by the resolver. -/
theorem ValueResolver.CTreeEquationLemmaIn.of_lookup_eq
    {resolve updated : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot : OperationPtr} {point : InsertPoint}
    (history : resolve.CTreeEquationLemmaIn ctx region rewriteRoot point)
    (preserved : ∀ pointer, pointer.InBounds ctx.raw → updated pointer = resolve pointer) :
    updated.CTreeEquationLemmaIn ctx region rewriteRoot point := by
  intro op bounds inside nonterm static dynamic
  apply (history op bounds inside nonterm static dynamic).of_lookup_eq
  · intro pointer member
    exact preserved pointer (by grind)
  · intro pointer member
    exact preserved pointer (by grind)

/-- The resolver history is initially empty at the entry of the interpreted SSA region. -/
theorem ValueResolver.ctreeEquationLemmaIn_entry
    {ctx : WfIRContext OpCode} (resolve : ValueResolver)
    {region : RegionPtr} {entry : BlockPtr} {irRoot : IRNode} (rewriteRoot : OperationPtr)
    (first : region.getFirstBlock! ctx.raw = some entry)
    (parent : entry.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) (rooted : entry.RootedAt irRoot ctx) :
    resolve.CTreeEquationLemmaIn ctx region rewriteRoot (InsertPoint.atStart! entry ctx.raw) := by
  intro op _ inside _ _ dominance
  exact False.elim
    (OperationPtr.not_dominatesIp_region_entry first parent ssa rooted inside dominance)

/-- A raw return establishes a historical equation after its result values have been installed. -/
theorem ValueResolver.DefinesDominatingIn.from_root
    {resolve : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot : OperationPtr}
    (defined : resolve.DefinesDominatingIn ctx region rewriteRoot (.before rewriteRoot))
    (point : InsertPoint) : resolve.DefinesDominatingIn ctx region rewriteRoot point := by
  intro value bounds inside static _
  exact defined value bounds inside static static

/-- Once execution reaches the rewrite root, all statically watched equations are available.
Fresh creation can preserve these equations through the entire replacement sequence. -/
theorem ValueResolver.CTreeEquationLemmaIn.from_root
    {resolve : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot : OperationPtr}
    (history : resolve.CTreeEquationLemmaIn ctx region rewriteRoot (.before rewriteRoot))
    (point : InsertPoint) : resolve.CTreeEquationLemmaIn ctx region rewriteRoot point := by
  intro op bounds inside nonterm static _
  exact history op bounds inside nonterm static static

/-- A raw return establishes a historical equation after its result values have been installed. -/
theorem ValueResolver.ctreeEquationHolds_of_outcome
    {resolve updated : ValueResolver} {ctx : WfIRContext OpCode} {op : OperationPtr}
    {operands results : Array RuntimeValue} {before after : MemoryState}
    (operandsGet : (op.getOperands! ctx.raw).mapM resolve = some operands)
    (operandsPreserved : ∀ value ∈ op.getOperands! ctx.raw, updated value = resolve value)
    (resultsGet : (op.getResults! ctx.raw).mapM updated = some results)
    (outcome : PureOrErr.CanInterpretTo
      (Veir.CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
        operands (op.getSuccessors! ctx.raw) before (op.getRegions! ctx.raw))
      (.ok (results, after, none))) : updated.CTreeEquationHolds ctx op :=
  ⟨operands, results, before, after,
    (Veir.mapM_eq_of_mem _ _ _ operandsPreserved).trans operandsGet, resultsGet, outcome⟩

/-- Installing an original operation's results preserves earlier observed producers.
An equation for the current operation is needed only if the matcher can inspect it. -/
theorem ValueResolver.CTreeEquationLemmaIn.after_operation
    {resolve updated : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot op : OperationPtr} {block : BlockPtr} {irRoot : IRNode}
    (ctxDom : ctx.Dom irRoot) (opRooted : op.RootedAt irRoot ctx)
    (opRegion : op.getParentRegion! ctx.raw = some region) (ssa : region.hasSSADominance ctx)
    (opReachable : op.HierarchicallyReachable ctx)
    (opParent : op.getParent! ctx.raw = some block)
    (prior : resolve.CTreeEquationLemmaIn ctx region rewriteRoot (.before op))
    (preserved : ∀ value, value.InBounds ctx.raw → value ∉ op.getResults! ctx.raw →
      updated value = resolve value)
    (observed : HasOpInfo.isTerminator (op.getOpType! ctx.raw) = false →
      op.DominatesIp (.before rewriteRoot) ctx → updated.CTreeEquationHolds ctx op) :
    updated.CTreeEquationLemmaIn ctx region rewriteRoot (InsertPoint.after op ctx.raw block) := by
  intro earlier earlierIn inside nonterm static dynamic
  simp [OperationPtr.DominatesIp.after_iff opRooted
    (show block.getParent! ctx.raw = some region by grind)] at dynamic
  simp [OperationPtr.dominates_iff_properlyDominates_or_eq] at dynamic
  rcases dynamic with old | self
  · apply (prior earlier earlierIn inside nonterm static (.Before old)).of_lookup_eq
    · intro value member
      apply preserved value (by grind)
      have dominance : earlier.Dominates op ctx false := Or.inr old
      obtain ⟨earlierRegion, earlierParent⟩ := dominance.exists_parentRegion opRegion
      grind [WfIRContext.Dom.not_mem_results_of_mem_operands]
    · intro value member
      apply preserved value (by grind)
      intro other
      have different : earlier ≠ op := by
        intro equal
        subst earlier
        exact OperationPtr.not_properlyDominates_self opRooted opRegion ssa old
      grind [OperationPtr.getResults!.mem_iff_exists_index, OperationPtr.getResult_def]
  · subst earlier
    exact observed nonterm static

/-- The available matcher inputs survive an original operation step. -/
theorem ValueResolver.DefinesDominatingIn.after_operation
    {resolve updated : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot op : OperationPtr} {block : BlockPtr}
    (opParent : op.getParent! ctx.raw = some block)
    (blockParent : block.getParent! ctx.raw = some region)
    (prior : resolve.DefinesDominatingIn ctx region rewriteRoot (.before op))
    (preserved : ∀ value, value.InBounds ctx.raw → value ∉ op.getResults! ctx.raw →
      updated value = resolve value)
    (installed : ∀ value ∈ op.getResults! ctx.raw, ∃ runtime,
      updated value = some runtime ∧ runtime.Conforms (value.getType! ctx.raw)) :
    updated.DefinesDominatingIn ctx region rewriteRoot (InsertPoint.after op ctx.raw block) := by
  intro value bounds inside static dynamic
  by_cases result : value ∈ op.getResults! ctx.raw
  · exact installed value result
  · obtain old | fresh := (ValuePtr.DominatesIp.after_iff blockParent).mp dynamic
    · obtain ⟨runtime, lookup, conforms⟩ := prior value bounds inside static old
      exact ⟨runtime, (preserved value bounds result).trans lookup, conforms⟩
    · exact False.elim (result fresh)

/-- Matcher equations from original-IR history held by an arbitrary runtime resolver.
The resolver may be the variable state of the rewritten program. -/
theorem ValueResolver.CTreeEquationLemmaIn.successor_entry
    {resolve updated : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot : OperationPtr} {block succ : BlockPtr} {irRoot : IRNode}
    (ctxDom : ctx.Dom irRoot) (blockIn : block.InBounds ctx.raw)
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) (successor : succ ∈ block.getSuccessors! ctx.raw)
    (succRooted : succ.RootedAt irRoot ctx) (succReachable : succ.HierarchicallyReachable ctx)
    (prior : resolve.CTreeEquationLemmaIn ctx region rewriteRoot (.atEnd block))
    (preserved : ∀ value, value.InBounds ctx.raw → value ∉ succ.getArguments! ctx.raw →
      updated value = resolve value) :
    updated.CTreeEquationLemmaIn ctx region rewriteRoot (InsertPoint.atStart! succ ctx.raw) := by
  intro op bounds inside nonterm static dynamic
  have opRooted : op.RootedAt irRoot ctx := by grind
  have opReachable : op.HierarchicallyReachable ctx := by grind
  have succIn : succ.InBounds ctx.raw := by grind [BlockPtr.getParent!_of_not_inBounds]
  have ipParent : (InsertPoint.atStart! succ ctx.raw).block! ctx.raw = some succ :=
    InsertPoint.block!_atStart!_eq ctx.wellFormed succIn
  obtain ⟨opRegion, opParentRegion⟩ := dynamic.exists_parentRegion ipParent succParent
  have old : op.DominatesIp (.atEnd block) ctx := by
    grind [OperationPtr.DominatesIp.predecessor_exit_of_successor_entry]
  apply (prior op bounds inside nonterm static old).of_lookup_eq
  · intro value member
    apply preserved value (by grind)
    intro argument
    have operandDominates : value.DominatesIp (.before op) ctx := by grind
    have excludes : ¬value.DominatesIp (.before op) ctx := by grind
    exact excludes operandDominates
  · intro value member
    apply preserved value (by grind)
    grind [OperationPtr.getResults!.mem_iff_exists_index, BlockPtr.getArguments!.mem_iff_exists_index,
      OperationPtr.getResult_def, BlockPtr.getArgument_def]

/-- Installing a successor's arguments maintains the available matcher dependencies. -/
theorem ValueResolver.DefinesDominatingIn.successor_entry
    {resolve updated : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot : OperationPtr} {block succ : BlockPtr}
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) (successor : succ ∈ block.getSuccessors! ctx.raw)
    (prior : resolve.DefinesDominatingIn ctx region rewriteRoot (.atEnd block))
    (preserved : ∀ value, value.InBounds ctx.raw → value ∉ succ.getArguments! ctx.raw →
      updated value = resolve value)
    (installed : ∀ value ∈ succ.getArguments! ctx.raw, ∃ runtime,
      updated value = some runtime ∧ runtime.Conforms (value.getType! ctx.raw)) :
    updated.DefinesDominatingIn ctx region rewriteRoot (InsertPoint.atStart! succ ctx.raw) := by
  intro value bounds inside static dynamic
  by_cases argument : value ∈ succ.getArguments! ctx.raw
  · exact installed value argument
  · obtain old | argument' := ValuePtr.DominatesIp.predecessor_exit_of_successor_entry
        blockParent succParent ssa successor dynamic
    · obtain ⟨runtime, lookup, conforms⟩ := prior value bounds inside static old
      exact ⟨runtime, (preserved value bounds argument).trans lookup, conforms⟩
    · exact False.elim (argument argument')

/-- Matcher equations from original-IR history held by an arbitrary runtime resolver.
The resolver may be the variable state of the rewritten program. -/
theorem CTree.Pattern.Valid.runtimeEquations_of_resolver_history
    {rule : Pattern OpCode} (valid : CTree.Pattern.Valid rule)
    {ctx : WfIRContext OpCode} {root : OperationPtr} {region : RegionPtr} {irRoot : IRNode}
    {assignment : Assignment OpCode} (resolve : ValueResolver)
    (ctxDom : ctx.Dom irRoot) {verifyRoot : OperationPtr}
    (ctxVerified : ctx.Verified verifyRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (matched : rule.matcher.run ctx.raw root = some assignment)
    (localScope : assignment.RegionScope ctx region)
    (operandScope : ∀ value ∈ root.getOperands! ctx.raw, value.DefinedInRegion region ctx)
    (defined : resolve.DefinesDominatingIn ctx region root (.before root))
    (history : resolve.CTreeEquationLemmaIn ctx region root (.before root)) :
    ∀ decl ∈ rule.matcher.decls, CTree.MatchDecl.RuntimeEquations ctx.raw rule.matcher.rootHandle
      resolve assignment decl := by
  obtain ⟨rootResults, rootScope, matchscope⟩ := valid.matcherScope_of_run
    ctxDom rootRooted rootRegion rootReachable rootIn matched
  have bounds := rule.matcher.inBounds_of_run rootIn matched
  intro decl member
  cases decl with
  | value ty handle =>
    intro pointer pointerGet
    exact defined pointer (bounds.getValue pointerGet) (localScope.getValue pointerGet)
      (matchscope.getValue pointerGet (rootScope.leaf ty handle member))
      (matchscope.getValue pointerGet (rootScope.leaf ty handle member))
  | operation code operands types matcher property handle results count =>
    intro observed observedGet sameCode
    have observedIn := bounds.getOp observedGet
    refine ⟨⟨ctx, observed, observedIn,
      OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerified observedIn,
      sameCode, rfl, rfl, rfl⟩, ?_⟩
    have supported := valid.Supported.1 _ member
    by_cases isRoot : handle = rule.matcher.rootHandle
    · have rootGet := rule.matcher.getOp_root_of_run matched
      rw [isRoot, rootGet] at observedGet
      cases observedGet
      obtain ⟨localRegion, reachable⟩ := rootReachable.exists_locallyReachable rootRegion
      have available : ∃ args, (root.getOperands! ctx.raw).mapM resolve = some args := by
        apply Array.exists_mapM_option_eq_some_iff.mpr
        intro index indexIn
        obtain ⟨runtime, lookup, _⟩ := defined (root.getOperands! ctx.raw)[index] (by grind)
          (operandScope _ (by grind)) (by grind [WfIRContext.Dom.operand_dominatesIp_before])
          (by grind [WfIRContext.Dom.operand_dominatesIp_before])
        exact ⟨runtime, lookup⟩
      obtain ⟨args, argsGet⟩ := available
      refine ⟨args.toList, lookup_list_of_array _ _ _ argsGet, ?_⟩
      intro different
      exact False.elim (different isRoot)
    · have nonroot := rootScope.nonrootOperation code operands types matcher property handle results count member isRoot
      have dominates : observed.ProperlyDominates root ctx false := by
        rcases matchscope.getOp observedGet with ⟨_, equal⟩ | dominance
        · exact False.elim (nonroot.1 equal)
        · exact dominance
      subst code
      have nonterm : HasOpInfo.isTerminator (observed.getOpType! ctx.raw) = false := by
        simpa only using supported
      have inside : region.Ancestor observed ctx :=
        IRNode.Ancestor.of_getParentRegion!_eq_some (localScope.getOp observedGet)
      obtain ⟨args, values, before, after, argsGet, valuesGet, outcome⟩ :=
        history observed observedIn inside nonterm (.Before dominates) (.Before dominates)
      refine ⟨args.toList, lookup_list_of_array _ _ _ argsGet, ?_⟩
      intro _
      refine ⟨values.toList, lookup_list_of_array _ _ _ valuesGet, before, after, ?_⟩
      have successors := Veir.CTree.interpretOp'_successors_irrelevant
        (observed.getOpType! ctx.raw) (observed.getProperties! ctx.raw (observed.getOpType! ctx.raw))
        (observed.getResultTypes! ctx.raw) args (observed.getSuccessors! ctx.raw) #[] before
        (observed.getRegions! ctx.raw) nonterm
      rw [successors] at outcome
      simpa only [Interp.map, Array.toArray_toList, Veir.CTree.interpretOp'] using outcome
  | type => trivial
  | inspectOperation => trivial
  | applyNative => trivial

end Veir.Puddle
