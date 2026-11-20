module

public import Veir.PatternRewriter.Puddle.MatcherScope
public import Veir.PatternRewriter.Puddle.CreationStructure
public import Veir.PatternRewriter.Puddle.CTreeExecutionSoundness
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.PatternRewriter.Puddle.MatcherScope
import all Veir.PatternRewriter.Puddle.CreationSemantics
import all Veir.Dominance.Basic
import all Veir.IR.Basic

namespace Veir.Puddle

public section

/-- A replacement input is an old value available before the root, or a freshly allocated value. -/
def ReplacementValueScope (original : WfIRContext OpCode) (root : OperationPtr) (value : ValuePtr) : Prop :=
  value.DominatesIp (.before root) original ∨ ¬value.InBounds original.raw

/-- Only statically available value handles can feed creation or the final replacement. -/
def Assignment.ReplacementScope (assignment : Assignment OpCode) (original : WfIRContext OpCode)
    (root : OperationPtr) (defined : HandleContext) : Prop :=
  ∀ (handle : Handle OpCode .value), defined.require handle = true →
    ∀ value, assignment.getValue handle = some value → ReplacementValueScope original root value

theorem Assignment.ReplacementScope.bind_insertFresh
    {original : WfIRContext OpCode} {root : OperationPtr} {before after : HandleContext}
    {a b : Assignment OpCode} {kind : HandleType OpCode} {handle : Handle OpCode kind}
    {binding : Binding OpCode} (scope : a.ReplacementScope original root before)
    (collected : before.insertFresh handle = some after) (bound : a.bind handle binding = some b)
    (newValue : ∀ value, binding = .value value → ReplacementValueScope original root value) :
    b.ReplacementScope original root after := by
  intro queried required value hvalue
  have hb : b.getBinding queried = some (.value value) := by
    cases hread : b.getBinding queried with
    | none => simp [Assignment.getValue, hread] at hvalue
    | some existing => cases existing <;> simp_all [Assignment.getValue]
  by_cases heq : queried.id = handle.id
  · have installed := Assignment.getBinding_of_bind bound
    have hsame : b.getBinding queried = some binding := by
      simpa [Assignment.getBinding, heq] using installed
    exact newValue value (Option.some.inj (hsame.symm.trans hb))
  · have hbefore : before.require queried = true := by
      rw [← HandleContext.require_of_insertFresh_of_ne collected heq]
      exact required
    have hread : a.getValue queried = some value := by
      rw [Assignment.getBinding_of_bind_of_ne queried bound heq] at hb
      simp [Assignment.getValue, hb]
    exact scope queried hbefore value hread

theorem Assignment.ReplacementScope.bindValues_insertManyFresh
    {original : WfIRContext OpCode} {root : OperationPtr} {before after : HandleContext}
    {a b : Assignment OpCode} {handles : List (Handle OpCode .value)} {values : List ValuePtr}
    (scope : a.ReplacementScope original root before)
    (collected : before.insertManyFresh handles = some after) (bound : a.bindValues handles values = some b)
    (newValues : ∀ value ∈ values, ReplacementValueScope original root value) :
    b.ReplacementScope original root after := by
  induction handles generalizing a before values with
  | nil =>
    cases values with
    | nil => cases bound; cases collected; exact scope
    | cons value values => simp [Assignment.bindValues] at bound
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindValues] at bound
    | cons value values =>
      simp only [Assignment.bindValues, HandleContext.insertManyFresh, List.foldlM_cons,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at bound collected
      obtain ⟨middle, hb, hr⟩ := bound
      obtain ⟨middleContext, hc, hcr⟩ := collected
      have hscope := scope.bind_insertFresh hc hb (fun other heq => by
        cases heq; exact newValues value (by simp))
      exact ih hscope hcr hr (fun other hm => newValues other (by simp [hm]))

theorem MetadataTuple.Shape.replacementScope_bind
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {original : WfIRContext OpCode} {root : OperationPtr} {before after : HandleContext}
    {a b : Assignment OpCode} (scope : a.ReplacementScope original root before)
    (collected : shape.insertFreshBindings before handles = some after)
    (bound : shape.bind a handles values = some b) : b.ReplacementScope original root after := by
  induction shape generalizing a before with
  | unit => cases bound; cases collected; exact scope
  | atom atom =>
    cases atom <;> exact scope.bind_insertFresh collected bound (fun _ h => by cases h)
  | cons atom tail ih =>
    cases atom <;>
      simp only [MetadataTuple.Shape.bind, MetadataTuple.Shape.insertFreshBindings,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at bound collected
    all_goals
      obtain ⟨middle, hh, ht⟩ := bound
      obtain ⟨middleContext, hc, hct⟩ := collected
      exact ih _ _ (scope.bind_insertFresh hc hh (fun _ h => by cases h)) hct ht

theorem CreateDecl.replacementScope_of_run (decl : CreateDecl OpCode)
    {original before created : WfIRContext OpCode} {root : OperationPtr}
    {beforeContext afterContext : HandleContext} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (scope : a.ReplacementScope original root beforeContext)
    (stage : Veir.WfIRContext.WithCreatedOps original before)
    (checked : decl.checkBindings beforeContext = some afterContext)
    (run : decl.run a before = some (created, newOps, b)) :
    b.ReplacementScope original root afterContext := by
  cases decl with
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨bound, hb, rfl, _, rfl⟩ := run
    exact scope.bind_insertFresh checked hb (fun _ h => by cases h)
  | property code value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨bound, hb, rfl, _, rfl⟩ := run
    exact scope.bind_insertFresh checked hb (fun _ h => by cases h)
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨values, _, outputValues, _, bound, hb, rfl, _, rfl⟩ := run
    simp only [CreateDecl.checkBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨u, _, houtputs⟩ := checked
    exact MetadataTuple.Shape.replacementScope_bind _ _ outputValues scope houtputs hb
  | operation code operands types property opHandle results =>
    simp only [CreateDecl.checkBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨u₁, _, u₂, _, u₃, _, u₄, _, middleContext, hop, hresults⟩ := checked
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨operandPtrs, _, resultTypes, _, props, _, u, _, hrun⟩ := run
    split at hrun
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨⟨allocated, newOp⟩, hcreate, bound, hbound, boundResults, hboundResults, rfl, _, rfl⟩ := hrun
      have hscope := scope.bind_insertFresh hop hbound (fun _ h => by cases h)
      apply hscope.bindValues_insertManyFresh hresults hboundResults
      intro value hvalue
      right
      have hfresh := WfRewriter.createOp_new_not_inBounds newOp hcreate
      have hsourceFresh : ¬newOp.InBounds original.raw := by
        intro hin
        exact hfresh (stage.inBounds_mono (.operation newOp) hin)
      have hmem : value ∈ newOp.getResults! allocated.raw := by simpa using hvalue
      obtain ⟨index, _, hvalueEq⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp hmem
      subst value
      grind
    · contradiction

private theorem creation_prefix_trans {a b c : WfIRContext OpCode}
    (hab : Veir.WfIRContext.WithCreatedOps a b) (hbc : Veir.WfIRContext.WithCreatedOps b c) :
    Veir.WfIRContext.WithCreatedOps a c := by
  induction hbc with
  | Nil => exact hab
  | CreatedOp _ _ _ _ h ih => exact .CreatedOp _ _ _ (ih hab) h

theorem CreateProg.replacementScope_of_runDecls (decls : List (CreateDecl OpCode))
    {original before created : WfIRContext OpCode} {root : OperationPtr}
    {beforeContext afterContext : HandleContext} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (scope : a.ReplacementScope original root beforeContext)
    (stage : Veir.WfIRContext.WithCreatedOps original before)
    (checked : decls.foldlM CreateDecl.checkBindings beforeContext = some afterContext)
    (run : CreateProg.runDecls decls before a = some (created, newOps, b)) :
    b.ReplacementScope original root afterContext := by
  induction decls generalizing before a beforeContext newOps with
  | nil =>
    simp only [CreateProg.runDecls, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, _, rfl⟩ := run
    cases checked
    exact scope
  | cons decl rest ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨middleContext, hdeclChecked, hrestChecked⟩ := checked
    simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨⟨middle, firstOps, middleAssignment⟩, hfirst, ⟨last, restOps, finalAssignment⟩,
      hrest, rfl, _, hfinal⟩ := run
    subst b
    have hscope := decl.replacementScope_of_run scope stage hdeclChecked hfirst
    have hprefix := creation_prefix_trans stage (CreateDecl.run_withCreatedOps decl _ _ _ _ _ hfirst)
    exact ih hscope hprefix hrestChecked hrest


theorem Assignment.ReplacementScope.getValues
    {original : WfIRContext OpCode} {root : OperationPtr} {defined : HandleContext}
    {assignment : Assignment OpCode} {handles : Array (Handle OpCode .value)} {values : Array ValuePtr}
    (scope : assignment.ReplacementScope original root defined)
    (required : defined.requireMany handles.toList = true)
    (read : assignment.getValues handles = some values) :
    ∀ value ∈ values, ReplacementValueScope original root value := by
  intro value member
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem member
  have hread := Array.mapM_option_eq_some_implies read i hi
  have hsize := Array.size_eq_of_mapM_eq_some read
  have hiHandles : i < handles.size := by omega
  have hrequired : defined.require handles[i] = true := by
    simp only [HandleContext.requireMany, List.all_eq_true] at required
    exact required _ (by simp)
  exact scope _ hrequired _ hread

/-- The static root-result prohibition and concrete matcher scope initialize creation safety. -/
theorem CTree.Pattern.Valid.replacementScope_of_match {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx : WfIRContext OpCode} {root : OperationPtr}
    {assignment : Assignment OpCode} {defined : HandleContext}
    (ctxDom : ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (run : rule.matcher.run ctx.raw root = some assignment)
    (collected : rule.matcher.collectBindings = some defined) :
    assignment.ReplacementScope ctx root defined := by
  obtain ⟨results, rootScope, scope⟩ := valid.matcherScope_of_run
    ctxDom rootRooted rootRegion rootReachable rootIn run
  simp only [MatchProg.collectBindings, rootScope.resultsIdentified, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at collected
  obtain ⟨_, hresults, rawDefined, _, hdefined⟩ := collected
  cases hresults
  subst defined
  intro handle required value read
  left
  exact scope.getValue read (HandleContext.require_of_forbidMany results.toList required).2

/-- Every returned replacement either properly precedes the root or was freshly allocated. -/
theorem CTree.Pattern.Valid.replacementScope_of_interpret {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx created : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {values : Array ValuePtr}
    (ctxDom : ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (run : rule.interpret ctx root = some (created, some (newOps, values))) :
    ∀ value ∈ values, ReplacementValueScope ctx root value := by
  obtain ⟨beforeContext, afterContext, collected, checked, required⟩ :=
    Pattern.creation_check_of_structurallyWellFormed valid.structurallyWellFormed
  unfold Pattern.interpret at run
  cases hm : rule.matcher.run ctx.raw root with
  | none => simp [hm] at run
  | some matched =>
    simp only [hm] at run
    cases hc : rule.creation.run matched ctx with
    | none => simp [hc] at run
    | some output =>
      obtain ⟨allocated, ops, finalAssignment⟩ := output
      simp only [hc] at run
      cases hv : finalAssignment.getValues rule.replacement.values with
      | none => simp [hv] at run
      | some returned =>
        simp only [hv, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, h⟩ := run
        obtain ⟨rfl, rfl⟩ := h
        have initial := valid.replacementScope_of_match ctxDom rootRooted rootRegion
          rootReachable rootIn hm collected
        have finalScope := CreateProg.replacementScope_of_runDecls rule.creation.decls initial
          (.Nil ctx) checked hc
        exact finalScope.getValues required hv


theorem ReplacementValueScope.dominates_of_inBounds
    {ctx : WfIRContext OpCode} {root : OperationPtr} {value : ValuePtr}
    (scope : ReplacementValueScope ctx root value) (inBounds : value.InBounds ctx.raw) :
    value.DominatesIp (.before root) ctx := by
  exact scope.resolve_right (fun h => h inBounds)

theorem ReplacementValueScope.notOwn
    {ctx : WfIRContext OpCode} {root : OperationPtr} {value : ValuePtr}
    (scope : ReplacementValueScope ctx root value)
    (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootSSA : region.hasSSADominance ctx) (rootIn : root.InBounds ctx.raw)
    (index : Nat) (indexBound : index < root.getNumResults! ctx.raw) :
    (root.getResult index : ValuePtr) ≠ value := by
  intro equal
  subst value
  rcases scope with dominated | fresh
  · have hproper := (ValuePtr.DominatesIp.before_iff.mp dominated).2
    exact OperationPtr.not_properlyDominates_self rootRooted rootRegion rootSSA
      (by simpa [ValuePtr.ProperlyDominates] using hproper)
  · apply fresh
    grind

/-- Concrete checked matching and creation discharge the driver's replacement safety contract
in an SSA region. This includes exclusion of the erased operation's own result slots. -/
theorem CTree.Pattern.Valid.replacement_contract_of_interpret {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx created : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {values : Array ValuePtr}
    (ctxDom : ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootSSA : region.hasSSADominance ctx)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (run : rule.interpret ctx root = some (created, some (newOps, values))) :
    (∀ value ∈ values, ∀ index < root.getNumResults! ctx.raw,
      (root.getResult index : ValuePtr) ≠ value) ∧
    (∀ value ∈ values, value.InBounds ctx.raw → value.DominatesIp (.before root) ctx) := by
  have scope := valid.replacementScope_of_interpret ctxDom rootRooted rootRegion rootReachable rootIn run
  exact ⟨fun value member index bound =>
    (scope value member).notOwn rootRooted rootRegion rootSSA rootIn index bound,
    fun value member bound => (scope value member).dominates_of_inBounds bound⟩


/-- Operands installed by creation retain the same source scope guarantee as replacement values. -/
theorem CreateDecl.operandScope_of_run (decl : CreateDecl OpCode)
    {original before created : WfIRContext OpCode} {root : OperationPtr}
    {beforeContext afterContext : HandleContext} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (scope : a.ReplacementScope original root beforeContext)
    (checked : decl.checkBindings beforeContext = some afterContext)
    (run : decl.run a before = some (created, newOps, b)) :
    ∀ op ∈ newOps, ∀ value ∈ op.getOperands! created.raw, ReplacementValueScope original root value := by
  cases decl with
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨bound, _, rfl, rfl, _⟩ := run
    simp
  | property code value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨bound, _, rfl, rfl, _⟩ := run
    simp
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨values, _, outputValues, _, bound, _, rfl, rfl, _⟩ := run
    simp
  | operation code operands types property opHandle results =>
    simp only [CreateDecl.checkBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨u₁, hrequired, _⟩ := checked
    have required : beforeContext.requireMany operands.toList = true := by simpa [guard] using hrequired
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨operandPtrs, hoperands, resultTypes, _, props, _, u, _, hrun⟩ := run
    split at hrun
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨⟨allocated, newOp⟩, hcreate, bound, _, boundResults, _, rfl, rfl, _⟩ := hrun
      intro op member value hvalue
      have hop : op = newOp := by simpa using member
      subst op
      have installed := OperationPtr.getOperands!_WfRewriter_createOp hcreate (operation := newOp)
      simp only [↓reduceIte] at installed
      rw [installed] at hvalue
      exact scope.getValues required hoperands value hvalue
    · contradiction

/-- Later allocations preserve the scope guarantee of operands installed earlier. -/
theorem CreateProg.operandScope_of_runDecls (decls : List (CreateDecl OpCode))
    {original before created : WfIRContext OpCode} {root : OperationPtr}
    {beforeContext afterContext : HandleContext} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (scope : a.ReplacementScope original root beforeContext)
    (stage : Veir.WfIRContext.WithCreatedOps original before)
    (checked : decls.foldlM CreateDecl.checkBindings beforeContext = some afterContext)
    (run : CreateProg.runDecls decls before a = some (created, newOps, b)) :
    ∀ op ∈ newOps, ∀ value ∈ op.getOperands! created.raw, ReplacementValueScope original root value := by
  induction decls generalizing before a beforeContext newOps with
  | nil =>
    simp only [CreateProg.runDecls, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, _⟩ := run
    simp
  | cons decl rest ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨middleContext, hdeclChecked, hrestChecked⟩ := checked
    simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨⟨middle, firstOps, middleAssignment⟩, hfirst, ⟨last, restOps, finalAssignment⟩,
      hrest, rfl, rfl, hfinal⟩ := run
    subst b
    have hscope := decl.replacementScope_of_run scope stage hdeclChecked hfirst
    have hstage := creation_prefix_trans stage (CreateDecl.run_withCreatedOps decl _ _ _ _ _ hfirst)
    have hhead := decl.operandScope_of_run scope hdeclChecked hfirst
    have htail := ih hscope hstage hrestChecked hrest
    intro op member value hvalue
    simp only [Array.mem_append] at member
    rcases member with first | rest
    · have opIn := ((decl.run_structure hfirst).1 op).mp first |>.1
      have fields := WfIRContext.WithCreatedOps.operation_fields
        (CreateProg.runDecls_withCreatedOps _ _ _ _ _ _ hrest) op opIn
      exact hhead op first value (by simpa [fields.2.2.1] using hvalue)
    · exact htail op rest value hvalue

/-- Every operand of every returned new operation excludes the matched root's old SSA slots. -/
theorem CTree.Pattern.Valid.createdOperandScope_of_interpret {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx created : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {values : Array ValuePtr}
    (ctxDom : ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (run : rule.interpret ctx root = some (created, some (newOps, values))) :
    ∀ op ∈ newOps, ∀ value ∈ op.getOperands! created.raw, ReplacementValueScope ctx root value := by
  obtain ⟨beforeContext, afterContext, collected, checked, _⟩ :=
    Pattern.creation_check_of_structurallyWellFormed valid.structurallyWellFormed
  unfold Pattern.interpret at run
  cases hm : rule.matcher.run ctx.raw root with
  | none => simp [hm] at run
  | some matched =>
    simp only [hm] at run
    cases hc : rule.creation.run matched ctx with
    | none => simp [hc] at run
    | some output =>
      obtain ⟨allocated, ops, finalAssignment⟩ := output
      simp only [hc] at run
      cases hv : finalAssignment.getValues rule.replacement.values with
      | none => simp [hv] at run
      | some returned =>
        simp only [hv, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, h⟩ := run
        obtain ⟨rfl, rfl⟩ := h
        have initial := valid.replacementScope_of_match ctxDom rootRooted rootRegion
          rootReachable rootIn hm collected
        exact CreateProg.operandScope_of_runDecls rule.creation.decls initial (.Nil ctx) checked hc


theorem CreateDecl.nonterminator_of_run (decl : CreateDecl OpCode)
    {before created : WfIRContext OpCode} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (supported : match decl with
      | .operation code .. => HasOpInfo.isTerminator code = false
      | _ => True)
    (run : decl.run a before = some (created, newOps, b)) :
    ∀ op ∈ newOps, HasOpInfo.isTerminator (op.getOpType! created.raw) = false := by
  cases decl with
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨bound, _, rfl, rfl, _⟩ := run
    simp
  | property code value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨bound, _, rfl, rfl, _⟩ := run
    simp
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨values, _, outputValues, _, bound, _, rfl, rfl, _⟩ := run
    simp
  | operation code operands types property opHandle results =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨operandPtrs, _, resultTypes, _, props, _, u, _, hrun⟩ := run
    split at hrun
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨⟨allocated, newOp⟩, hcreate, bound, _, boundResults, _, rfl, rfl, _⟩ := hrun
      intro op member
      have hop : op = newOp := by simpa using member
      subst op
      have installed := OperationPtr.getOpType!_WfRewriter_createOp hcreate (operation := newOp)
      have hcode : newOp.getOpType! allocated.raw = code := by simpa using installed
      rw [hcode]
      exact supported
    · contradiction

theorem CreateProg.nonterminator_of_runDecls (decls : List (CreateDecl OpCode))
    {before created : WfIRContext OpCode} {a b : Assignment OpCode} {newOps : Array OperationPtr}
    (supported : ∀ decl ∈ decls, match decl with
      | .operation code .. => HasOpInfo.isTerminator code = false
      | _ => True)
    (run : CreateProg.runDecls decls before a = some (created, newOps, b)) :
    ∀ op ∈ newOps, HasOpInfo.isTerminator (op.getOpType! created.raw) = false := by
  induction decls generalizing before a newOps with
  | nil =>
    simp only [CreateProg.runDecls, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, _⟩ := run
    simp
  | cons decl rest ih =>
    simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨⟨middle, firstOps, middleAssignment⟩, hfirst, ⟨last, restOps, finalAssignment⟩,
      hrest, rfl, rfl, hfinal⟩ := run
    subst b
    have hhead := decl.nonterminator_of_run (supported decl (by simp)) hfirst
    have htail := ih (fun decl hd => supported decl (List.mem_cons_of_mem _ hd)) hrest
    intro op member
    simp only [Array.mem_append] at member
    rcases member with first | rest
    · have opIn := ((decl.run_structure hfirst).1 op).mp first |>.1
      have fields := WfIRContext.WithCreatedOps.operation_fields
        (CreateProg.runDecls_withCreatedOps _ _ _ _ _ _ hrest) op opIn
      simpa [fields.1] using hhead op first
    · exact htail op rest

theorem CTree.Pattern.Valid.created_nonterminator_of_interpret {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx created : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {values : Array ValuePtr}
    (run : rule.interpret ctx root = some (created, some (newOps, values))) :
    ∀ op ∈ newOps, HasOpInfo.isTerminator (op.getOpType! created.raw) = false := by
  unfold Pattern.interpret at run
  split at run
  · simp_all
  · split at run
    · contradiction
    · rename_i matched hmatch createdCtx createdOps finalAssignment hcreate
      split at run
      · contradiction
      · cases run
        exact CreateProg.nonterminator_of_runDecls rule.creation.decls valid.Supported.2 hcreate


end

end Veir.Puddle
