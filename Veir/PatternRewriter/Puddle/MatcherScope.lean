module

import all Veir.Verifier

public import Veir.PatternRewriter.Puddle.ExecutionBounds
public import Veir.PatternRewriter.Puddle.HandleContextLemmas
public import Veir.Interpreter.CTreeEquationLemma
public import Veir.Interpreter.CTreeMemoryPreservation
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.ExecutionBounds
import all Veir.PatternRewriter.Puddle.MatcherSemantics
import all Veir.Interpreter.CTreeEquationLemma
import all Veir.Interpreter.EquationLemma
import all Veir.Interpreter.CTreeInterpreter
import all Veir.PatternRewriter.Puddle.CreationSemantics
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.Dominance.Basic

namespace Veir.Puddle

public section

/-- Root results are the only values temporarily bound by matching that need not dominate the root.
They stay confined to the root's distinguished result handle identifiers. -/
def Binding.MatcherScope (ctx : WfIRContext OpCode) (root : OperationPtr)
    (rootHandle : Handle OpCode .op) (rootResults : List Nat) (id : Nat) : Binding OpCode → Prop
  | .op operation => (operation = root ∧ id = rootHandle.id) ∨ operation.ProperlyDominates root ctx false
  | .value pointer => pointer.DominatesIp (.before root) ctx ∨
      (id ∈ rootResults ∧ pointer ∈ root.getResults! ctx.raw)
  | _ => True

/-- Pointer scope maintained while the runtime matcher walks backwards through SSA definitions. -/
def Assignment.MatcherScope (a : Assignment OpCode) (ctx : WfIRContext OpCode)
    (root : OperationPtr) (rootHandle : Handle OpCode .op) (rootResults : List Nat) : Prop :=
  ∀ (id : Nat) (binding : Binding OpCode), a.bindings[id]?.join = some binding →
    binding.MatcherScope ctx root rootHandle rootResults id

/-- Updating one scoped binding preserves the scope of the whole assignment. -/
theorem Assignment.MatcherScope.bind {a b : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {rootHandle : Handle OpCode .op} {rootResults : List Nat}
    {kind : HandleType OpCode} {handle : Handle OpCode kind} {binding : Binding OpCode}
    (ha : a.MatcherScope ctx root rootHandle rootResults) (h : a.bind handle binding = some b)
    (hb : binding.MatcherScope ctx root rootHandle rootResults handle.id) :
    b.MatcherScope ctx root rootHandle rootResults := by
  intro id existing he
  let other : Handle OpCode .type := ⟨id⟩
  change b.getBinding other = some existing at he
  by_cases heq : other.id = handle.id
  · have installed := Assignment.getBinding_of_bind h
    have hx : b.getBinding other = some binding := by
      simpa [Assignment.getBinding, heq] using installed
    have hbinding : binding = existing := Option.some.inj (hx.symm.trans he)
    change id = handle.id at heq
    simpa only [← hbinding, heq] using hb
  · rw [Assignment.getBinding_of_bind_of_ne other h heq] at he
    exact ha id existing he

/-- Batch result binding preserves scope when each possible new binding is scoped. -/
theorem Assignment.MatcherScope.bindValues {a b : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {rootHandle : Handle OpCode .op} {rootResults : List Nat}
    {handles : List (Handle OpCode .value)} {pointers : List ValuePtr}
    (ha : a.MatcherScope ctx root rootHandle rootResults)
    (h : a.bindValues handles pointers = some b)
    (hb : ∀ handle ∈ handles, ∀ pointer ∈ pointers,
      (Binding.value pointer).MatcherScope ctx root rootHandle rootResults handle.id) :
    b.MatcherScope ctx root rootHandle rootResults := by
  induction handles generalizing a pointers with
  | nil => cases pointers <;> simp_all [Assignment.bindValues]
  | cons handle handles ih =>
    cases pointers with
    | nil => simp [Assignment.bindValues] at h
    | cons pointer pointers =>
      simp only [Assignment.bindValues, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hh, ht⟩ := h
      exact ih (ha.bind hh (hb handle (by simp) pointer (by simp))) ht
        (fun h hh p hp => hb h (by simp [hh]) p (by simp [hp]))

/-- Metadata binding cannot introduce a pointer outside the matcher's scope. -/
theorem MetadataTuple.Shape.matcherScope_bind
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {a b : Assignment OpCode} {ctx : WfIRContext OpCode} {root : OperationPtr}
    {rootHandle : Handle OpCode .op} {rootResults : List Nat}
    (ha : a.MatcherScope ctx root rootHandle rootResults) (h : shape.bind a handles values = some b) :
    b.MatcherScope ctx root rootHandle rootResults := by
  induction shape generalizing a b with
  | unit => cases h; exact ha
  | atom atom => cases atom <;> exact ha.bind h trivial
  | cons head tail ih =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hh, ht⟩ := h
    apply ih _ _ (a := middle) ?_ ht
    cases head <;> exact ha.bind hh trivial

/-- An operation binding remembers whether it is the distinguished root or a proper SSA dominator. -/
theorem Assignment.MatcherScope.getOp {a : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {rootHandle : Handle OpCode .op} {rootResults : List Nat}
    (ha : a.MatcherScope ctx root rootHandle rootResults)
    {handle : Handle OpCode .op} {op : OperationPtr} (h : a.getOp handle = some op) :
    (op = root ∧ handle.id = rootHandle.id) ∨ op.ProperlyDominates root ctx false := by
  unfold Assignment.getOp at h
  split at h <;> try contradiction
  cases h
  exact ha handle.id _ (by assumption)

/-- Values outside the hidden root-result identifiers are in the pre-root SSA scope. -/
theorem Assignment.MatcherScope.getValue {a : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {rootHandle : Handle OpCode .op} {rootResults : List Nat}
    (ha : a.MatcherScope ctx root rootHandle rootResults)
    {handle : Handle OpCode .value} {pointer : ValuePtr} (h : a.getValue handle = some pointer)
    (hsafe : handle.id ∉ rootResults) : pointer.DominatesIp (.before root) ctx := by
  unfold Assignment.getValue at h
  split at h <;> try contradiction
  cases h
  have hs := ha handle.id _ (by assumption)
  rcases hs with hd | ⟨hbad, _⟩
  · exact hd
  · exact False.elim (hsafe hbad)

/-- Finding a non-root operation from a bound SSA result walks to a proper root dominator. -/
theorem Assignment.MatcherScope.findOp_properlyDominates
    {a : Assignment OpCode} {ctx : WfIRContext OpCode} {root : OperationPtr}
    {rootHandle opHandle : Handle OpCode .op} {rootResults : List Nat}
    {results : Array (Handle OpCode .value)} {op : OperationPtr}
    (ha : a.MatcherScope ctx root rootHandle rootResults) (hne : opHandle ≠ rootHandle)
    (hsafe : ∀ handle ∈ results, handle.id ∉ rootResults)
    (h : a.findOp opHandle results = some op) : op.ProperlyDominates root ctx false := by
  unfold Assignment.findOp at h
  split at h
  · rename_i matched hmatched
    cases h
    rcases ha.getOp hmatched with ⟨_, heq⟩ | hd
    · exact False.elim (hne (by cases opHandle; cases rootHandle; simpa using heq))
    · exact hd
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨value, hfind, h⟩ := h
    split at h <;> try contradiction
    rename_i result
    cases h
    obtain ⟨handle, hmem, hvalue⟩ := Array.exists_of_findSome?_eq_some hfind
    have hd := ha.getValue hvalue (hsafe handle hmem)
    cases hd with
    | OpResult hin hdom => cases hdom with | Before hp => exact hp

/-- Binding type metadata leaves all pointer scope facts intact. -/
theorem Assignment.MatcherScope.bindTypes {a b : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {rootHandle : Handle OpCode .op} {rootResults : List Nat}
    {handles : List (Handle OpCode .type)} {types : List TypeAttr}
    (ha : a.MatcherScope ctx root rootHandle rootResults) (h : a.bindTypes handles types = some b) :
    b.MatcherScope ctx root rootHandle rootResults := by
  induction handles generalizing a types with
  | nil => cases types <;> simp_all [Assignment.bindTypes]
  | cons handle handles ih =>
    cases types with
    | nil => simp [Assignment.bindTypes] at h
    | cons ty types =>
      simp only [Assignment.bindTypes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hh, ht⟩ := h
      exact ih (ha.bind hh trivial) ht

/-- A static result-output condition sufficient for runtime backward traversal. -/
def MatchDecl.ScopeCompatible (rootHandle : Handle OpCode .op) (rootResults : List Nat)
    (decl : MatchDecl OpCode) : Prop :=
  match decl with
  | .operation _ _ _ _ _ op results _ =>
    if op = rootHandle then ∀ handle ∈ results, handle.id ∈ rootResults
    else ∀ handle ∈ results, handle.id ∉ rootResults
  | _ => True

/-- Runtime matching walks only to SSA dominators, while keeping root results in their own slots. -/
theorem MatchDecl.matcherScope_of_run (decl : MatchDecl OpCode)
    {ctx : WfIRContext OpCode} {root : OperationPtr} {rootHandle : Handle OpCode .op}
    {rootResults : List Nat} {a b : Assignment OpCode}
    (ctxDom : ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx)
    (ha : a.MatcherScope ctx root rootHandle rootResults) (hbound : a.InBounds ctx.raw)
    (hroot : a.getOp rootHandle = some root) (hcompatible : decl.ScopeCompatible rootHandle rootResults)
    (h : decl.run ctx.raw a = some b) : b.MatcherScope ctx root rootHandle rootResults := by
  cases decl with
  | operation code operands types matcher property op results count =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨matched, hfind, a₁, h₁, a₂, h₂, u₁, _, u₂, _, a₃, h₃, u₃, _, a₄, h₄, u₄, _, h₅⟩ := h
    have hscope : (matched = root ∧ op = rootHandle) ∨ matched.ProperlyDominates root ctx false := by
      by_cases hop : op = rootHandle
      · left
        subst op
        simp only [Assignment.findOp, hroot] at hfind
        cases hfind
        exact ⟨rfl, rfl⟩
      · right
        exact ha.findOp_properlyDominates hop (by simpa [MatchDecl.ScopeCompatible, hop] using hcompatible) hfind
    have hdom : matched.Dominates root ctx false := by
      rcases hscope with ⟨rfl, _⟩ | hd
      · exact .inl rfl
      · exact .inr hd
    have hmatchedIn := hbound.findOp hfind
    have hmatchedRooted : matched.RootedAt irRoot ctx := by grind
    have hmatchedReachable : matched.HierarchicallyReachable ctx := by grind
    obtain ⟨matchedRegion, hmatchedRegion⟩ := hdom.exists_parentRegion rootRegion
    obtain ⟨matchedRegion', hmatchedLocal⟩ := hmatchedReachable.exists_locallyReachable hmatchedRegion
    have hnewop : (Binding.op matched).MatcherScope ctx root rootHandle rootResults op.id := by
      rcases hscope with ⟨rfl, rfl⟩ | hd
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr hd
    have ha₁ := ha.bind h₁ hnewop
    have ha₂ := ha₁.bindValues h₂ (by
      intro handle hhandle pointer hpointer
      rcases hscope with ⟨rfl, rfl⟩ | hd
      · right
        have hcompat : ∀ handle ∈ results, handle.id ∈ rootResults := by
          simpa [MatchDecl.ScopeCompatible] using hcompatible
        exact ⟨hcompat handle (by simpa using hhandle), by simpa using hpointer⟩
      · left
        have hp : pointer.InBounds ctx.raw := by grind
        obtain ⟨i, hi, heq⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp (by simpa using hpointer)
        subst pointer
        exact ValuePtr.DominatesIp.OpResult (by grind) (.Before hd))
    have ha₃ := ha₂.bind h₃ trivial
    have ha₄ := ha₃.bindTypes h₄
    apply ha₄.bindValues h₅
    intro handle hhandle pointer hpointer
    left
    have hoperand : pointer ∈ matched.getOperands! ctx.raw := by simpa using hpointer
    have hd : pointer.ProperlyDominates matched ctx :=
      ctxDom.operand_properlyDominates (by grind) hmatchedLocal hoperand
    apply ValuePtr.DominatesIp.before_iff.mpr
    refine ⟨by grind, ?_⟩
    rcases hscope with ⟨rfl, _⟩ | hm
    · exact hd
    · apply hd.trans_of_reachable (reachable := rootReachable)
      cases hm with
      | AncestorDominatedInRegion ancestor localDominance => exact .AncestorDominatedInRegion ancestor localDominance true
  | value type handle =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, hb⟩ := h
    exact ha.bind hb trivial
  | type matcher handle =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, _, _, _, heq⟩ := h
    cases heq
    exact ha
  | inspectOperation op inspect outputs =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, hb⟩ := h
    exact MetadataTuple.Shape.matcherScope_bind _ _ _ ha hb
  | applyNative inputs predicate =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, _, _, _, heq⟩ := h
    cases heq
    exact ha

/-- Static root/result freshness gives the local runtime scope contract. -/
theorem MatcherRootScope.scopeCompatible {prog : MatchProg OpCode α}
    {rootResults : Array (Handle OpCode .value)} (scope : MatcherRootScope prog rootResults)
    (decl : MatchDecl OpCode) (member : decl ∈ prog.decls) :
    decl.ScopeCompatible prog.rootHandle (rootResults.toList.map Handle.id) := by
  cases decl <;> try trivial
  rename_i code operands types matcher property op results count
  by_cases hop : op = prog.rootHandle
  · simpa [MatchDecl.ScopeCompatible, hop] using
      scope.rootOperation code operands types matcher property op results count member hop
  · simpa [MatchDecl.ScopeCompatible, hop] using
      (scope.nonrootOperation code operands types matcher property op results count member hop).2

/-- The complete runtime matcher preserves its backward SSA scope invariant. -/
theorem MatchProg.matcherScope_of_runDecls (decls : List (MatchDecl OpCode))
    {ctx : WfIRContext OpCode} {root : OperationPtr} {rootHandle : Handle OpCode .op}
    {rootResults : List Nat} {a b : Assignment OpCode}
    (ctxDom : ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx)
    (ha : a.MatcherScope ctx root rootHandle rootResults) (hbound : a.InBounds ctx.raw)
    (hroot : a.getOp rootHandle = some root)
    (hcompatible : ∀ decl ∈ decls, decl.ScopeCompatible rootHandle rootResults)
    (h : MatchProg.runDecls decls ctx.raw a = some b) :
    b.MatcherScope ctx root rootHandle rootResults := by
  induction decls generalizing a with
  | nil => cases h; exact ha
  | cons decl decls ih =>
    simp only [MatchProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hd, hr⟩ := h
    have hscope := decl.matcherScope_of_run ctxDom rootRooted rootRegion rootReachable
      ha hbound hroot (hcompatible decl (by simp)) hd
    have hbounds := decl.inBounds_of_run hbound hd
    have hext : middle.Extends a := by
      intro kind handle binding hb
      exact decl.getBinding_preserved_of_run hd hb
    exact ih hscope hbounds (hext.getOp hroot)
      (fun d hm => hcompatible d (by simp [hm])) hr

/-- Actual successful matching of a statically valid root layout only visits dominating SSA defs. -/
theorem MatchProg.matcherScope_of_run (prog : MatchProg OpCode α)
    {ctx : WfIRContext OpCode} {root : OperationPtr} {a : Assignment OpCode}
    {rootResults : Array (Handle OpCode .value)} (scope : MatcherRootScope prog rootResults)
    (ctxDom : ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (h : prog.run ctx.raw root = some a) :
    a.MatcherScope ctx root prog.rootHandle (rootResults.toList.map Handle.id) := by
  unfold MatchProg.run at h
  split at h <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  all_goals
    repeat first | obtain ⟨_, _, h⟩ := h
    rename_i initial hbind
    have hempty : (Assignment.empty OpCode prog.numHandles).MatcherScope ctx root prog.rootHandle
        (rootResults.toList.map Handle.id) := by
      intro id binding hb
      by_cases hi : id < prog.numHandles <;> simp [Assignment.empty, hi] at hb
    have hscope := hempty.bind hbind (Or.inl ⟨rfl, rfl⟩)
    have hbound := (Assignment.empty_inBounds prog.numHandles ctx.raw).bind hbind rootIn
    have hroot : Assignment.getOp _ prog.rootHandle = some root := Assignment.getOp_of_bindOp hbind
    exact MatchProg.matcherScope_of_runDecls _ ctxDom rootRooted rootRegion rootReachable
      hscope hbound hroot (fun d hm => scope.scopeCompatible d hm) h

/-- Static pattern validity discharges every root-result scope side condition automatically. -/
theorem CTree.Pattern.Valid.matcherScope_of_run {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx : WfIRContext OpCode} {root : OperationPtr}
    {a : Assignment OpCode} (ctxDom : ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (h : rule.matcher.run ctx.raw root = some a) :
    ∃ rootResults, MatcherRootScope rule.matcher rootResults ∧
      a.MatcherScope ctx root rule.matcher.rootHandle (rootResults.toList.map Handle.id) := by
  obtain ⟨results, scope⟩ := valid.matcher_rootScope
  exact ⟨results, scope, rule.matcher.matcherScope_of_run scope ctxDom rootRooted rootRegion rootReachable rootIn h⟩

private theorem lookup_list_of_array {α β : Type} (xs : Array α) (f : α → Option β)
    (ys : Array β) (h : xs.mapM f = some ys) : xs.toList.mapM f = some ys.toList := by
  simp only [Array.mapM_eq_mapM_toList] at h
  cases hm : xs.toList.mapM f with
  | none => simp [hm] at h
  | some values =>
    rw [hm] at h
    change some values.toArray = some ys at h
    cases h
    rfl

/-- Once a reachable execution supplies the historical SSA invariant, concrete matching produces
all per-declaration runtime equations automatically. Opcode memory preservation and successor
independence discharge the raw-interpreter obligations. -/
theorem CTree.Pattern.Valid.runtimeEquations_of_history {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx : WfIRContext OpCode} {root : OperationPtr}
    {assignment : Assignment OpCode} {state : InterpreterState ctx}
    (ctxDom : ctx.Dom irRoot) {verifyRoot : OperationPtr}
    (ctxVerified : ctx.Verified verifyRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (hmatch : rule.matcher.run ctx.raw root = some assignment)
    (defined : state.DefinesDominating (InsertPoint.before root) (by grind))
    (history : state.variables.CTreeEquationLemmaAt (InsertPoint.before root))
 :
    ∀ decl ∈ rule.matcher.decls, CTree.MatchDecl.RuntimeEquations ctx.raw rule.matcher.rootHandle
      state.variables.getVar? assignment decl := by
  obtain ⟨rootResults, rootScope, matchscope⟩ := valid.matcherScope_of_run
    ctxDom rootRooted rootRegion rootReachable rootIn hmatch
  have bounds := rule.matcher.inBounds_of_run rootIn hmatch
  intro decl member
  cases decl with
  | value ty handle =>
    intro pointer hpointer
    have hsafe := rootScope.leaf ty handle member
    have hdom := matchscope.getValue hpointer hsafe
    have hp : pointer.InBounds ctx.raw := bounds.getValue hpointer
    obtain ⟨value, hv⟩ := defined.exists_getVar_of_dominatesIp hp hdom
    exact ⟨value, hv, VariableState.getVar?_conforms hv⟩
  | operation code operands types matcher property handle results count =>
    intro matched hmatched hcode
    have hmatchedIn := bounds.getOp hmatched
    refine ⟨⟨ctx, matched, hmatchedIn,
      OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerified hmatchedIn,
      hcode, rfl, rfl, rfl⟩, ?_⟩
    have hsupported := valid.Supported.1 _ member
    by_cases hisroot : handle = rule.matcher.rootHandle
    · have hroot := rule.matcher.getOp_root_of_run hmatch
      rw [hisroot, hroot] at hmatched
      cases hmatched
      obtain ⟨localRegion, hlocal⟩ := rootReachable.exists_locallyReachable rootRegion
      obtain ⟨values, hvalues⟩ := defined.exists_getOperandValues_eq_some ctxDom (by grind) hlocal
      refine ⟨values.toList, ?_, ?_⟩
      · exact lookup_list_of_array _ _ _ hvalues
      · intro hne
        exact False.elim (hne hisroot)
    · have hnonroot := rootScope.nonrootOperation code operands types matcher property handle results count member hisroot
      have hproper : matched.ProperlyDominates root ctx false := by
        rcases matchscope.getOp hmatched with ⟨_, hid⟩ | hd
        · exact False.elim (hnonroot.1 hid)
        · exact hd
      subst code
      have hterm : HasOpInfo.isTerminator (matched.getOpType! ctx.raw) = false := by
        simpa only using hsupported
      obtain ⟨args, values, before, after, hargs, hvalues, hraw⟩ :=
        history matched hmatchedIn hterm (.Before hproper)
      refine ⟨args.toList, lookup_list_of_array _ _ _ hargs, ?_⟩
      intro _
      refine ⟨values.toList, lookup_list_of_array _ _ _ hvalues, before, after, ?_⟩
      have hsucc := Veir.CTree.interpretOp'_successors_irrelevant
        (matched.getOpType! ctx.raw) (matched.getProperties! ctx.raw (matched.getOpType! ctx.raw))
        (matched.getResultTypes! ctx.raw) args (matched.getSuccessors! ctx.raw) #[] before
        (matched.getRegions! ctx.raw) hterm
      rw [hsucc] at hraw
      simpa only [Interp.map, Array.toArray_toList, Veir.CTree.interpretOp'] using hraw
  | type => trivial
  | inspectOperation => trivial
  | applyNative => trivial

end

end Veir.Puddle
