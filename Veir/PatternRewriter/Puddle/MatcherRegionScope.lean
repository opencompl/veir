module

import all Veir.Verifier
public import Veir.PatternRewriter.Puddle.MatcherScope
import all Veir.PatternRewriter.Puddle.MatcherScope
import all Veir.Dominance.Basic
public import Veir.Interpreter.CTreeEntryInvariant
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.ExecutionBounds
import all Veir.Interpreter.CTreeEntryInvariant
import all Veir.PatternRewriter.Puddle.CreationSemantics
import all Veir.IR.Basic
namespace Veir.Puddle
public section

def Binding.RegionScope (ctx : WfIRContext OpCode) (region : RegionPtr) : Binding OpCode → Prop
  | .op operation => operation.getParentRegion! ctx.raw = some region
  | .value pointer => pointer.DefinedInRegion region ctx
  | _ => True

def Assignment.RegionScope (a : Assignment OpCode) (ctx : WfIRContext OpCode) (region : RegionPtr) : Prop :=
  ∀ (id : Nat) (binding : Binding OpCode), a.bindings[id]?.join = some binding → binding.RegionScope ctx region

/-- Updating one scoped binding preserves the scope of the whole assignment. -/
theorem Assignment.RegionScope.bind {a b : Assignment OpCode} {ctx : WfIRContext OpCode}
    {region : RegionPtr}
    {kind : HandleType OpCode} {handle : Handle OpCode kind} {binding : Binding OpCode}
    (ha : a.RegionScope ctx region) (h : a.bind handle binding = some b)
    (hb : binding.RegionScope ctx region) :
    b.RegionScope ctx region := by
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
theorem Assignment.RegionScope.bindValues {a b : Assignment OpCode} {ctx : WfIRContext OpCode}
    {region : RegionPtr}
    {handles : List (Handle OpCode .value)} {pointers : List ValuePtr}
    (ha : a.RegionScope ctx region)
    (h : a.bindValues handles pointers = some b)
    (hb : ∀ handle ∈ handles, ∀ pointer ∈ pointers,
      (Binding.value pointer).RegionScope ctx region) :
    b.RegionScope ctx region := by
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
theorem MetadataTuple.Shape.regionScope_bind
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {a b : Assignment OpCode} {ctx : WfIRContext OpCode} {region : RegionPtr}
    (ha : a.RegionScope ctx region) (h : shape.bind a handles values = some b) :
    b.RegionScope ctx region := by
  induction shape generalizing a b with
  | unit => cases h; exact ha
  | atom atom => cases atom <;> exact ha.bind h trivial
  | cons head tail ih =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hh, ht⟩ := h
    apply ih _ _ (a := middle) ?_ ht
    cases head <;> exact ha.bind hh trivial

/-- Binding type metadata leaves all pointer scope facts intact. -/
theorem Assignment.RegionScope.bindTypes {a b : Assignment OpCode} {ctx : WfIRContext OpCode}
    {region : RegionPtr}
    {handles : List (Handle OpCode .type)} {types : List TypeAttr}
    (ha : a.RegionScope ctx region) (h : a.bindTypes handles types = some b) :
    b.RegionScope ctx region := by
  induction handles generalizing a types with
  | nil => cases types <;> simp_all [Assignment.bindTypes]
  | cons handle handles ih =>
    cases types with
    | nil => simp [Assignment.bindTypes] at h
    | cons ty types =>
      simp only [Assignment.bindTypes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hh, ht⟩ := h
      exact ih (ha.bind hh trivial) ht


theorem Assignment.RegionScope.getOp {a : Assignment OpCode} {ctx : WfIRContext OpCode}
    {region : RegionPtr} (ha : a.RegionScope ctx region)
    {handle : Handle OpCode .op} {op : OperationPtr} (h : a.getOp handle = some op) :
    op.getParentRegion! ctx.raw = some region := by
  unfold Assignment.getOp at h
  split at h <;> try contradiction
  cases h
  exact ha handle.id _ (by assumption)

theorem Assignment.RegionScope.getValue {a : Assignment OpCode} {ctx : WfIRContext OpCode}
    {region : RegionPtr} (ha : a.RegionScope ctx region)
    {handle : Handle OpCode .value} {value : ValuePtr} (h : a.getValue handle = some value) :
    value.DefinedInRegion region ctx := by
  unfold Assignment.getValue at h
  split at h <;> try contradiction
  cases h
  exact ha handle.id _ (by assumption)

theorem Assignment.RegionScope.findOp {a : Assignment OpCode} {ctx : WfIRContext OpCode}
    {region : RegionPtr} (ha : a.RegionScope ctx region)
    {handle : Handle OpCode .op} {results : Array (Handle OpCode .value)} {op : OperationPtr}
    (h : a.findOp handle results = some op) : op.getParentRegion! ctx.raw = some region := by
  unfold Assignment.findOp at h
  split at h
  · rename_i found hfound
    cases h
    exact ha.getOp hfound
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨value, hfind, h⟩ := h
    split at h <;> try contradiction
    rename_i result
    cases h
    obtain ⟨valueHandle, _, hvalue⟩ := Array.exists_of_findSome?_eq_some hfind
    exact ha.getValue hvalue

/-- Operand isolation closes a matched operation's backward dependencies inside its region. -/
theorem MatchDecl.regionScope_of_run (decl : MatchDecl OpCode)
    {ctx : WfIRContext OpCode} {region : RegionPtr} {a b : Assignment OpCode}
    (closed : ∀ (op : OperationPtr), op.InBounds ctx.raw → op.getParentRegion! ctx.raw = some region →
      ∀ (value : ValuePtr), value ∈ op.getOperands! ctx.raw → value.DefinedInRegion region ctx)
    (ha : a.RegionScope ctx region) (bounds : a.InBounds ctx.raw)
    (h : decl.run ctx.raw a = some b) : b.RegionScope ctx region := by
  cases decl with
  | operation code operands types matcher property op results count =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨matched, hfind, a₁, h₁, a₂, h₂, u₁, _, u₂, _, a₃, h₃, u₃, _, a₄, h₄, u₄, _, h₅⟩ := h
    have localRegion := ha.findOp hfind
    have hop := bounds.findOp hfind
    have ha₁ := ha.bind h₁ localRegion
    have ha₂ := ha₁.bindValues h₂ (by
      intro handle hhandle pointer hpointer
      obtain ⟨i, hi, heq⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp (by simpa using hpointer)
      subst pointer
      simpa [Binding.RegionScope, ValuePtr.DefinedInRegion, OperationPtr.getResult] using localRegion)
    have ha₃ := ha₂.bind h₃ trivial
    have ha₄ := ha₃.bindTypes h₄
    apply ha₄.bindValues h₅
    intro handle hhandle pointer hpointer
    exact closed matched hop localRegion pointer (by simpa using hpointer)
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
    exact MetadataTuple.Shape.regionScope_bind _ _ _ ha hb
  | applyNative inputs predicate =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, _, _, _, heq⟩ := h
    cases heq
    exact ha

theorem MatchProg.regionScope_of_runDecls (decls : List (MatchDecl OpCode))
    {ctx : WfIRContext OpCode} {region : RegionPtr} {a b : Assignment OpCode}
    (closed : ∀ (op : OperationPtr), op.InBounds ctx.raw → op.getParentRegion! ctx.raw = some region →
      ∀ (value : ValuePtr), value ∈ op.getOperands! ctx.raw → value.DefinedInRegion region ctx)
    (ha : a.RegionScope ctx region) (bounds : a.InBounds ctx.raw)
    (h : MatchProg.runDecls decls ctx.raw a = some b) : b.RegionScope ctx region := by
  induction decls generalizing a with
  | nil => cases h; exact ha
  | cons decl decls ih =>
    simp only [MatchProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hd, hr⟩ := h
    exact ih (decl.regionScope_of_run closed ha bounds hd) (decl.inBounds_of_run bounds hd) hr

theorem MatchProg.regionScope_of_run (prog : MatchProg OpCode α)
    {ctx : WfIRContext OpCode} {region : RegionPtr} {root : OperationPtr} {a : Assignment OpCode}
    (closed : ∀ (op : OperationPtr), op.InBounds ctx.raw → op.getParentRegion! ctx.raw = some region →
      ∀ (value : ValuePtr), value ∈ op.getOperands! ctx.raw → value.DefinedInRegion region ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region) (rootIn : root.InBounds ctx.raw)
    (h : prog.run ctx.raw root = some a) : a.RegionScope ctx region := by
  unfold MatchProg.run at h
  split at h <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  all_goals
    repeat first | obtain ⟨_, _, h⟩ := h
    rename_i initial hbind
    have hempty : (Assignment.empty OpCode prog.numHandles).RegionScope ctx region := by
      intro id binding hb
      by_cases hi : id < prog.numHandles <;> simp [Assignment.empty, hi] at hb
    exact MatchProg.regionScope_of_runDecls _ closed (hempty.bind hbind rootRegion)
      ((Assignment.empty_inBounds prog.numHandles ctx.raw).bind hbind rootIn) h

theorem MatchDecl.regionScope_of_run_reachable (decl : MatchDecl OpCode)
    {ctx : WfIRContext OpCode} {region : RegionPtr} {a b : Assignment OpCode}
    (closed : ∀ (op : OperationPtr), op.InBounds ctx.raw → op.getParentRegion! ctx.raw = some region → op.HierarchicallyReachable ctx →
      ∀ (value : ValuePtr), value ∈ op.getOperands! ctx.raw → value.DefinedInRegion region ctx)
    (known : ∀ (handle : Handle OpCode .op) (op : OperationPtr), b.getOp handle = some op →
      op.HierarchicallyReachable ctx)
    (ha : a.RegionScope ctx region) (bounds : a.InBounds ctx.raw)
    (h : decl.run ctx.raw a = some b) : b.RegionScope ctx region := by
  cases decl with
  | operation code operands types matcher property op results count =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨matched, hfind, a₁, h₁, a₂, h₂, u₁, _, u₂, _, a₃, h₃, u₃, _, a₄, h₄, u₄, _, h₅⟩ := h
    have localRegion := ha.findOp hfind
    have hop := bounds.findOp hfind
    have ha₁ := ha.bind h₁ localRegion
    have ha₂ := ha₁.bindValues h₂ (by
      intro handle hhandle pointer hpointer
      obtain ⟨i, hi, heq⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp (by simpa using hpointer)
      subst pointer
      simpa [Binding.RegionScope, ValuePtr.DefinedInRegion, OperationPtr.getResult] using localRegion)
    have ha₃ := ha₂.bind h₃ trivial
    have ha₄ := ha₃.bindTypes h₄
    apply ha₄.bindValues h₅
    intro handle hhandle pointer hpointer
    have extension : b.Extends a₁ := by
      intro kind handle binding hb
      exact Assignment.getBinding_preserved_of_bindValues h₅
        (Assignment.getBinding_preserved_of_bindTypes h₄
          (Assignment.getBinding_preserved_of_bind h₃
            (Assignment.getBinding_preserved_of_bindValues h₂ hb)))
    have reached := known op matched (extension.getOp (Assignment.getOp_of_bindOp h₁))
    exact closed matched hop localRegion reached pointer (by simpa using hpointer)
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
    exact MetadataTuple.Shape.regionScope_bind _ _ _ ha hb
  | applyNative inputs predicate =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, _, _, _, heq⟩ := h
    cases heq
    exact ha

theorem MatchProg.regionScope_of_runDecls_reachable (decls : List (MatchDecl OpCode))
    {ctx : WfIRContext OpCode} {region : RegionPtr} {a b : Assignment OpCode}
    (closed : ∀ (op : OperationPtr), op.InBounds ctx.raw → op.getParentRegion! ctx.raw = some region →
      op.HierarchicallyReachable ctx → ∀ (value : ValuePtr), value ∈ op.getOperands! ctx.raw →
      value.DefinedInRegion region ctx)
    (known : ∀ (handle : Handle OpCode .op) (op : OperationPtr), b.getOp handle = some op →
      op.HierarchicallyReachable ctx)
    (ha : a.RegionScope ctx region) (bounds : a.InBounds ctx.raw)
    (h : MatchProg.runDecls decls ctx.raw a = some b) : b.RegionScope ctx region := by
  induction decls generalizing a with
  | nil => cases h; exact ha
  | cons decl decls ih =>
    simp only [MatchProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hd, hr⟩ := h
    have extension : b.Extends middle := by
      intro kind handle binding hb
      exact MatchProg.getBinding_preserved_of_runDecls _ hr hb
    exact ih (decl.regionScope_of_run_reachable closed
      (fun handle op hb => known handle op (extension.getOp hb)) ha bounds hd)
      (decl.inBounds_of_run bounds hd) hr

theorem MatchProg.regionScope_of_run_reachable (prog : MatchProg OpCode α)
    {ctx : WfIRContext OpCode} {region : RegionPtr} {root : OperationPtr} {a : Assignment OpCode}
    (closed : ∀ (op : OperationPtr), op.InBounds ctx.raw → op.getParentRegion! ctx.raw = some region →
      op.HierarchicallyReachable ctx → ∀ (value : ValuePtr), value ∈ op.getOperands! ctx.raw →
      value.DefinedInRegion region ctx)
    (known : ∀ (handle : Handle OpCode .op) (op : OperationPtr), a.getOp handle = some op →
      op.HierarchicallyReachable ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region) (rootIn : root.InBounds ctx.raw)
    (h : prog.run ctx.raw root = some a) : a.RegionScope ctx region := by
  unfold MatchProg.run at h
  split at h <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  all_goals
    repeat first | obtain ⟨_, _, h⟩ := h
    rename_i initial hbind
    have hempty : (Assignment.empty OpCode prog.numHandles).RegionScope ctx region := by
      intro id binding hb
      by_cases hi : id < prog.numHandles <;> simp [Assignment.empty, hi] at hb
    exact MatchProg.regionScope_of_runDecls_reachable _ closed known (hempty.bind hbind rootRegion)
      ((Assignment.empty_inBounds prog.numHandles ctx.raw).bind hbind rootIn) h

/-- Region-local execution invariants suffice for runtime matcher equations. -/
theorem CTree.Pattern.Valid.runtimeEquations_of_historyIn {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx : WfIRContext OpCode} {root : OperationPtr}
    {assignment : Assignment OpCode} {state : InterpreterState ctx}
    (ctxDom : ctx.Dom irRoot) {verifyRoot : OperationPtr}
    (ctxVerified : ctx.Verified verifyRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootReachable : root.HierarchicallyReachable ctx) (rootIn : root.InBounds ctx.raw)
    (hmatch : rule.matcher.run ctx.raw root = some assignment)
    (closed : ∀ (op : OperationPtr), op.InBounds ctx.raw → op.getParentRegion! ctx.raw = some region →
      ∀ (value : ValuePtr), value ∈ op.getOperands! ctx.raw → value.DefinedInRegion region ctx)
    (defined : state.DefinesDominatingIn region (InsertPoint.before root))
    (history : state.variables.CTreeEquationLemmaIn region (InsertPoint.before root))
 :
    ∀ decl ∈ rule.matcher.decls, CTree.MatchDecl.RuntimeEquations ctx.raw rule.matcher.rootHandle
      state.variables.getVar? assignment decl := by
  obtain ⟨rootResults, rootScope, matchscope⟩ := valid.matcherScope_of_run
    ctxDom rootRooted rootRegion rootReachable rootIn hmatch
  have bounds := rule.matcher.inBounds_of_run rootIn hmatch
  have localScope := rule.matcher.regionScope_of_run closed rootRegion rootIn hmatch
  intro decl member
  cases decl with
  | value ty handle =>
    intro pointer hpointer
    have hsafe := rootScope.leaf ty handle member
    have hdom := matchscope.getValue hpointer hsafe
    have hp : pointer.InBounds ctx.raw := bounds.getValue hpointer
    obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp (defined pointer hp (localScope.getValue hpointer) hdom)
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
      have hdefined : ∃ values, state.variables.getOperandValues root = some values := by
        simp only [VariableState.getOperandValues, Array.exists_mapM_option_eq_some_iff]
        intro i hi
        apply Option.isSome_iff_exists.mp
        apply defined _ (by grind) (closed root rootIn rootRegion _ (by grind))
        grind [WfIRContext.Dom.operand_dominatesIp_before]
      obtain ⟨values, hvalues⟩ := hdefined
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
      have inside : region.Ancestor matched ctx :=
        IRNode.Ancestor.of_getParentRegion!_eq_some (localScope.getOp hmatched)
      have heq := history matched hmatchedIn inside hterm (.Before hproper)
      obtain ⟨args, values, memory, after, hargs, hvalues, hraw⟩ := heq
      refine ⟨args.toList, lookup_list_of_array _ _ _ hargs, ?_⟩
      intro _
      refine ⟨values.toList, lookup_list_of_array _ _ _ hvalues, memory, after, ?_⟩
      have hsucc := Veir.CTree.interpretOp'_successors_irrelevant
        (matched.getOpType! ctx.raw) (matched.getProperties! ctx.raw (matched.getOpType! ctx.raw))
        (matched.getResultTypes! ctx.raw) args (matched.getSuccessors! ctx.raw) #[] memory
        (matched.getRegions! ctx.raw) hterm
      rw [hsucc] at hraw
      simpa only [Interp.map, Array.toArray_toList, Veir.CTree.interpretOp'] using hraw
  | type => trivial
  | inspectOperation => trivial
  | applyNative => trivial

end
end Veir.Puddle
