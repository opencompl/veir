module

public import Veir.PatternRewriter.Puddle.Execution
public import Veir.PatternRewriter.Semantics
public import Veir.PatternRewriter.Puddle.AssignmentLemmas
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Semantics
import all Veir.PatternRewriter.Basic

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Binding metadata preserves every populated runtime slot. -/
theorem MetadataTuple.Shape.getBinding_preserved_of_bind
    (shape : MetadataTuple.Shape OpInfo Handles) (handles : Handles) (values : shape.Values)
    {a b : Assignment OpInfo} {kind : HandleType OpInfo} {handle : Handle OpInfo kind}
    {existing : Binding OpInfo} (h : shape.bind a handles values = some b)
    (hold : a.getBinding handle = some existing) : b.getBinding handle = some existing := by
  induction shape generalizing a b with
  | unit => cases h; exact hold
  | atom atom =>
    cases atom <;> exact Assignment.getBinding_preserved_of_bind h hold
  | cons head tail ih =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hh, ht⟩ := h
    apply ih _ _ ht
    cases head <;> exact Assignment.getBinding_preserved_of_bind hh hold

/-- Successful match instructions preserve populated runtime slots. -/
theorem MatchDecl.getBinding_preserved_of_run (decl : MatchDecl OpInfo)
    {ctx : IRContext OpInfo} {a b : Assignment OpInfo}
    {kind : HandleType OpInfo} {handle : Handle OpInfo kind} {existing : Binding OpInfo}
    (h : decl.run ctx a = some b) (hold : a.getBinding handle = some existing) :
    b.getBinding handle = some existing := by
  cases decl with
  | operation code operands types matcher property op results hsize =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨matched, _, a₁, h₁, a₂, h₂, u₁, _, u₂, _, a₃, h₃, u₃, _, a₄, h₄, u₄, _, h₅⟩ := h
    exact Assignment.getBinding_preserved_of_bindValues h₅
      (Assignment.getBinding_preserved_of_bindTypes h₄
        (Assignment.getBinding_preserved_of_bind h₃
          (Assignment.getBinding_preserved_of_bindValues h₂
            (Assignment.getBinding_preserved_of_bind h₁ hold))))
  | value type value =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    exact Assignment.getBinding_preserved_of_bind h hold
  | type matcher type =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨_, _, _, _, heq⟩ := h
    cases heq
    exact hold
  | inspectOperation op inspect outputs =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h
    exact MetadataTuple.Shape.getBinding_preserved_of_bind _ _ _ h hold
  | applyNative inputs predicate =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨_, _, _, _, heq⟩ := h
    cases heq
    exact hold

/-- Successful match programs preserve populated runtime slots. -/
theorem MatchProg.getBinding_preserved_of_runDecls (decls : List (MatchDecl OpInfo))
    {ctx : IRContext OpInfo} {a b : Assignment OpInfo}
    {kind : HandleType OpInfo} {handle : Handle OpInfo kind} {existing : Binding OpInfo}
    (h : MatchProg.runDecls decls ctx a = some b) (hold : a.getBinding handle = some existing) :
    b.getBinding handle = some existing := by
  induction decls generalizing a with
  | nil => cases h; exact hold
  | cons decl decls ih =>
    simp only [MatchProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hd, hr⟩ := h
    exact ih hr (decl.getBinding_preserved_of_run hd hold)

/-- Successful matching retains the distinguished root operation binding. -/
theorem MatchProg.getOp_root_of_run (prog : MatchProg OpInfo α)
    {ctx : IRContext OpInfo} {root : OperationPtr} {a : Assignment OpInfo}
    (h : prog.run ctx root = some a) : a.getOp prog.rootHandle = some root := by
  unfold MatchProg.run at h
  split at h <;>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  all_goals
    repeat first | obtain ⟨_, _, h⟩ := h
    have hb := Assignment.getBinding_of_bind (by assumption :
      (Assignment.empty OpInfo prog.numHandles).bindOp prog.rootHandle root = some _)
    have hf := MatchProg.getBinding_preserved_of_runDecls _ h hb
    simp [Assignment.getOp, hf]

/-- A successful operation constraint identifies its operation and the inspected IR fields. -/
theorem MatchDecl.operation_fields_indexed_of_run
    {code : OpInfo} {operands : Array (Handle OpInfo .value)}
    {types : Array (Handle OpInfo .type)} {matcher : PropertyMatcher code}
    {property : Handle OpInfo (.prop code)} {op : Handle OpInfo .op}
    {results : Array (Handle OpInfo .value)} {hsize : results.size = types.size}
    {ctx : IRContext OpInfo} {a b : Assignment OpInfo}
    (h : (MatchDecl.operation code operands types matcher property op results hsize).run ctx a = some b) :
    ∃ matched : OperationPtr,
      b.getOp op = some matched ∧ matched.getOpType! ctx = code ∧
      matcher (matched.getProperties! ctx code) = true ∧
      b.getValues operands = some (matched.getOperands! ctx) ∧
      (∀ i (hi : i < types.size),
        b.getType types[i] = some (matched.getResultTypes! ctx)[i]!) ∧
      b.getProperty property = some (matched.getProperties! ctx code) ∧
      (∀ i (hi : i < results.size),
        b.getValue results[i] = some (matched.getResults! ctx)[i]!) := by
  simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨matched, _, a₁, h₁, a₂, h₂, u₁, hcode, u₂, hmatcher,
    a₃, h₃, u₃, _, a₄, h₄, u₄, _, h₅⟩ := h
  have hp₁ {kind} (handle : Handle OpInfo kind) (binding : Binding OpInfo)
      (hb : a₁.getBinding handle = some binding) : b.getBinding handle = some binding :=
    Assignment.getBinding_preserved_of_bindValues h₅
      (Assignment.getBinding_preserved_of_bindTypes h₄
        (Assignment.getBinding_preserved_of_bind h₃
          (Assignment.getBinding_preserved_of_bindValues h₂ hb)))
  have hp₂ {kind} (handle : Handle OpInfo kind) (binding : Binding OpInfo)
      (hb : a₂.getBinding handle = some binding) : b.getBinding handle = some binding :=
    Assignment.getBinding_preserved_of_bindValues h₅
      (Assignment.getBinding_preserved_of_bindTypes h₄
        (Assignment.getBinding_preserved_of_bind h₃ hb))
  have hp₄ {kind} (handle : Handle OpInfo kind) (binding : Binding OpInfo)
      (hb : a₄.getBinding handle = some binding) : b.getBinding handle = some binding :=
    Assignment.getBinding_preserved_of_bindValues h₅ hb
  refine ⟨matched, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Assignment.getOp, hp₁ _ _ (Assignment.getBinding_of_bind h₁)]
  · simpa [guard] using hcode
  · simpa [guard] using hmatcher
  · simpa using Assignment.getValues_of_bindValues h₅
  · intro i hi
    have hb : a₄.getType types[i] = some (matched.getResultTypes! ctx)[i]! := by
      simpa only [← Array.getElem_toList, Array.getElem!_toList] using
        Assignment.getType_of_bindTypes_getElem h₄ i (by simpa using hi)
    have hread : a₄.getBinding types[i] = some (.type (matched.getResultTypes! ctx)[i]!) := by
      cases hg : a₄.getBinding types[i] <;> simp [Assignment.getType, hg] at hb
      rename_i binding
      cases binding <;> simp_all only [Option.some.injEq, reduceCtorEq]
    simp [Assignment.getType, hp₄ _ _ hread]
  · have hb := Assignment.getBinding_preserved_of_bindValues h₅
      (Assignment.getBinding_preserved_of_bindTypes h₄ (Assignment.getBinding_of_bind h₃))
    simp [Assignment.getProperty, hb]
  · intro i hi
    have hb : a₂.getValue results[i] = some (matched.getResults! ctx)[i]! := by
      simpa only [← Array.getElem_toList, Array.getElem!_toList] using
        Assignment.getValue_of_bindValues_getElem h₂ i (by simpa using hi)
    have hread : a₂.getBinding results[i] = some (.value (matched.getResults! ctx)[i]!) := by
      cases hg : a₂.getBinding results[i] <;> simp [Assignment.getValue, hg] at hb
      rename_i binding
      cases binding <;> simp_all only [Option.some.injEq, reduceCtorEq]
    simp [Assignment.getValue, hp₂ _ _ hread]

/-- Successful operation matching recovers all constrained arrays and metadata. -/
theorem MatchDecl.operation_fields_of_run
    {code : OpInfo} {operands : Array (Handle OpInfo .value)}
    {types : Array (Handle OpInfo .type)} {matcher : PropertyMatcher code}
    {property : Handle OpInfo (.prop code)} {op : Handle OpInfo .op}
    {results : Array (Handle OpInfo .value)} {hsize : results.size = types.size}
    {ctx : IRContext OpInfo} {a b : Assignment OpInfo}
    (h : (MatchDecl.operation code operands types matcher property op results hsize).run ctx a = some b) :
    ∃ matched : OperationPtr,
      b.getOp op = some matched ∧ matched.getOpType! ctx = code ∧
      matcher (matched.getProperties! ctx code) = true ∧
      b.getValues operands = some (matched.getOperands! ctx) ∧
      b.getTypes types = some (matched.getResultTypes! ctx) ∧
      b.getProperty property = some (matched.getProperties! ctx code) ∧
      b.getValues results = some (matched.getResults! ctx) := by
  obtain ⟨matched, hop, hcode, hmatcher, hoperands, htypes, hproperty, hresults⟩ :=
    MatchDecl.operation_fields_indexed_of_run h
  have hsizes : types.size = (matched.getResultTypes! ctx).size ∧
      results.size = (matched.getResults! ctx).size := by
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨actual, _, a₁, h₁, a₂, h₂, u₁, _, u₂, _,
      a₃, h₃, u₃, _, a₄, h₄, u₄, _, h₅⟩ := h
    have hactual : actual = matched := by
      have hkeep := Assignment.getBinding_preserved_of_bindValues h₅
        (Assignment.getBinding_preserved_of_bindTypes h₄
          (Assignment.getBinding_preserved_of_bind h₃
            (Assignment.getBinding_preserved_of_bindValues h₂
              (Assignment.getBinding_of_bind h₁))))
      have hread : b.getOp op = some actual := by simp [Assignment.getOp, hkeep]
      exact Option.some.inj (hread.symm.trans hop)
    subst actual
    exact ⟨by simpa using Assignment.bindTypes_length h₄,
      by simpa using Assignment.bindValues_length h₂⟩
  refine ⟨matched, hop, hcode, hmatcher, hoperands, ?_, hproperty, ?_⟩
  · exact (Array.mapM_eq_some_iff_of_size_eq hsizes.1).mpr fun i hi => by
      simpa only [getElem!_pos types i hi] using htypes i hi
  · exact (Array.mapM_eq_some_iff_of_size_eq hsizes.2).mpr fun i hi => by
      simpa only [getElem!_pos results i hi] using hresults i hi

/-- Successful creation only extends the context with unattached operations. -/
theorem CreateDecl.run_withCreatedOps (decl : CreateDecl OpInfo)
    (assignment : Assignment OpInfo) (ctx newCtx : WfIRContext OpInfo)
    (newOps : Array OperationPtr) (newAssignment : Assignment OpInfo)
    (h : decl.run assignment ctx = some (newCtx, newOps, newAssignment)) :
    WfIRContext.WithCreatedOps ctx newCtx := by
  cases decl with
  | operation code operandHandles typeHandles propertyHandle opHandle resultHandles =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨operands, hop, types, hty, properties, hprop, u, hguard, h⟩ := h
    split at h
    · rename_i hin
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨middleCtx, newOp⟩, hcreate, bound, hbound, final, hfinal, heq⟩ := h
      cases heq
      exact .CreatedOp (newOp := newOp) _ _ _ (.Nil _)
        ⟨code, types, operands, #[], #[], properties, _, _, _, _, hcreate⟩
    · contradiction
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨bound, _, heq⟩ := h
    cases heq
    exact .Nil _
  | property code value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨bound, _, heq⟩ := h
    cases heq
    exact .Nil _
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨values, _, outputValues, _, bound, _, heq⟩ := h
    cases heq
    exact .Nil _

/-- Concatenating sequences of unattached creations concatenates their context extensions. -/
private theorem withCreatedOps_trans {ctx₁ ctx₂ ctx₃ : WfIRContext OpInfo}
    (h₁ : Veir.WfIRContext.WithCreatedOps ctx₁ ctx₂)
    (h₂ : Veir.WfIRContext.WithCreatedOps ctx₂ ctx₃) :
    Veir.WfIRContext.WithCreatedOps ctx₁ ctx₃ := by
  induction h₂ with
  | Nil => exact h₁
  | CreatedOp _ _ _ _ h ih => exact .CreatedOp _ _ _ (ih h₁) h

/-- Successful execution of a creation list only adds unattached operations. -/
theorem CreateProg.runDecls_withCreatedOps (decls : List (CreateDecl OpInfo))
    (assignment : Assignment OpInfo) (ctx newCtx : WfIRContext OpInfo)
    (newOps : Array OperationPtr) (newAssignment : Assignment OpInfo)
    (h : CreateProg.runDecls decls ctx assignment = some (newCtx, newOps, newAssignment)) :
    Veir.WfIRContext.WithCreatedOps ctx newCtx := by
  induction decls generalizing ctx assignment newOps with
  | nil => simp only [CreateProg.runDecls, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact .Nil _
  | cons decl decls ih =>
    simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨middleCtx, created, middleAssignment⟩, hdecl, rest⟩ := h
    obtain ⟨⟨finalCtx, restOps, finalAssignment⟩, hrest, hfinal⟩ := rest
    cases hfinal
    exact withCreatedOps_trans
      (CreateDecl.run_withCreatedOps _ _ _ _ _ _ hdecl)
      (ih _ _ _ hrest)

/-- Successful execution of a creation program only adds unattached operations. -/
theorem CreateProg.run_withCreatedOps (prog : CreateProg OpInfo α)
    (assignment : Assignment OpInfo) (ctx newCtx : WfIRContext OpInfo)
    (newOps : Array OperationPtr) (newAssignment : Assignment OpInfo)
    (h : prog.run assignment ctx = some (newCtx, newOps, newAssignment)) :
    WfIRContext.WithCreatedOps ctx newCtx :=
  CreateProg.runDecls_withCreatedOps _ _ _ _ _ _ h

/-- Rejected Puddle matches leave the context unchanged. -/
theorem Pattern.interpret_returnsCtxNoChanges (rule : Pattern OpCode) :
    LocalRewritePattern.ReturnsCtxNoChanges rule.interpret := by
  intro ctx op newCtx h
  unfold Pattern.interpret at h
  split at h
  · cases h; rfl
  · split at h
    · contradiction
    · split at h <;> simp_all

/-- Successful Puddle interpretation only creates unattached operations. -/
theorem Pattern.interpret_returnCtxChanges (rule : Pattern OpCode) :
    LocalRewritePattern.ReturnCtxChanges rule.interpret := by
  intro ctx op newCtx newOps newValues h
  unfold Pattern.interpret at h
  split at h
  · simp_all
  · split at h
    · contradiction
    · rename_i matched _ createdCtx createdOps finalAssignment hcreate
      split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        exact CreateProg.run_withCreatedOps _ _ _ _ _ _ hcreate

/-- Compiling a rejected match returns the original rewriter with its action flag cleared. -/
theorem Pattern.compile_run_of_no_match (rule : Pattern OpInfo)
    (rewriter : PatternRewriter OpInfo) (op : OperationPtr)
    (opIn : op.InBounds rewriter.ctx.raw)
    (h : rule.matcher.run rewriter.ctx.raw op = none) :
    rule.compile.run rewriter op opIn =
      some { rewriter with hasDoneAction := false } := by
  simp [Pattern.compile, RewritePattern.fromLocalRewrite, Pattern.interpret, h]

end

end Veir.Puddle
