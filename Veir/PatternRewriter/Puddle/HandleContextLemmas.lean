module

public import Veir.PatternRewriter.Puddle.MatcherSemantics
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.PatternRewriter.Puddle.MatcherSemantics

namespace Veir.Puddle

public section

theorem HandleContext.lookup_preserved_of_insertManyFresh
    {before after : HandleContext} {kind : HandleType OpCode}
    (handles : List (Handle OpCode kind)) {id : Nat} {oldKind : HandleType OpCode}
    (collected : before.insertManyFresh handles = some after)
    (bound : before.lookup id = some oldKind) : after.lookup id = some oldKind := by
  induction handles generalizing before with
  | nil =>
    simp only [HandleContext.insertManyFresh, List.foldlM_nil, Option.pure_def,
      Option.some.injEq] at collected
    subst after; exact bound
  | cons handle handles ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hfirst, hrest⟩ := collected
    exact ih hrest (HandleContext.lookup_preserved_of_insertFresh hfirst bound)

theorem HandleContext.lookup_of_insertManyFresh
    {before after : HandleContext} {kind : HandleType OpCode}
    (handles : List (Handle OpCode kind)) (collected : before.insertManyFresh handles = some after)
    {handle : Handle OpCode kind} (member : handle ∈ handles) : after.lookup handle.id = some kind := by
  induction handles generalizing before with
  | nil => simp at member
  | cons first rest ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hfirst, hrest⟩ := collected
    rcases List.mem_cons.mp member with heq | hmem
    · subst handle
      exact HandleContext.lookup_preserved_of_insertManyFresh _ hrest
        (HandleContext.lookup_of_insertFresh hfirst)
    · exact ih hrest hmem

theorem HandleContext.lookup_eq_none_of_insertFresh
    {before after : HandleContext} {kind : HandleType OpCode} {handle : Handle OpCode kind}
    (collected : before.insertFresh handle = some after) : before.lookup handle.id = none := by
  unfold HandleContext.insertFresh at collected
  split at collected
  · assumption
  · contradiction

theorem HandleContext.lookup_eq_none_of_insertManyFresh
    {before after : HandleContext} {kind : HandleType OpCode}
    (handles : List (Handle OpCode kind)) (collected : before.insertManyFresh handles = some after)
    {handle : Handle OpCode kind} (member : handle ∈ handles) : before.lookup handle.id = none := by
  induction handles generalizing before with
  | nil => simp at member
  | cons first rest ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hfirst, hrest⟩ := collected
    rcases List.mem_cons.mp member with heq | hmem
    · subst handle; exact HandleContext.lookup_eq_none_of_insertFresh hfirst
    · have hm := ih hrest hmem
      cases hb : before.lookup handle.id with
      | none => rfl
      | some oldKind =>
        have hk := HandleContext.lookup_preserved_of_insertFresh hfirst hb
        rw [hm] at hk
        contradiction

theorem MetadataTuple.Shape.lookup_preserved_of_insertFreshBindings
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles)
    {before after : HandleContext} {id : Nat} {kind : HandleType OpCode}
    (collected : shape.insertFreshBindings before handles = some after)
    (bound : before.lookup id = some kind) : after.lookup id = some kind := by
  induction shape generalizing before with
  | unit => cases collected; exact bound
  | atom atom => cases atom <;> exact HandleContext.lookup_preserved_of_insertFresh collected bound
  | cons atom tail ih =>
    cases atom <;>
      simp only [MetadataTuple.Shape.insertFreshBindings, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at collected
    all_goals
      obtain ⟨middle, hfirst, hrest⟩ := collected
      exact ih _ hrest (HandleContext.lookup_preserved_of_insertFresh hfirst bound)

theorem MatchDecl.lookup_preserved_of_collectBindings
    (decl : MatchDecl OpCode) {before after : HandleContext} {id : Nat} {kind : HandleType OpCode}
    (collected : decl.collectBindings before = some after)
    (bound : before.lookup id = some kind) : after.lookup id = some kind := by
  cases decl with
  | type matcher handle => exact HandleContext.lookup_preserved_of_insertFresh collected bound
  | value typeHandle handle =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, _, hbind⟩ := collected
    exact HandleContext.lookup_preserved_of_insertFresh hbind bound
  | operation code operands types matcher property op results count =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, _, u', _, middle₁, hresults, middle₂, hproperty, hop⟩ := collected
    exact HandleContext.lookup_preserved_of_insertFresh hop
      (HandleContext.lookup_preserved_of_insertFresh hproperty
        (HandleContext.lookup_preserved_of_insertManyFresh _ hresults bound))
  | inspectOperation op inspect outputs =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, _, hbind⟩ := collected
    exact MetadataTuple.Shape.lookup_preserved_of_insertFreshBindings _ _ hbind bound
  | applyNative inputs predicate =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at collected
    obtain ⟨u, _, rfl⟩ := collected
    exact bound

theorem MatchProg.lookup_preserved_of_collectDeclBindings
    (decls : List (MatchDecl OpCode)) {before after : HandleContext} {id : Nat} {kind : HandleType OpCode}
    (collected : MatchProg.collectDeclBindings decls before = some after)
    (bound : before.lookup id = some kind) : after.lookup id = some kind := by
  induction decls generalizing before with
  | nil => cases collected; exact bound
  | cons decl decls ih =>
    simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hfirst, hrest⟩ := collected
    exact ih hrest (decl.lookup_preserved_of_collectBindings hfirst bound)

theorem HandleContext.lookup_of_require {defined : HandleContext} {kind : HandleType OpCode}
    {handle : Handle OpCode kind} (required : defined.require handle = true) :
    defined.lookup handle.id = some kind := by
  simp only [HandleContext.require, decide_eq_true_eq] at required
  exact required.1

theorem HandleContext.not_mem_of_require_missing {defined : HandleContext} {ignored : List Nat}
    {kind : HandleType OpCode} {handle : Handle OpCode kind}
    (required : defined.require handle = true)
    (missing : ∀ id ∈ ignored, defined.lookup id = none) : handle.id ∉ ignored := by
  intro hmem
  have hk := HandleContext.lookup_of_require required
  rw [missing _ hmem] at hk
  contradiction

theorem MetadataTuple.Shape.avoids_of_require_missing
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles)
    {defined : HandleContext} {ignored : List Nat}
    (required : shape.requireBindings defined handles = true)
    (missing : ∀ id ∈ ignored, defined.lookup id = none) : shape.Avoids ignored handles := by
  induction shape with
  | unit => trivial
  | atom atom => cases atom <;> exact HandleContext.not_mem_of_require_missing required missing
  | cons atom tail ih =>
    cases atom <;> simp only [MetadataTuple.Shape.requireBindings, Bool.and_eq_true] at required
    all_goals exact ⟨HandleContext.not_mem_of_require_missing required.1 missing, ih _ required.2⟩

private theorem require_of_guard {b : Bool} {u : Unit}
    (h : (guard (b = true) : Option Unit) = some u) : b = true := by
  cases b <;> simp_all [guard]

theorem CTree.MatchDecl.avoids_of_collectBindings_missing
    (decl : MatchDecl OpCode) {before after : HandleContext} {ignored : List Nat}
    (collected : decl.collectBindings before = some after)
    (missing : ∀ id ∈ ignored, before.lookup id = none) : CTree.MatchDecl.Avoids ignored decl := by
  cases decl with
  | type matcher handle => trivial
  | value ty handle =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, hrequired, _⟩ := collected
    exact HandleContext.not_mem_of_require_missing (require_of_guard hrequired) missing
  | operation code operands types matcher property op results count =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, hv, u', ht, _⟩ := collected
    have hvalues := require_of_guard hv
    have htypes := require_of_guard ht
    simp only [HandleContext.requireMany, List.all_eq_true] at hvalues htypes
    exact ⟨fun handle hm => HandleContext.not_mem_of_require_missing
        (hvalues _ (by simpa using hm)) missing,
      fun handle hm => HandleContext.not_mem_of_require_missing
        (htypes _ (by simpa using hm)) missing⟩
  | inspectOperation op inspect outputs => trivial
  | applyNative inputs predicate =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, hrequired, _⟩ := collected
    exact MetadataTuple.Shape.avoids_of_require_missing _ _ (require_of_guard hrequired) missing

theorem MatchProg.avoids_of_collectDeclBindings_missing
    (decls : List (MatchDecl OpCode)) {before after : HandleContext} {ignored : List Nat}
    (collected : MatchProg.collectDeclBindings decls before = some after)
    (missing : ∀ id ∈ ignored, after.lookup id = none) :
    ∀ decl ∈ decls, CTree.MatchDecl.Avoids ignored decl := by
  induction decls generalizing before with
  | nil => simp
  | cons first rest ih =>
    simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hfirst, hrest⟩ := collected
    have hmiddle : ∀ id ∈ ignored, middle.lookup id = none := by
      intro id hm
      cases hb : middle.lookup id with
      | none => rfl
      | some kind =>
        have ha := MatchProg.lookup_preserved_of_collectDeclBindings _ hrest hb
        rw [missing _ hm] at ha
        contradiction
    have hbefore : ∀ id ∈ ignored, before.lookup id = none := by
      intro id hm
      cases hb : before.lookup id with
      | none => rfl
      | some kind =>
        have ha := first.lookup_preserved_of_collectBindings hfirst hb
        rw [hmiddle _ hm] at ha
        contradiction
    intro decl hd
    rcases List.mem_cons.mp hd with heq | hmem
    · subst decl; exact CTree.MatchDecl.avoids_of_collectBindings_missing _ hfirst hbefore
    · exact ih hrest decl hmem


theorem HandleContext.not_mem_of_require_valueKind {defined : HandleContext} {ignored : List Nat}
    {kind : HandleType OpCode} {handle : Handle OpCode kind}
    (required : defined.require handle = true) (notValue : kind ≠ .value)
    (known : ∀ id ∈ ignored, defined.lookup id = some .value) : handle.id ∉ ignored := by
  intro hmem
  have hk := HandleContext.lookup_of_require required
  rw [known _ hmem] at hk
  exact notValue (Option.some.inj hk).symm

theorem MetadataTuple.Shape.avoids_of_require_valueKind
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles)
    {defined : HandleContext} {ignored : List Nat}
    (required : shape.requireBindings defined handles = true)
    (known : ∀ id ∈ ignored, defined.lookup id = some .value) : shape.Avoids ignored handles := by
  induction shape with
  | unit => trivial
  | atom atom =>
    cases atom <;> exact HandleContext.not_mem_of_require_valueKind required (by intro h; cases h) known
  | cons atom tail ih =>
    cases atom <;> simp only [MetadataTuple.Shape.requireBindings, Bool.and_eq_true] at required
    all_goals exact ⟨HandleContext.not_mem_of_require_valueKind required.1
      (by intro h; cases h) known, ih _ required.2⟩

@[expose]
def MatchDecl.isGuard (decl : MatchDecl OpCode) : Bool :=
  match decl with
  | @MatchDecl.inspectOperation _ _ _ _ _ _ _ => true
  | @MatchDecl.applyNative _ _ _ _ _ _ => true
  | _ => false

theorem CTree.MatchDecl.avoids_of_collectBindings_guard
    (decl : MatchDecl OpCode) {before after : HandleContext} {ignored : List Nat}
    (collected : decl.collectBindings before = some after) (isGuard : decl.isGuard = true)
    (known : ∀ id ∈ ignored, before.lookup id = some .value) : CTree.MatchDecl.Avoids ignored decl := by
  cases decl with
  | type matcher handle => simp [MatchDecl.isGuard] at isGuard
  | value ty handle => simp [MatchDecl.isGuard] at isGuard
  | operation code operands types matcher property op results count => simp [MatchDecl.isGuard] at isGuard
  | inspectOperation op inspect outputs => trivial
  | applyNative inputs predicate =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, hrequired, _⟩ := collected
    exact MetadataTuple.Shape.avoids_of_require_valueKind _ _ (require_of_guard hrequired) known

theorem MatchProg.avoids_of_collectDeclBindings_guards
    (decls : List (MatchDecl OpCode)) {before after : HandleContext} {ignored : List Nat}
    (collected : MatchProg.collectDeclBindings decls before = some after)
    (guards : ∀ decl ∈ decls, decl.isGuard = true)
    (known : ∀ id ∈ ignored, before.lookup id = some .value) :
    ∀ decl ∈ decls, CTree.MatchDecl.Avoids ignored decl := by
  induction decls generalizing before with
  | nil => simp
  | cons first rest ih =>
    simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hfirst, hrest⟩ := collected
    have hmiddle : ∀ id ∈ ignored, middle.lookup id = some .value := by
      intro id hm; exact first.lookup_preserved_of_collectBindings hfirst (known id hm)
    intro decl hd
    rcases List.mem_cons.mp hd with heq | hmem
    · subst decl; exact CTree.MatchDecl.avoids_of_collectBindings_guard _ hfirst (guards first (by simp)) known
    · exact ih hrest (fun decl hd => guards decl (by simp [hd])) hmiddle decl hmem

theorem MatchProg.collectDeclBindings_append (first rest : List (MatchDecl OpCode))
    (defined : HandleContext) :
    MatchProg.collectDeclBindings (first ++ rest) defined =
      (MatchProg.collectDeclBindings first defined >>= MatchProg.collectDeclBindings rest) := by
  induction first generalizing defined with
  | nil => rfl
  | cons decl decls ih => simp [MatchProg.collectDeclBindings, ih, Option.bind_assoc]

theorem MatchProg.bindingDecls_root_last {prog : MatchProg OpCode α}
    {code operands types matcher property op results count rest}
    (h : prog.decls = .operation code operands types matcher property op results count :: rest) :
    ∃ first guards, prog.bindingDecls = first ++
      .operation code operands types matcher property op results count :: guards ∧
      ∀ decl ∈ guards, decl.isGuard = true := by
  let isStructural : MatchDecl OpCode → Bool := fun
    | @MatchDecl.applyNative _ _ _ _ _ _ => false
    | @MatchDecl.inspectOperation _ _ _ _ _ _ _ => false
    | _ => true
  refine ⟨(rest.partition isStructural).1.reverse, (rest.partition isStructural).2, ?_, ?_⟩
  · simp [MatchProg.bindingDecls, h, List.partition_eq_filter_filter, isStructural]
    congr 4 <;> funext decl <;> cases decl <;> rfl
  · intro decl hd
    simp [List.partition_eq_filter_filter, isStructural] at hd
    cases decl <;> simp_all [MatchDecl.isGuard]


theorem MatchDecl.operation_lookup_of_collectBindings
    {code operands types matcher property op results count} {before after : HandleContext}
    (collected : (MatchDecl.operation code operands types matcher property op results count).collectBindings before = some after) :
    after.lookup op.id = some .op := by
  simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
  obtain ⟨u, _, u', _, middle₁, _, middle₂, _, hop⟩ := collected
  exact HandleContext.lookup_of_insertFresh hop

theorem MatchDecl.operation_fresh_of_collectBindings
    {code operands types matcher property op results count} {before after : HandleContext}
    (collected : (MatchDecl.operation code operands types matcher property op results count).collectBindings before = some after) :
    before.lookup op.id = none := by
  cases hb : before.lookup op.id with
  | none => rfl
  | some kind =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, _, u', _, middle₁, hresults, middle₂, hproperty, hop⟩ := collected
    have hk := HandleContext.lookup_preserved_of_insertFresh hproperty
      (HandleContext.lookup_preserved_of_insertManyFresh _ hresults hb)
    rw [HandleContext.lookup_eq_none_of_insertFresh hop] at hk
    contradiction

theorem MatchProg.operation_lookup_of_collectDeclBindings
    (decls : List (MatchDecl OpCode)) {before after : HandleContext}
    {code operands types matcher property op results count}
    (collected : MatchProg.collectDeclBindings decls before = some after)
    (member : MatchDecl.operation code operands types matcher property op results count ∈ decls) :
    after.lookup op.id = some .op := by
  induction decls generalizing before with
  | nil => simp at member
  | cons first rest ih =>
    simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hfirst, hrest⟩ := collected
    rcases List.mem_cons.mp member with heq | hmem
    · subst first
      exact MatchProg.lookup_preserved_of_collectDeclBindings _ hrest
        (MatchDecl.operation_lookup_of_collectBindings hfirst)
    · exact ih hrest hmem

theorem MatchProg.avoids_rootResults_of_collectDeclBindings {prog : MatchProg OpCode α}
    {code operands types matcher property results count rest} {after : HandleContext}
    (rootFirst : prog.decls = .operation code operands types matcher property prog.rootHandle results count :: rest)
    (collected : MatchProg.collectDeclBindings prog.bindingDecls .empty = some after) :
    ∀ decl ∈ prog.bindingDecls,
      CTree.MatchDecl.Avoids (results.toList.map Handle.id) decl := by
  obtain ⟨first, guards, horder, hguards⟩ := MatchProg.bindingDecls_root_last rootFirst
  rw [horder, MatchProg.collectDeclBindings_append] at collected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
  obtain ⟨beforeRoot, hfirst, htail⟩ := collected
  simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at htail
  obtain ⟨afterRoot, hroot, hguardsCollected⟩ := htail
  have hrootOriginal := hroot
  simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at hroot
  obtain ⟨u, _, u', _, middle₁, hresults, middle₂, hproperty, hop⟩ := hroot
  have hmissing : ∀ id ∈ results.toList.map Handle.id, beforeRoot.lookup id = none := by
    intro id hm
    obtain ⟨handle, hh, rfl⟩ := List.mem_map.mp hm
    exact HandleContext.lookup_eq_none_of_insertManyFresh _ hresults hh
  have hknown : ∀ id ∈ results.toList.map Handle.id, afterRoot.lookup id = some .value := by
    intro id hm
    obtain ⟨handle, hh, rfl⟩ := List.mem_map.mp hm
    exact HandleContext.lookup_preserved_of_insertFresh hop
      (HandleContext.lookup_preserved_of_insertFresh hproperty
        (HandleContext.lookup_of_insertManyFresh _ hresults hh))
  intro decl hd
  rw [horder] at hd
  rcases List.mem_append.mp hd with hbefore | htail
  · exact MatchProg.avoids_of_collectDeclBindings_missing first hfirst hmissing decl hbefore
  · rcases List.mem_cons.mp htail with heq | hafter
    · subst decl
      exact CTree.MatchDecl.avoids_of_collectBindings_missing _ hrootOriginal hmissing
    · exact MatchProg.avoids_of_collectDeclBindings_guards guards hguardsCollected hguards hknown decl hafter


theorem MatchProg.rootResults_coverage_of_collectDeclBindings {prog : MatchProg OpCode α}
    {code operands types matcher property results count rest} {after : HandleContext}
    (rootFirst : prog.decls = .operation code operands types matcher property prog.rootHandle results count :: rest)
    (collected : MatchProg.collectDeclBindings prog.bindingDecls .empty = some after) :
    ∀ decl ∈ prog.bindingDecls,
      ∀ code' operands' types' matcher' property' op' results' count',
      decl = .operation code' operands' types' matcher' property' op' results' count' →
      op' = prog.rootHandle → ∀ handle ∈ results', handle.id ∈ results.toList.map Handle.id := by
  obtain ⟨first, guards, horder, hguards⟩ := MatchProg.bindingDecls_root_last rootFirst
  rw [horder, MatchProg.collectDeclBindings_append] at collected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
  obtain ⟨beforeRoot, hfirst, htail⟩ := collected
  simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at htail
  obtain ⟨afterRoot, hroot, hguardsCollected⟩ := htail
  have hmissing := MatchDecl.operation_fresh_of_collectBindings hroot
  intro decl hd code' operands' types' matcher' property' op' results' count' heq hop handle hm
  subst decl
  subst op'
  rw [horder] at hd
  rcases List.mem_append.mp hd with hbefore | htail
  · have hk := MatchProg.operation_lookup_of_collectDeclBindings first hfirst hbefore
    rw [hmissing] at hk
    contradiction
  · rcases List.mem_cons.mp htail with heq | hafter
    · cases heq
      exact List.mem_map.mpr ⟨handle, by simpa using hm, rfl⟩
    · have hg := hguards _ hafter
      simp [MatchDecl.isGuard] at hg


theorem CTree.MatchProg.realizes_of_run_of_collectBindings {prog : MatchProg OpCode α}
    {ctx : IRContext OpCode} {root : OperationPtr} {concrete : Assignment OpCode}
    (resolve : ValuePtr → Option RuntimeValue) (run : prog.run ctx root = some concrete)
    (collected : prog.collectBindings.isSome = true)
    (equations : ∀ decl ∈ prog.decls,
      CTree.MatchDecl.RuntimeEquations ctx prog.rootHandle resolve concrete decl) :
    ∃ results defined semantic,
      prog.rootResults? = some results ∧
      MatchProg.collectDeclBindings prog.bindingDecls .empty = some defined ∧
      CTree.MatchProg.Realizes prog semantic ∧
      defined.AgreesOn (results.toList.map Handle.id) semantic (concrete.denote resolve (fun ptr => ptr.getType! ctx)) ∧
      semantic.AgreesWith (concrete.denote resolve (fun ptr => ptr.getType! ctx)) := by
  have hex : ∃ final, prog.collectBindings = some final := by
    cases h : prog.collectBindings with
    | none => simp [h] at collected
    | some final => exact ⟨final, rfl⟩
  obtain ⟨final, hfinal⟩ := hex
  simp only [MatchProg.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hfinal
  obtain ⟨results, hresults, defined, hdefined, _⟩ := hfinal
  suffices replay : ∃ semantic, CTree.MatchProg.Realizes prog semantic ∧
      defined.AgreesOn (results.toList.map Handle.id) semantic (concrete.denote resolve (fun ptr => ptr.getType! ctx)) ∧
      semantic.AgreesWith (concrete.denote resolve (fun ptr => ptr.getType! ctx)) by
    obtain ⟨semantic, hr, ha, hc⟩ := replay
    exact ⟨results, defined, semantic, hresults, hdefined, hr, ha, hc⟩
  cases hdecls : prog.decls with
  | nil => simp [MatchProg.rootResults?, hdecls] at hresults
  | cons decl rest =>
    cases decl with
    | operation code operands types matcher property op resultHandles count =>
      by_cases hroot : op = prog.rootHandle
      · subst op
        have heq : resultHandles = results := by
          simpa [MatchProg.rootResults?, hdecls] using hresults
        subst results
        exact CTree.MatchProg.realizes_of_run resolve run hdefined equations
          (MatchProg.avoids_rootResults_of_collectDeclBindings hdecls hdefined)
          (MatchProg.rootResults_coverage_of_collectDeclBindings hdecls hdefined)
      · simp [MatchProg.rootResults?, hdecls, hroot] at hresults
    | value ty handle => simp [MatchProg.rootResults?, hdecls] at hresults
    | type matcher handle => simp [MatchProg.rootResults?, hdecls] at hresults
    | inspectOperation op inspect outputs => simp [MatchProg.rootResults?, hdecls] at hresults
    | applyNative inputs predicate => simp [MatchProg.rootResults?, hdecls] at hresults

theorem Pattern.matcher_collectBindings_isSome {rule : Pattern OpCode}
    (wellFormed : rule.StructurallyWellFormed) : rule.matcher.collectBindings.isSome = true := by
  cases h : rule.matcher.collectBindings with
  | none => simp [Pattern.StructurallyWellFormed, Pattern.checkStructure, h] at wellFormed
  | some defined => rfl

/-- Pattern validity and a concrete match give a semantic match under primitive execution facts. -/
theorem CTree.Pattern.Valid.realizes_of_run {rule : Veir.Puddle.Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx : IRContext OpCode} {root : OperationPtr}
    {concrete : Assignment OpCode} (resolve : ValuePtr → Option RuntimeValue)
    (run : rule.matcher.run ctx root = some concrete)
    (equations : ∀ decl ∈ rule.matcher.decls,
      CTree.MatchDecl.RuntimeEquations ctx rule.matcher.rootHandle resolve concrete decl) :
    ∃ results defined semantic,
      rule.matcher.rootResults? = some results ∧
      MatchProg.collectDeclBindings rule.matcher.bindingDecls .empty = some defined ∧
      CTree.MatchProg.Realizes rule.matcher semantic ∧
      defined.AgreesOn (results.toList.map Handle.id) semantic (concrete.denote resolve (fun ptr => ptr.getType! ctx)) ∧
      semantic.AgreesWith (concrete.denote resolve (fun ptr => ptr.getType! ctx)) :=
  CTree.MatchProg.realizes_of_run_of_collectBindings resolve run
    (Pattern.matcher_collectBindings_isSome valid.structurallyWellFormed) equations


theorem HandleContext.unavailable_of_insertFresh {before after : HandleContext}
    {kind : HandleType OpCode} {handle : Handle OpCode kind}
    (h : before.insertFresh handle = some after) : after.unavailable = before.unavailable := by
  unfold HandleContext.insertFresh at h
  split at h
  · cases h; rfl
  · contradiction

theorem HandleContext.unavailable_of_insertManyFresh {before after : HandleContext}
    {kind : HandleType OpCode} (handles : List (Handle OpCode kind))
    (h : before.insertManyFresh handles = some after) : after.unavailable = before.unavailable := by
  induction handles generalizing before with
  | nil => cases h; rfl
  | cons first rest ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨middle, hf, hr⟩ := h
    exact (ih hr).trans (HandleContext.unavailable_of_insertFresh hf)

theorem MetadataTuple.Shape.unavailable_of_insertFreshBindings
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) {before after : HandleContext}
    (h : shape.insertFreshBindings before handles = some after) : after.unavailable = before.unavailable := by
  induction shape generalizing before with
  | unit => cases h; rfl
  | atom atom => cases atom <;> exact HandleContext.unavailable_of_insertFresh h
  | cons atom tail ih =>
    cases atom <;> simp only [MetadataTuple.Shape.insertFreshBindings, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    all_goals
      obtain ⟨middle, hf, hr⟩ := h
      exact (ih _ hr).trans (HandleContext.unavailable_of_insertFresh hf)

theorem MatchDecl.unavailable_of_collectBindings
    (decl : MatchDecl OpCode) {before after : HandleContext}
    (h : decl.collectBindings before = some after) : after.unavailable = before.unavailable := by
  cases decl with
  | type matcher handle => exact HandleContext.unavailable_of_insertFresh h
  | value ty handle =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, _, h⟩ := h
    exact HandleContext.unavailable_of_insertFresh h
  | operation code operands types matcher property op results count =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, _, u', _, middle₁, hresults, middle₂, hproperty, hop⟩ := h
    exact (HandleContext.unavailable_of_insertFresh hop).trans
      ((HandleContext.unavailable_of_insertFresh hproperty).trans
        (HandleContext.unavailable_of_insertManyFresh _ hresults))
  | inspectOperation op inspect outputs =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, _, h⟩ := h
    exact MetadataTuple.Shape.unavailable_of_insertFreshBindings _ _ h
  | applyNative inputs predicate =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨u, _, rfl⟩ := h
    rfl

theorem MatchProg.unavailable_of_collectDeclBindings
    (decls : List (MatchDecl OpCode)) {before after : HandleContext}
    (h : MatchProg.collectDeclBindings decls before = some after) : after.unavailable = before.unavailable := by
  induction decls generalizing before with
  | nil => cases h; rfl
  | cons decl rest ih =>
    simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hf, hr⟩ := h
    exact (ih hr).trans (decl.unavailable_of_collectBindings hf)

theorem MatchDecl.operation_inputs_known_of_collectBindings
    {code operands types matcher property op results count} {before after : HandleContext}
    (collected : (MatchDecl.operation code operands types matcher property op results count).collectBindings before = some after) :
    (∀ handle ∈ operands, after.lookup handle.id = some .value) ∧
      (∀ handle ∈ types, after.lookup handle.id = some .type) ∧
      after.lookup property.id = some (.prop code) := by
  have hpreserve {id kind} (h : before.lookup id = some kind) : after.lookup id = some kind :=
    MatchDecl.lookup_preserved_of_collectBindings
      (.operation code operands types matcher property op results count) collected h
  simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
  obtain ⟨u, hv, u', ht, middle₁, hresults, middle₂, hproperty, hop⟩ := collected
  have hvalues := require_of_guard hv
  have htypes := require_of_guard ht
  simp only [HandleContext.requireMany, List.all_eq_true] at hvalues htypes
  exact ⟨fun handle hm => hpreserve (HandleContext.lookup_of_require (hvalues handle (by simpa using hm))),
    fun handle hm => hpreserve (HandleContext.lookup_of_require (htypes handle (by simpa using hm))),
    HandleContext.lookup_preserved_of_insertFresh hop (HandleContext.lookup_of_insertFresh hproperty)⟩

theorem MatchProg.rootInputs_available_of_collectDeclBindings {prog : MatchProg OpCode α}
    {code operands types matcher property results count rest} {after : HandleContext}
    (rootFirst : prog.decls = .operation code operands types matcher property prog.rootHandle results count :: rest)
    (collected : MatchProg.collectDeclBindings prog.bindingDecls .empty = some after) :
    after.requireMany operands.toList = true ∧ after.requireMany types.toList = true ∧
      after.require property = true := by
  have hempty : after.unavailable = [] := MatchProg.unavailable_of_collectDeclBindings _ collected
  obtain ⟨first, guards, horder, hguards⟩ := MatchProg.bindingDecls_root_last rootFirst
  rw [horder, MatchProg.collectDeclBindings_append] at collected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
  obtain ⟨beforeRoot, hfirst, htail⟩ := collected
  simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at htail
  obtain ⟨afterRoot, hroot, hguardsCollected⟩ := htail
  obtain ⟨hoperands, htypes, hproperty⟩ := MatchDecl.operation_inputs_known_of_collectBindings hroot
  have keep {id kind} (h : afterRoot.lookup id = some kind) : after.lookup id = some kind :=
    MatchProg.lookup_preserved_of_collectDeclBindings guards hguardsCollected h
  simp only [HandleContext.requireMany, List.all_eq_true]
  refine ⟨?_, ?_, ?_⟩
  · intro handle hm
    simp [HandleContext.require, hempty, keep (hoperands handle (by simpa using hm))]
  · intro handle hm
    simp [HandleContext.require, hempty, keep (htypes handle (by simpa using hm))]
  · simp [HandleContext.require, hempty, keep hproperty]


theorem MatchProg.rootResults_known_of_collectDeclBindings {prog : MatchProg OpCode α}
    {code operands types matcher property results count rest} {after : HandleContext}
    (rootFirst : prog.decls = .operation code operands types matcher property prog.rootHandle results count :: rest)
    (collected : MatchProg.collectDeclBindings prog.bindingDecls .empty = some after) :
    ∀ id ∈ results.toList.map Handle.id, after.lookup id = some .value := by
  obtain ⟨first, guards, horder, hguards⟩ := MatchProg.bindingDecls_root_last rootFirst
  rw [horder, MatchProg.collectDeclBindings_append] at collected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
  obtain ⟨beforeRoot, hfirst, htail⟩ := collected
  simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at htail
  obtain ⟨afterRoot, hroot, hguardsCollected⟩ := htail
  simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at hroot
  obtain ⟨u, _, u', _, middle₁, hresults, middle₂, hproperty, hop⟩ := hroot
  intro id hm
  obtain ⟨handle, hh, rfl⟩ := List.mem_map.mp hm
  exact MatchProg.lookup_preserved_of_collectDeclBindings _ hguardsCollected
    (HandleContext.lookup_preserved_of_insertFresh hop
      (HandleContext.lookup_preserved_of_insertFresh hproperty
        (HandleContext.lookup_of_insertManyFresh _ hresults hh)))

theorem CTree.MatchProg.rootSemantics_eq_of_agreesOn_collect {prog : MatchProg OpCode α}
    {code operands types matcher property results count rest} {defined : HandleContext}
    {stage target : SemanticAssignment}
    (rootFirst : prog.decls = .operation code operands types matcher property prog.rootHandle results count :: rest)
    (collected : MatchProg.collectDeclBindings prog.bindingDecls .empty = some defined)
    (agree : defined.AgreesOn (results.toList.map Handle.id) stage target) (memory : MemoryState) :
    CTree.MatchProg.rootSemantics prog stage memory = CTree.MatchProg.rootSemantics prog target memory := by
  obtain ⟨hv, ht, hp⟩ := MatchProg.rootInputs_available_of_collectDeclBindings rootFirst collected
  have hsafe := MatchProg.avoids_rootResults_of_collectDeclBindings rootFirst collected
    (.operation code operands types matcher property prog.rootHandle results count)
    (CTree.MatchProg.mem_bindingDecls.mpr (by simp [rootFirst]))
  have hpropertySafe := HandleContext.not_mem_of_require_valueKind hp (by intro h; cases h)
    (MatchProg.rootResults_known_of_collectDeclBindings rootFirst collected)
  exact CTree.MatchProg.rootSemantics_eq_of_agreesOn rootFirst agree hv ht hp hsafe.1 hsafe.2
    hpropertySafe memory


/-- Full matcher bridge, including equality of the replayed and concrete root semantics. -/
theorem CTree.Pattern.Valid.realizes_of_run_with_rootSemantics {rule : Veir.Puddle.Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) {ctx : IRContext OpCode} {root : OperationPtr}
    {concrete : Assignment OpCode} (resolve : ValuePtr → Option RuntimeValue)
    (run : rule.matcher.run ctx root = some concrete)
    (equations : ∀ decl ∈ rule.matcher.decls,
      CTree.MatchDecl.RuntimeEquations ctx rule.matcher.rootHandle resolve concrete decl) :
    ∃ results defined semantic,
      rule.matcher.rootResults? = some results ∧
      MatchProg.collectDeclBindings rule.matcher.bindingDecls .empty = some defined ∧
      CTree.MatchProg.Realizes rule.matcher semantic ∧
      defined.AgreesOn (results.toList.map Handle.id) semantic (concrete.denote resolve (fun ptr => ptr.getType! ctx)) ∧
      semantic.AgreesWith (concrete.denote resolve (fun ptr => ptr.getType! ctx)) ∧
      ∀ memory, CTree.MatchProg.rootSemantics rule.matcher semantic memory =
        CTree.MatchProg.rootSemantics rule.matcher (concrete.denote resolve (fun ptr => ptr.getType! ctx)) memory := by
  obtain ⟨results, defined, semantic, hresults, hdefined, hrealizes, hagree, hconsistent⟩ :=
    CTree.Pattern.Valid.realizes_of_run valid resolve run equations
  refine ⟨results, defined, semantic, hresults, hdefined, hrealizes, hagree, hconsistent, ?_⟩
  intro memory
  cases hdecls : rule.matcher.decls with
  | nil => simp [MatchProg.rootResults?, hdecls] at hresults
  | cons decl rest =>
    cases decl with
    | operation code operands types matcher property op resultHandles count =>
      by_cases hroot : op = rule.matcher.rootHandle
      · subst op
        have heq : resultHandles = results := by
          simpa [MatchProg.rootResults?, hdecls] using hresults
        subst results
        exact CTree.MatchProg.rootSemantics_eq_of_agreesOn_collect hdecls hdefined hagree memory
      · simp [MatchProg.rootResults?, hdecls, hroot] at hresults
    | value ty handle => simp [MatchProg.rootResults?, hdecls] at hresults
    | type matcher handle => simp [MatchProg.rootResults?, hdecls] at hresults
    | inspectOperation op inspect outputs => simp [MatchProg.rootResults?, hdecls] at hresults
    | applyNative inputs predicate => simp [MatchProg.rootResults?, hdecls] at hresults


theorem MatchDecl.operation_results_lookup_of_collectBindings
    {code operands types matcher property op results count} {before after : HandleContext}
    (collected : (MatchDecl.operation code operands types matcher property op results count).collectBindings before = some after) :
    ∀ handle ∈ results, after.lookup handle.id = some .value := by
  simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
  obtain ⟨u, _, u', _, middle₁, hresults, middle₂, hproperty, hop⟩ := collected
  intro handle hm
  exact HandleContext.lookup_preserved_of_insertFresh hop
    (HandleContext.lookup_preserved_of_insertFresh hproperty
      (HandleContext.lookup_of_insertManyFresh _ hresults (by simpa using hm)))

theorem MatchProg.operation_results_lookup_of_collectDeclBindings
    (decls : List (MatchDecl OpCode)) {before after : HandleContext}
    {code operands types matcher property op results count}
    (collected : MatchProg.collectDeclBindings decls before = some after)
    (member : MatchDecl.operation code operands types matcher property op results count ∈ decls) :
    ∀ handle ∈ results, after.lookup handle.id = some .value := by
  induction decls generalizing before with
  | nil => simp at member
  | cons first rest ih =>
    simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hfirst, hrest⟩ := collected
    rcases List.mem_cons.mp member with heq | hmem
    · subst first
      intro handle hm
      exact MatchProg.lookup_preserved_of_collectDeclBindings _ hrest
        (MatchDecl.operation_results_lookup_of_collectBindings hfirst handle hm)
    · exact ih hrest hmem

theorem MatchProg.value_lookup_of_collectDeclBindings
    (decls : List (MatchDecl OpCode)) {before after : HandleContext}
    {ty : Handle OpCode .type} {handle : Handle OpCode .value}
    (collected : MatchProg.collectDeclBindings decls before = some after)
    (member : MatchDecl.value ty handle ∈ decls) : after.lookup handle.id = some .value := by
  induction decls generalizing before with
  | nil => simp at member
  | cons first rest ih =>
    simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hfirst, hrest⟩ := collected
    rcases List.mem_cons.mp member with heq | hmem
    · subst first
      simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at hfirst
      obtain ⟨u, _, hvalue⟩ := hfirst
      exact MatchProg.lookup_preserved_of_collectDeclBindings _ hrest
        (HandleContext.lookup_of_insertFresh hvalue)
    · exact ih hrest hmem

theorem MatchProg.nonroot_results_disjoint_of_collectDeclBindings {prog : MatchProg OpCode α}
    {rootCode rootOperands rootTypes rootMatcher rootProperty rootResults rootCount rest}
    {after : HandleContext}
    (rootFirst : prog.decls = .operation rootCode rootOperands rootTypes rootMatcher rootProperty
      prog.rootHandle rootResults rootCount :: rest)
    (collected : MatchProg.collectDeclBindings prog.bindingDecls .empty = some after)
    {code operands types matcher property op results count}
    (member : MatchDecl.operation code operands types matcher property op results count ∈ prog.bindingDecls)
    (nonroot : op ≠ prog.rootHandle) :
    ∀ handle ∈ results, handle.id ∉ rootResults.toList.map Handle.id := by
  obtain ⟨first, guards, horder, hguards⟩ := MatchProg.bindingDecls_root_last rootFirst
  rw [horder, MatchProg.collectDeclBindings_append] at collected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
  obtain ⟨beforeRoot, hfirst, htail⟩ := collected
  simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at htail
  obtain ⟨afterRoot, hroot, _⟩ := htail
  simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at hroot
  obtain ⟨u, _, u', _, middle₁, hrootResults, _⟩ := hroot
  rw [horder] at member
  have hprefix : MatchDecl.operation code operands types matcher property op results count ∈ first := by
    rcases List.mem_append.mp member with hprefix | htail
    · exact hprefix
    · rcases List.mem_cons.mp htail with heq | hguard
      · cases heq; exact False.elim (nonroot rfl)
      · have hg := hguards _ hguard; simp [MatchDecl.isGuard] at hg
  intro handle hm hrootId
  obtain ⟨rootResult, hrootResult, heq⟩ := List.mem_map.mp hrootId
  have hmissing := HandleContext.lookup_eq_none_of_insertManyFresh _ hrootResults hrootResult
  have hknown := MatchProg.operation_results_lookup_of_collectDeclBindings _ hfirst hprefix handle hm
  rw [heq, hknown] at hmissing
  contradiction

theorem MatchProg.leaf_disjoint_of_collectDeclBindings {prog : MatchProg OpCode α}
    {rootCode rootOperands rootTypes rootMatcher rootProperty rootResults rootCount rest}
    {after : HandleContext}
    (rootFirst : prog.decls = .operation rootCode rootOperands rootTypes rootMatcher rootProperty
      prog.rootHandle rootResults rootCount :: rest)
    (collected : MatchProg.collectDeclBindings prog.bindingDecls .empty = some after)
    {ty : Handle OpCode .type} {handle : Handle OpCode .value}
    (member : MatchDecl.value ty handle ∈ prog.bindingDecls) :
    handle.id ∉ rootResults.toList.map Handle.id := by
  obtain ⟨first, guards, horder, hguards⟩ := MatchProg.bindingDecls_root_last rootFirst
  rw [horder, MatchProg.collectDeclBindings_append] at collected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
  obtain ⟨beforeRoot, hfirst, htail⟩ := collected
  simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at htail
  obtain ⟨afterRoot, hroot, _⟩ := htail
  simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at hroot
  obtain ⟨u, _, u', _, middle₁, hrootResults, _⟩ := hroot
  rw [horder] at member
  have hprefix : MatchDecl.value ty handle ∈ first := by
    rcases List.mem_append.mp member with hprefix | htail
    · exact hprefix
    · rcases List.mem_cons.mp htail with heq | hguard
      · cases heq
      · have hg := hguards _ hguard; simp [MatchDecl.isGuard] at hg
  intro hrootId
  obtain ⟨rootResult, hrootResult, heq⟩ := List.mem_map.mp hrootId
  have hmissing := HandleContext.lookup_eq_none_of_insertManyFresh _ hrootResults hrootResult
  have hknown := MatchProg.value_lookup_of_collectDeclBindings _ hfirst hprefix
  rw [heq, hknown] at hmissing
  contradiction


/-- The matcher's concrete root-result IDs are disjoint from all non-root semantic binders. -/
structure MatcherRootScope (prog : MatchProg OpCode α) (rootResults : Array (Handle OpCode .value)) : Prop where
  resultsIdentified : prog.rootResults? = some rootResults
  rootOperation : ∀ code operands types matcher property op results count,
    MatchDecl.operation code operands types matcher property op results count ∈ prog.decls →
    op = prog.rootHandle → ∀ handle ∈ results, handle.id ∈ rootResults.toList.map Handle.id
  nonrootOperation : ∀ code operands types matcher property op results count,
    MatchDecl.operation code operands types matcher property op results count ∈ prog.decls →
    op ≠ prog.rootHandle → op.id ≠ prog.rootHandle.id ∧
      ∀ handle ∈ results, handle.id ∉ rootResults.toList.map Handle.id
  leaf : ∀ ty handle, MatchDecl.value ty handle ∈ prog.decls →
    handle.id ∉ rootResults.toList.map Handle.id

theorem Handle.eq_of_id_eq {kind : HandleType OpCode} {a b : Handle OpCode kind}
    (h : a.id = b.id) : a = b := by
  cases a; cases b; simpa using h

theorem MatcherRootScope.of_collectDeclBindings {prog : MatchProg OpCode α}
    {rootCode rootOperands rootTypes rootMatcher rootProperty rootResults rootCount rest}
    {after : HandleContext}
    (rootFirst : prog.decls = .operation rootCode rootOperands rootTypes rootMatcher rootProperty
      prog.rootHandle rootResults rootCount :: rest)
    (collected : MatchProg.collectDeclBindings prog.bindingDecls .empty = some after) :
    MatcherRootScope prog rootResults := by
  constructor
  · simp [MatchProg.rootResults?, rootFirst]
  · intro code operands types matcher property op results count member isRoot
    exact MatchProg.rootResults_coverage_of_collectDeclBindings rootFirst collected
      _ (CTree.MatchProg.mem_bindingDecls.mpr member) code operands types matcher property op results count
      rfl isRoot
  · intro code operands types matcher property op results count member nonroot
    refine ⟨fun heq => nonroot (Handle.eq_of_id_eq heq), ?_⟩
    exact MatchProg.nonroot_results_disjoint_of_collectDeclBindings rootFirst collected
      (CTree.MatchProg.mem_bindingDecls.mpr member) nonroot
  · intro ty handle member
    exact MatchProg.leaf_disjoint_of_collectDeclBindings rootFirst collected
      (CTree.MatchProg.mem_bindingDecls.mpr member)

/-- Static validity alone establishes the concrete matcher scope needed by trace replay. -/
theorem CTree.Pattern.Valid.matcher_rootScope {rule : Veir.Puddle.Pattern OpCode}
    (valid : CTree.Pattern.Valid rule) : ∃ rootResults, MatcherRootScope rule.matcher rootResults := by
  have hex : ∃ final, rule.matcher.collectBindings = some final := by
    have hsome := Pattern.matcher_collectBindings_isSome valid.structurallyWellFormed
    cases h : rule.matcher.collectBindings with
    | none => simp [h] at hsome
    | some final => exact ⟨final, rfl⟩
  obtain ⟨final, hfinal⟩ := hex
  simp only [MatchProg.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hfinal
  obtain ⟨results, hresults, defined, hdefined, _⟩ := hfinal
  cases hdecls : rule.matcher.decls with
  | nil => simp [MatchProg.rootResults?, hdecls] at hresults
  | cons decl rest =>
    cases decl with
    | operation code operands types matcher property op resultHandles count =>
      by_cases hroot : op = rule.matcher.rootHandle
      · subst op
        exact ⟨resultHandles, MatcherRootScope.of_collectDeclBindings hdecls hdefined⟩
      · simp [MatchProg.rootResults?, hdecls, hroot] at hresults
    | value ty handle => simp [MatchProg.rootResults?, hdecls] at hresults
    | type matcher handle => simp [MatchProg.rootResults?, hdecls] at hresults
    | inspectOperation op inspect outputs => simp [MatchProg.rootResults?, hdecls] at hresults
    | applyNative inputs predicate => simp [MatchProg.rootResults?, hdecls] at hresults


end

end Veir.Puddle
