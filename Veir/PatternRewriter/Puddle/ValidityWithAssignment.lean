module

public import Veir.PatternRewriter.Puddle.Validity
import all Veir.PatternRewriter.Puddle.Validity

import Veir.Data.Refinement
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Attribute
import all Veir.IR.Basic
import all Veir.PatternRewriter.Semantics

/-!
# Assignment-based Puddle Pattern Validity

This file defines the assignment-quantified formulation of semantic preservation and proves that it
is equivalent to the author-facing `Pattern.PreservesSemantics` predicate for structurally
well-formed patterns.
-/

namespace Veir.Puddle

public section

/-- Binds multiple values to multiple value handles. -/
@[expose]
def SemanticAssignment.bindValues (assignment : SemanticAssignment)
    (handles : List (Handle OpCode .value)) (values : List RuntimeValue) :
    Option SemanticAssignment :=
  match handles, values with
  | [], [] => some assignment
  | handle :: handles, value :: values =>
    (assignment.bindValue handle value).bindValues handles values
  | _, _ => none

/-- A semantic assignment satisfies the constraints of a matcher declaration. -/
@[expose]
def MatchDecl.ModelsWithAssignment (decl : MatchDecl OpCode)
    (assignment : SemanticAssignment) : Prop :=
  match decl with
  | .type matcher handle =>
    ∃ type, assignment.getType handle = some type ∧ matcher type = true
  | .value typeHandle handle =>
    ∃ type value,
      assignment.getType typeHandle = some type ∧
      assignment.getValue handle = some value ∧
      value.Conforms type
  | .operation opCode operandHandles returnTypeHandles property propertyHandle _ resultHandles _ =>
    ∃ operands resultTypes results actualProperty,
      assignment.getValues operandHandles.toList = some operands ∧
      assignment.getTypes returnTypeHandles.toList = some resultTypes ∧
      assignment.getProperty propertyHandle = some actualProperty ∧
      assignment.getValues resultHandles.toList = some results.toList ∧
      property actualProperty = true ∧
      InterpretsTo opCode actualProperty resultTypes.toArray operands.toArray results
  | @MatchDecl.applyNative _ _ _ inputBundle inputs predicate =>
    ∃ values,
      MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs = some values ∧
      predicate values = true

/-- Pointwise semantic facts for every matcher declaration. -/
@[expose]
def MatchProg.ModelsWithAssignment (prog : MatchProg OpCode α)
    (assignment : SemanticAssignment) : Prop :=
  ∀ decl ∈ prog.decls, decl.ModelsWithAssignment assignment

/-! The evaluator is a proof-level view of the typed, pure denotation. The universal purity
check is noncomputable; compiled rewrites continue to use `CreateDecl.run`. -/

/-- Semantically execute one creation declaration and bind all of its outputs. -/
@[expose]
noncomputable def CreateDecl.eval (assignment : SemanticAssignment) (decl : CreateDecl OpCode)
     : Option SemanticAssignment := by
  classical
  exact match decl with
  | .type value result =>
      some (assignment.bindType result value)
  | .property _ value result =>
      some (assignment.bindProperty result value)
  | .operation opCode operands resultTypeHandles propertyHandle _ resultHandles => do
      let values ← assignment.getValues operands.toList
      let resultTypes ← assignment.getTypes resultTypeHandles.toList
      let property ← assignment.getProperty propertyHandle
      let results ←
        match interpretOp' opCode property resultTypes.toArray values.toArray #[] .empty with
        | .ok (results, _, none) => some results
        | _ => none
      if InterpretsTo opCode property resultTypes.toArray values.toArray results then
        assignment.bindValues resultHandles.toList results.toList
      else none
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs rewrite outputs => do
      let inputValues ← MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs
      let outputValues ← rewrite inputValues
      return MetadataTuple.bindSemantic (self := outputBundle) assignment outputs outputValues

/-- Semantically execute creation declarations in program order. -/
@[expose]
noncomputable def CreateProg.evalDecls (decls : List (CreateDecl OpCode)) (assignment : SemanticAssignment)
    : Option SemanticAssignment :=
  decls.foldlM CreateDecl.eval assignment

/-- The assignment-quantified semantic preservation property. -/
@[expose]
def Pattern.PreservesSemanticsWithAssignment (rule : Pattern OpCode) : Prop :=
  ∀ assignment, rule.matcher.ModelsWithAssignment assignment →
    ∃ final, CreateProg.evalDecls rule.creation.decls assignment = some final ∧
      rule.replacement.refinesRoot rule.matcher.rootResults? assignment final


/-- Assignments agree on value and metadata handles; operation handles are structural only. -/
private def SemanticAssignment.AgreeOn (ctx : HandleContext)
    (left right : SemanticAssignment) : Prop :=
  ∀ id kind, ctx.lookup id = some kind → kind ≠ .op → left id = right id

private def SemanticBinding.HasKind : SemanticBinding → HandleType OpCode → Prop
  | .value _, .value => True
  | .type _, .type => True
  | .property actualOpCode _, .prop expectedOpCode => actualOpCode = expectedOpCode
  | _, _ => False

/-- Every value or metadata handle in the context has a binding of the expected kind. -/
private def SemanticAssignment.Realizes (ctx : HandleContext)
    (assignment : SemanticAssignment) : Prop :=
  ∀ id kind, ctx.lookup id = some kind → kind ≠ .op →
    ∃ binding, assignment id = some binding ∧ binding.HasKind kind

private theorem SemanticAssignment.AgreeOn.empty (left right : SemanticAssignment) :
    AgreeOn HandleContext.empty left right := by
  intro id kind h
  change none = some kind at h
  contradiction

private theorem SemanticAssignment.Realizes.empty :
    Realizes HandleContext.empty SemanticAssignment.empty := by
  intro id kind hlookup
  change none = some kind at hlookup
  contradiction

private def HandleContext.Extends (larger smaller : HandleContext) : Prop :=
  ∀ id kind, smaller.lookup id = some kind → larger.lookup id = some kind

private theorem HandleContext.Extends.refl (ctx : HandleContext) : ctx.Extends ctx := by
  intro id kind hlookup
  exact hlookup

private theorem HandleContext.Extends.trans
    {first second third : HandleContext}
    (hsecond : second.Extends first) (hthird : third.Extends second) : third.Extends first := by
  intro id kind hlookup
  exact hthird id kind (hsecond id kind hlookup)

private theorem HandleContext.Extends.insertFresh
    {ctx ctx' : HandleContext} {handle : Handle OpCode kind}
    (hinsert : ctx.insertFresh handle = some ctx') : ctx'.Extends ctx := by
  unfold HandleContext.insertFresh at hinsert
  split at hinsert
  next hnone =>
    simp only [Option.some.injEq] at hinsert
    subst ctx'
    intro id actualKind hlookup
    change (if handle.id = id then some kind else ctx.lookup id) = some actualKind
    split
    next heq =>
      subst id
      rw [hnone] at hlookup
      contradiction
    next => exact hlookup
  next => contradiction

private theorem HandleContext.lookup_insertFresh_self
    {ctx ctx' : HandleContext} {handle : Handle OpCode kind}
    (hinsert : ctx.insertFresh handle = some ctx') :
    ctx'.lookup handle.id = some kind := by
  unfold HandleContext.insertFresh at hinsert
  split at hinsert
  next =>
    simp only [Option.some.injEq] at hinsert
    subst ctx'
    change (if handle.id = handle.id then some kind else ctx.lookup handle.id) = some kind
    simp
  next => contradiction

private theorem HandleContext.Extends.insertManyFresh
    {ctx ctx' : HandleContext} {handles : List (Handle OpCode kind)}
    (hinsert : ctx.insertManyFresh handles = some ctx') : ctx'.Extends ctx := by
  induction handles generalizing ctx with
  | nil =>
    simp [HandleContext.insertManyFresh] at hinsert
    subst ctx'
    exact .refl ctx
  | cons handle handles ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons] at hinsert
    cases hhead : ctx.insertFresh handle with
    | none => simp [hhead] at hinsert
    | some nextCtx =>
      simp [hhead] at hinsert
      exact (HandleContext.Extends.insertFresh hhead).trans (ih hinsert)

private theorem MatchDecl.collectBindings_extends
    {ctx ctx' : HandleContext} {decl : MatchDecl OpCode}
    (hcollect : decl.collectBindings ctx = some ctx') : ctx'.Extends ctx := by
  cases decl with
  | type matcher result => exact HandleContext.Extends.insertFresh hcollect
  | value typeHandle result =>
    simp only [MatchDecl.collectBindings, guard] at hcollect
    split at hcollect
    next => exact HandleContext.Extends.insertFresh hcollect
    next => contradiction
  | operation opCode operands resultTypes property propertyHandle opHandle resultHandles nested =>
    simp only [MatchDecl.collectBindings, guard] at hcollect
    split at hcollect
    next =>
      split at hcollect
      next =>
        simp only [pure_bind] at hcollect
        cases hresults : ctx.insertManyFresh resultHandles.toList with
        | none => simp [hresults] at hcollect
        | some resultsCtx =>
          simp [hresults] at hcollect
          cases hproperty : resultsCtx.insertFresh propertyHandle with
          | none => simp [hproperty] at hcollect
          | some propertyCtx =>
            simp [hproperty] at hcollect
            exact (HandleContext.Extends.insertManyFresh hresults).trans
              ((HandleContext.Extends.insertFresh hproperty).trans
                (HandleContext.Extends.insertFresh hcollect))
      next => contradiction
    next => contradiction
  | applyNative inputs predicate =>
    simp only [MatchDecl.collectBindings, guard] at hcollect
    split at hcollect
    next =>
      simp at hcollect
      subst ctx'
      exact .refl ctx
    next => contradiction

private theorem MatchProg.collectDeclBindings_extends
    {decls : List (MatchDecl OpCode)} {ctx ctx' : HandleContext}
    (hcollect : MatchProg.collectDeclBindings decls ctx = some ctx') : ctx'.Extends ctx := by
  induction decls generalizing ctx with
  | nil =>
    simp only [MatchProg.collectDeclBindings, Option.some.injEq] at hcollect
    subst ctx'
    exact .refl ctx
  | cons decl decls ih =>
    simp only [MatchProg.collectDeclBindings] at hcollect
    cases hdecl : decl.collectBindings ctx with
    | none => simp [hdecl] at hcollect
    | some nextCtx =>
      simp [hdecl] at hcollect
      exact (MatchDecl.collectBindings_extends hdecl).trans (ih hcollect)

private theorem HandleContext.lookup_insertManyFresh
    {ctx ctx' : HandleContext} {handles : List (Handle OpCode kind)}
    (hinsert : ctx.insertManyFresh handles = some ctx')
    (handle : Handle OpCode kind) (hmem : handle ∈ handles) :
    ctx'.lookup handle.id = some kind := by
  induction handles generalizing ctx with
  | nil => simp at hmem
  | cons head tail ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons] at hinsert
    cases hhead : ctx.insertFresh head with
    | none => simp [hhead] at hinsert
    | some next =>
      simp [hhead] at hinsert
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact (HandleContext.Extends.insertManyFresh hinsert) handle.id kind
          (HandleContext.lookup_insertFresh_self hhead)
      · exact ih hinsert hmem

private theorem MatchDecl.collectBindings_lookup_result
    {ctx ctx' : HandleContext} {opCode : OpCode}
    {operands : Array (Handle OpCode .value)} {resultTypes : Array (Handle OpCode .type)}
    {property : PropertyMatcher opCode} {propertyHandle : Handle OpCode (.prop opCode)}
    {opHandle : Handle OpCode .op} {results : Array (Handle OpCode .value)}
    {nested : results.size = resultTypes.size}
    (hcollect : (MatchDecl.operation opCode operands resultTypes property propertyHandle opHandle
      results nested).collectBindings ctx = some ctx') :
    ∀ result ∈ results.toList, ctx'.lookup result.id = some .value := by
  simp only [MatchDecl.collectBindings, guard] at hcollect
  split at hcollect
  next =>
    split at hcollect
    next =>
      simp only [pure_bind] at hcollect
      cases hresults : ctx.insertManyFresh results.toList with
      | none => simp [hresults] at hcollect
      | some resultsCtx =>
        simp [hresults] at hcollect
        cases hproperty : resultsCtx.insertFresh propertyHandle with
        | none => simp [hproperty] at hcollect
        | some propertyCtx =>
          simp [hproperty] at hcollect
          intro result hmem
          exact ((HandleContext.Extends.insertFresh hproperty).trans
            (HandleContext.Extends.insertFresh hcollect)) result.id .value
            (HandleContext.lookup_insertManyFresh hresults result hmem)
    next => contradiction
  next => contradiction

private theorem MatchProg.collectDeclBindings_lookup_result
    {decls : List (MatchDecl OpCode)} {ctx ctx' : HandleContext}
    {decl : MatchDecl OpCode} {result : Handle OpCode .value}
    (hcollect : MatchProg.collectDeclBindings decls ctx = some ctx')
    (hmem : decl ∈ decls)
    (hisOp : ∃ opCode operands resultTypes property propertyHandle opHandle results nested,
      decl = .operation opCode operands resultTypes property propertyHandle opHandle results nested ∧
        result ∈ results.toList) :
    ctx'.lookup result.id = some .value := by
  induction decls generalizing ctx with
  | nil => simp at hmem
  | cons head decls ih =>
    simp only [MatchProg.collectDeclBindings] at hcollect
    cases hhead : head.collectBindings ctx with
    | none => simp [hhead] at hcollect
    | some nextCtx =>
      simp [hhead] at hcollect
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · rcases hisOp with ⟨opCode, operands, resultTypes, property, propertyHandle,
          opHandle, results, nested, rfl, hresult⟩
        exact (MatchProg.collectDeclBindings_extends hcollect) result.id .value
          (MatchDecl.collectBindings_lookup_result hhead result hresult)
      · exact ih hcollect hmem

private theorem SemanticAssignment.AgreeOn.refl (ctx : HandleContext)
    (assignment : SemanticAssignment) : AgreeOn ctx assignment assignment := by
  intro _ _ _ _
  rfl

private theorem SemanticAssignment.AgreeOn.symm
    {ctx : HandleContext} {left right : SemanticAssignment}
    (hagrees : AgreeOn ctx left right) : AgreeOn ctx right left := by
  intro id kind hlookup hsemantic
  exact (hagrees id kind hlookup hsemantic).symm

private theorem SemanticAssignment.AgreeOn.trans
    {ctx : HandleContext} {first second third : SemanticAssignment}
    (hfirst : AgreeOn ctx first second) (hsecond : AgreeOn ctx second third) :
    AgreeOn ctx first third := by
  intro id kind hlookup hsemantic
  exact (hfirst id kind hlookup hsemantic).trans (hsecond id kind hlookup hsemantic)

private theorem SemanticAssignment.AgreeOn.mono
    {smaller larger : HandleContext} {left right : SemanticAssignment}
    (hagrees : AgreeOn larger left right) (hextends : larger.Extends smaller) :
    AgreeOn smaller left right := by
  intro id kind hlookup hsemantic
  exact hagrees id kind (hextends id kind hlookup) hsemantic

private theorem SemanticAssignment.AgreeOn.forbid
    {ctx : HandleContext} {left right : SemanticAssignment}
    (hagrees : AgreeOn ctx left right) (handle : Handle OpCode kind) :
    AgreeOn (ctx.forbid handle) left right := by
  exact hagrees

private theorem SemanticAssignment.AgreeOn.forbidMany
    {ctx : HandleContext} {left right : SemanticAssignment}
    (hagrees : AgreeOn ctx left right) (handles : List (Handle OpCode kind)) :
    AgreeOn (ctx.forbidMany handles) left right := by
  induction handles generalizing ctx with
  | nil => exact hagrees
  | cons handle handles ih =>
    exact ih (hagrees.forbid handle)

private theorem SemanticAssignment.AgreeOn.insertFresh
    {kind : HandleType OpCode} {ctx ctx' : HandleContext} {handle : Handle OpCode kind}
    {left right : SemanticAssignment} {binding : SemanticBinding}
    (hagrees : AgreeOn ctx left right) (hinsert : ctx.insertFresh handle = some ctx') :
    AgreeOn ctx' (left.bind handle.id binding) (right.bind handle.id binding) := by
  unfold HandleContext.insertFresh at hinsert
  split at hinsert
  next =>
    simp only [Option.some.injEq] at hinsert
    subst ctx'
    intro id kind' hlookup hsemantic
    simp only [SemanticAssignment.bind]
    split
    · rfl
    · apply hagrees id kind' ?_ hsemantic
      change (if handle.id = id then some kind else ctx.lookup id) = some kind' at hlookup
      split at hlookup
      · subst id
        contradiction
      · exact hlookup
  next => contradiction

private theorem SemanticAssignment.AgreeOn.bindFresh_preserves
    {kind : HandleType OpCode} {ctx ctx' : HandleContext} {handle : Handle OpCode kind}
    {assignment : SemanticAssignment} {binding : SemanticBinding}
    (hinsert : ctx.insertFresh handle = some ctx') :
    AgreeOn ctx (assignment.bind handle.id binding) assignment := by
  unfold HandleContext.insertFresh at hinsert
  split at hinsert
  next hnone =>
    intro id actualKind hlookup hsemantic
    simp only [SemanticAssignment.bind]
    split
    next heq =>
      subst id
      rw [hnone] at hlookup
      contradiction
    next => rfl
  next => contradiction

private theorem SemanticAssignment.Realizes.insertFresh
    {kind : HandleType OpCode} {ctx ctx' : HandleContext} {handle : Handle OpCode kind}
    {assignment : SemanticAssignment} {binding : SemanticBinding}
    (hrealizes : Realizes ctx assignment) (hkind : binding.HasKind kind)
    (hinsert : ctx.insertFresh handle = some ctx') :
    Realizes ctx' (assignment.bind handle.id binding) := by
  unfold HandleContext.insertFresh at hinsert
  split at hinsert
  next hnone =>
    simp only [Option.some.injEq] at hinsert
    subst ctx'
    intro id actualKind hlookup hsemantic
    change (if handle.id = id then some kind else ctx.lookup id) = some actualKind at hlookup
    split at hlookup
    next heq =>
      subst id
      simp only [Option.some.injEq] at hlookup
      subst actualKind
      exact ⟨binding, by simp [SemanticAssignment.bind], hkind⟩
    next hne =>
      rcases hrealizes id actualKind hlookup hsemantic with ⟨oldBinding, hold, holdKind⟩
      refine ⟨oldBinding, ?_, holdKind⟩
      simp [SemanticAssignment.bind, Ne.symm hne, hold]
  next => contradiction

/-- Operation handles remain structural; they have no semantic binding. -/
private theorem SemanticAssignment.AgreeOn.insertOp
    {ctx ctx' : HandleContext} {handle : Handle OpCode .op}
    {left right : SemanticAssignment}
    (hagrees : AgreeOn ctx left right) (hinsert : ctx.insertFresh handle = some ctx') :
    AgreeOn ctx' left right := by
  unfold HandleContext.insertFresh at hinsert
  split at hinsert
  next =>
    simp only [Option.some.injEq] at hinsert
    subst ctx'
    intro id kind hlookup hsemantic
    change (if handle.id = id then some .op else ctx.lookup id) = some kind at hlookup
    split at hlookup
    · simp only [Option.some.injEq] at hlookup
      exact False.elim (hsemantic hlookup.symm)
    · exact hagrees id kind hlookup hsemantic
  next => contradiction

private theorem SemanticAssignment.Realizes.insertOp
    {ctx ctx' : HandleContext} {handle : Handle OpCode .op}
    {assignment : SemanticAssignment}
    (hrealizes : Realizes ctx assignment) (hinsert : ctx.insertFresh handle = some ctx') :
    Realizes ctx' assignment := by
  unfold HandleContext.insertFresh at hinsert
  split at hinsert
  next =>
    simp only [Option.some.injEq] at hinsert
    subst ctx'
    intro id kind hlookup hsemantic
    change (if handle.id = id then some .op else ctx.lookup id) = some kind at hlookup
    split at hlookup
    · simp only [Option.some.injEq] at hlookup
      exact False.elim (hsemantic hlookup.symm)
    · exact hrealizes id kind hlookup hsemantic
  next => contradiction

private theorem SemanticAssignment.Realizes.getType
    {ctx : HandleContext} {assignment : SemanticAssignment}
    {handle : Handle OpCode .type} (hrealizes : Realizes ctx assignment)
    (hlookup : ctx.lookup handle.id = some .type) :
    ∃ type, assignment.getType handle = some type := by
  rcases hrealizes handle.id .type hlookup (by simp) with ⟨binding, hbinding, hkind⟩
  cases binding <;> simp [SemanticBinding.HasKind] at hkind
  rename_i type
  exact ⟨type, by simp [SemanticAssignment.getType, hbinding]⟩

private theorem HandleContext.lookup_of_requireMany
    {ctx : HandleContext} {handles : List (Handle OpCode kind)}
    (hrequire : ctx.requireMany handles = true) (handle : Handle OpCode kind)
    (hmem : handle ∈ handles) : ctx.lookup handle.id = some kind := by
  simp only [HandleContext.requireMany, List.all_eq_true] at hrequire
  exact (of_decide_eq_true (hrequire handle hmem)).1

private theorem SemanticAssignment.Realizes.getValue
    {ctx : HandleContext} {assignment : SemanticAssignment}
    {handle : Handle OpCode .value} (hrealizes : Realizes ctx assignment)
    (hlookup : ctx.lookup handle.id = some .value) :
    ∃ value, assignment.getValue handle = some value := by
  rcases hrealizes handle.id .value hlookup (by simp) with ⟨binding, hbinding, hkind⟩
  cases binding <;> simp [SemanticBinding.HasKind] at hkind
  rename_i value
  exact ⟨value, by simp [SemanticAssignment.getValue, hbinding]⟩

private theorem SemanticAssignment.Realizes.getValues
    {ctx : HandleContext} {assignment : SemanticAssignment}
    {handles : List (Handle OpCode .value)} (hrealizes : Realizes ctx assignment)
    (hrequire : ctx.requireMany handles = true) :
    ∃ values, assignment.getValues handles = some values := by
  induction handles with
  | nil => exact ⟨[], rfl⟩
  | cons handle handles ih =>
    have hhead := hrealizes.getValue
      (HandleContext.lookup_of_requireMany hrequire handle (by simp))
    have htail := ih (by
      simp only [HandleContext.requireMany, List.all_cons, Bool.and_eq_true] at hrequire ⊢
      exact hrequire.2)
    rcases hhead with ⟨value, hvalue⟩
    rcases htail with ⟨values, hvalues⟩
    refine ⟨value :: values, ?_⟩
    unfold SemanticAssignment.getValues at hvalues ⊢
    simp [hvalue, hvalues]

private theorem SemanticAssignment.Realizes.getTypes
    {ctx : HandleContext} {assignment : SemanticAssignment}
    {handles : List (Handle OpCode .type)} (hrealizes : Realizes ctx assignment)
    (hrequire : ctx.requireMany handles = true) :
    ∃ types, assignment.getTypes handles = some types := by
  induction handles with
  | nil => exact ⟨[], rfl⟩
  | cons handle handles ih =>
    have hhead := hrealizes.getType
      (HandleContext.lookup_of_requireMany hrequire handle (by simp))
    have htail := ih (by
      simp only [HandleContext.requireMany, List.all_cons, Bool.and_eq_true] at hrequire ⊢
      exact hrequire.2)
    rcases hhead with ⟨type, htype⟩
    rcases htail with ⟨types, htypes⟩
    refine ⟨type :: types, ?_⟩
    unfold SemanticAssignment.getTypes at htypes ⊢
    simp [htype, htypes]

private theorem SemanticAssignment.AgreeOn.insertFresh_right
    {kind : HandleType OpCode} {ctx ctx' : HandleContext} {handle : Handle OpCode kind}
    {left right : SemanticAssignment} {binding : SemanticBinding}
    (hagrees : AgreeOn ctx left right) (hinsert : ctx.insertFresh handle = some ctx')
    (hright : right handle.id = some binding) :
    AgreeOn ctx' (left.bind handle.id binding) right := by
  unfold HandleContext.insertFresh at hinsert
  split at hinsert
  next =>
    simp only [Option.some.injEq] at hinsert
    subst ctx'
    intro id kind' hlookup hsemantic
    simp only [SemanticAssignment.bind]
    split
    · subst id
      exact hright.symm
    · apply hagrees id kind' ?_ hsemantic
      change (if handle.id = id then some kind else ctx.lookup id) = some kind' at hlookup
      split at hlookup
      · subst id
        contradiction
      · exact hlookup
  next => contradiction

private theorem SemanticAssignment.AgreeOn.getValue
    {ctx : HandleContext} {left right : SemanticAssignment} {handle : Handle OpCode .value}
    (hagrees : AgreeOn ctx left right) (hlookup : ctx.lookup handle.id = some .value) :
    left.getValue handle = right.getValue handle := by
  unfold SemanticAssignment.getValue
  rw [hagrees handle.id .value hlookup (by simp)]

private theorem SemanticAssignment.AgreeOn.getType
    {ctx : HandleContext} {left right : SemanticAssignment} {handle : Handle OpCode .type}
    (hagrees : AgreeOn ctx left right) (hlookup : ctx.lookup handle.id = some .type) :
    left.getType handle = right.getType handle := by
  unfold SemanticAssignment.getType
  rw [hagrees handle.id .type hlookup (by simp)]

private theorem SemanticAssignment.AgreeOn.getProperty
    {ctx : HandleContext} {left right : SemanticAssignment}
    {opCode : OpCode} {handle : Handle OpCode (.prop opCode)}
    (hagrees : AgreeOn ctx left right) (hlookup : ctx.lookup handle.id = some (.prop opCode)) :
    left.getProperty handle = right.getProperty handle := by
  unfold SemanticAssignment.getProperty
  rw [hagrees handle.id (.prop opCode) hlookup (by simp)]

private theorem SemanticAssignment.AgreeOn.getValues
    {ctx : HandleContext} {left right : SemanticAssignment}
    {handles : List (Handle OpCode .value)}
    (hagrees : AgreeOn ctx left right) (hrequire : ctx.requireMany handles = true) :
    left.getValues handles = right.getValues handles := by
  induction handles with
  | nil => rfl
  | cons handle handles ih =>
    simp only [SemanticAssignment.getValues, List.mapM_cons]
    rw [hagrees.getValue (HandleContext.lookup_of_requireMany hrequire handle (by simp))]
    have htail := ih (by
      simp only [HandleContext.requireMany, List.all_cons, Bool.and_eq_true] at hrequire ⊢
      exact hrequire.2)
    unfold SemanticAssignment.getValues at htail
    rw [htail]

private theorem SemanticAssignment.AgreeOn.getTypes
    {ctx : HandleContext} {left right : SemanticAssignment}
    {handles : List (Handle OpCode .type)}
    (hagrees : AgreeOn ctx left right) (hrequire : ctx.requireMany handles = true) :
    left.getTypes handles = right.getTypes handles := by
  induction handles with
  | nil => rfl
  | cons handle handles ih =>
    simp only [SemanticAssignment.getTypes, List.mapM_cons]
    rw [hagrees.getType (HandleContext.lookup_of_requireMany hrequire handle (by simp))]
    have htail := ih (by
      simp only [HandleContext.requireMany, List.all_cons, Bool.and_eq_true] at hrequire ⊢
      exact hrequire.2)
    unfold SemanticAssignment.getTypes at htail
    rw [htail]

private theorem MetadataTuple.Shape.resolveSemantic_eq
    {ctx : HandleContext} {left right : SemanticAssignment}
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles)
    (hagrees : SemanticAssignment.AgreeOn ctx left right)
    (hrequire : shape.requireBindings ctx handles = true) :
    shape.resolveSemantic left handles = shape.resolveSemantic right handles := by
  induction shape with
  | unit => rfl
  | atom metadataAtom =>
    cases metadataAtom with
    | type =>
      exact hagrees.getType (of_decide_eq_true hrequire).1
    | property opCode =>
      exact hagrees.getProperty (of_decide_eq_true hrequire).1
  | cons head tail ih =>
    cases head with
    | type =>
      simp only [MetadataTuple.Shape.requireBindings, Bool.and_eq_true] at hrequire
      simp only [MetadataTuple.Shape.resolveSemantic, MetadataTuple.Atom.resolveSemantic]
      rw [hagrees.getType (of_decide_eq_true hrequire.1).1,
        ih handles.2 hrequire.2]
    | property opCode =>
      simp only [MetadataTuple.Shape.requireBindings, Bool.and_eq_true] at hrequire
      simp only [MetadataTuple.Shape.resolveSemantic, MetadataTuple.Atom.resolveSemantic]
      rw [hagrees.getProperty (of_decide_eq_true hrequire.1).1,
        ih handles.2 hrequire.2]

private theorem MetadataTuple.Shape.bindSemantic_rel
    {ctx ctx' : HandleContext} {left right : SemanticAssignment}
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    (hagrees : SemanticAssignment.AgreeOn ctx left right)
    (hinsert : shape.insertFreshBindings ctx handles = some ctx') :
    SemanticAssignment.AgreeOn ctx'
      (shape.bindSemantic left handles values) (shape.bindSemantic right handles values) := by
  induction shape generalizing ctx ctx' left right with
  | unit =>
    simp only [MetadataTuple.Shape.insertFreshBindings, Option.some.injEq] at hinsert
    subst ctx'
    exact hagrees
  | atom metadataAtom =>
    cases metadataAtom <;>
      exact hagrees.insertFresh hinsert
  | cons head tail ih =>
    cases head with
    | type =>
      simp only [MetadataTuple.Shape.insertFreshBindings] at hinsert
      cases hhead : ctx.insertFresh handles.1 with
      | none => simp [hhead] at hinsert
      | some nextCtx =>
        simp [hhead] at hinsert
        simpa [MetadataTuple.Shape.bindSemantic, MetadataTuple.Atom.bindSemantic,
          SemanticAssignment.bindType] using
          ih handles.2 values.2 (hagrees.insertFresh hhead) hinsert
    | property opCode =>
      simp only [MetadataTuple.Shape.insertFreshBindings] at hinsert
      cases hhead : ctx.insertFresh handles.1 with
      | none => simp [hhead] at hinsert
      | some nextCtx =>
        simp [hhead] at hinsert
        simpa [MetadataTuple.Shape.bindSemantic, MetadataTuple.Atom.bindSemantic,
          SemanticAssignment.bindProperty] using
          ih handles.2 values.2 (hagrees.insertFresh hhead) hinsert

private theorem SemanticAssignment.AgreeOn.insertManyFresh
    {ctx ctx' : HandleContext} {handles : List (Handle OpCode .value)}
    {left right left' right' : SemanticAssignment} {values : List RuntimeValue}
    (hagrees : AgreeOn ctx left right)
    (hinsert : ctx.insertManyFresh handles = some ctx')
    (hleft : left.bindValues handles values = some left')
    (hright : right.bindValues handles values = some right') :
    AgreeOn ctx' left' right' := by
  induction handles generalizing ctx ctx' left right left' right' values with
  | nil =>
    cases values <;> simp [SemanticAssignment.bindValues] at hleft hright
    subst left'
    subst right'
    simp [HandleContext.insertManyFresh] at hinsert
    subst ctx'
    exact hagrees
  | cons handle handles ih =>
    cases values with
    | nil => simp [SemanticAssignment.bindValues] at hleft
    | cons value values =>
      simp only [HandleContext.insertManyFresh, List.foldlM_cons] at hinsert
      simp only [SemanticAssignment.bindValues] at hleft hright
      cases heq : ctx.insertFresh handle with
      | none => simp [heq] at hinsert
      | some nextCtx =>
        simp [heq] at hinsert
        exact ih (hagrees.insertFresh heq) hinsert hleft hright

private theorem SemanticAssignment.getValues_cons_eq_some
    {assignment : SemanticAssignment} {handle : Handle OpCode .value}
    {handles : List (Handle OpCode .value)} {value : RuntimeValue} {values : List RuntimeValue}
    (hget : assignment.getValues (handle :: handles) = some (value :: values)) :
    assignment.getValue handle = some value ∧ assignment.getValues handles = some values := by
  unfold SemanticAssignment.getValues at hget ⊢
  simp only [List.mapM_cons] at hget
  cases hhead : assignment.getValue handle with
  | none => simp [hhead] at hget
  | some actual =>
    cases htail : List.mapM assignment.getValue handles with
    | none => simp [hhead, htail] at hget
    | some actuals =>
      simp [hhead, htail] at hget
      rcases hget with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

private theorem SemanticAssignment.eq_of_getValue_eq_some
    {assignment : SemanticAssignment} {handle : Handle OpCode .value} {value : RuntimeValue}
    (hget : assignment.getValue handle = some value) :
    assignment handle.id = some (.value value) := by
  grind [SemanticAssignment.getValue]

private theorem SemanticAssignment.eq_of_getType_eq_some
    {assignment : SemanticAssignment} {handle : Handle OpCode .type} {value : TypeAttr}
    (hget : assignment.getType handle = some value) :
    assignment handle.id = some (.type value) := by
  grind [SemanticAssignment.getType]

private theorem SemanticAssignment.eq_of_getProperty_eq_some
    {assignment : SemanticAssignment} {opCode : OpCode}
    {handle : Handle OpCode (.prop opCode)} {value : propertiesOf opCode}
    (hget : assignment.getProperty handle = some value) :
    assignment handle.id = some (.property opCode value) := by
  unfold SemanticAssignment.getProperty at hget
  split at hget <;> grind

private theorem SemanticAssignment.forallValues_apply_right
    {ctx ctx' : HandleContext} {handles : List (Handle OpCode .value)}
    {left right : SemanticAssignment} {values : List RuntimeValue}
    {next : List RuntimeValue → SemanticAssignment → Prop}
    (hagrees : AgreeOn ctx left right)
    (hinsert : ctx.insertManyFresh handles = some ctx')
    (hget : right.getValues handles = some values)
    (hmodels : left.forallValues handles next) :
    ∃ final, AgreeOn ctx' final right ∧ next values final := by
  induction handles generalizing ctx ctx' left values next with
  | nil =>
    simp [SemanticAssignment.getValues] at hget
    subst values
    simp [HandleContext.insertManyFresh] at hinsert
    subst ctx'
    exact ⟨left, hagrees, hmodels⟩
  | cons handle handles ih =>
    cases values with
    | nil =>
      unfold SemanticAssignment.getValues at hget
      simp only [List.mapM_cons] at hget
      cases hhead : right.getValue handle <;>
        cases htail : List.mapM right.getValue handles <;>
        simp [hhead, htail] at hget
    | cons value values =>
      simp only [HandleContext.insertManyFresh, List.foldlM_cons] at hinsert
      cases hhead : ctx.insertFresh handle with
      | none => simp [hhead] at hinsert
      | some nextCtx =>
        simp [hhead] at hinsert
        rcases SemanticAssignment.getValues_cons_eq_some hget with ⟨hvalue, hvalues⟩
        simp only [SemanticAssignment.forallValues] at hmodels
        have hraw := SemanticAssignment.eq_of_getValue_eq_some hvalue
        exact ih (ctx := nextCtx) (ctx' := ctx')
          (left := left.bindValue handle value) (values := values)
          (next := fun values final => next (value :: values) final)
          (hagrees.insertFresh_right hhead hraw) hinsert hvalues (hmodels value)

private theorem SemanticAssignment.forallValues_mono
    {assignment : SemanticAssignment} {handles : List (Handle OpCode .value)}
    {first second : List RuntimeValue → SemanticAssignment → Prop}
    (hnext : ∀ values final, first values final → second values final)
    (hmodels : assignment.forallValues handles first) :
    assignment.forallValues handles second := by
  induction handles generalizing assignment first second with
  | nil => exact hnext [] assignment hmodels
  | cons handle handles ih =>
    intro value
    exact ih (fun values final h => hnext (value :: values) final h) (hmodels value)

private theorem SemanticAssignment.forallValues_and
    {assignment : SemanticAssignment} {handles : List (Handle OpCode .value)}
    {first second : List RuntimeValue → SemanticAssignment → Prop}
    (hfirst : assignment.forallValues handles first)
    (hsecond : assignment.forallValues handles second) :
    assignment.forallValues handles fun values final => first values final ∧ second values final := by
  induction handles generalizing assignment first second with
  | nil => exact ⟨hfirst, hsecond⟩
  | cons handle handles ih =>
    intro value
    exact ih (hfirst value) (hsecond value)

private theorem SemanticAssignment.forallValues_realizes
    {ctx ctx' : HandleContext} {handles : List (Handle OpCode .value)}
    {assignment : SemanticAssignment}
    (hrealizes : Realizes ctx assignment)
    (hinsert : ctx.insertManyFresh handles = some ctx') :
    assignment.forallValues handles fun _ final => Realizes ctx' final := by
  induction handles generalizing ctx assignment with
  | nil =>
    simp [SemanticAssignment.forallValues, HandleContext.insertManyFresh] at hinsert ⊢
    subst ctx'
    exact hrealizes
  | cons handle handles ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons] at hinsert
    cases hhead : ctx.insertFresh handle with
    | none => simp [hhead] at hinsert
    | some nextCtx =>
      simp [hhead] at hinsert
      intro value
      exact ih (hrealizes.insertFresh (binding := .value value) trivial hhead) hinsert

private theorem SemanticAssignment.forallValues_generated
    {ctx ctx' : HandleContext} {handles : List (Handle OpCode .value)}
    {left : SemanticAssignment}
    (hinsert : ctx.insertManyFresh handles = some ctx') :
    left.forallValues handles fun values final =>
      ∀ right, AgreeOn ctx' final right →
        AgreeOn ctx left right ∧ right.getValues handles = some values := by
  induction handles generalizing ctx left with
  | nil =>
    simp [SemanticAssignment.forallValues, SemanticAssignment.getValues,
      HandleContext.insertManyFresh] at hinsert ⊢
    subst ctx'
    intro right hagrees
    exact hagrees
  | cons handle handles ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons] at hinsert
    cases hhead : ctx.insertFresh handle with
    | none => simp [hhead] at hinsert
    | some nextCtx =>
      simp [hhead] at hinsert
      simp only [SemanticAssignment.forallValues]
      intro value
      apply SemanticAssignment.forallValues_mono _
        (ih (ctx := nextCtx) (left := left.bindValue handle value) hinsert)
      intro values final hgenerated right hagrees
      rcases hgenerated right hagrees with ⟨hagreesNext, hvalues⟩
      have hagreesOld := hagreesNext.mono (HandleContext.Extends.insertFresh hhead)
      have hheadLookup := HandleContext.lookup_insertFresh_self hhead
      have hvalue : right.getValue handle = some value := by
        rw [← hagreesNext.getValue hheadLookup]
        simp [SemanticAssignment.bindValue, SemanticAssignment.getValue,
          SemanticAssignment.bind]
      constructor
      · intro id kind hlookup hsemantic
        rw [← hagreesOld id kind hlookup hsemantic]
        simp only [SemanticAssignment.bindValue, SemanticAssignment.bind]
        split
        next heq =>
          subst id
          unfold HandleContext.insertFresh at hhead
          split at hhead
          next hnone => rw [hnone] at hlookup; contradiction
          next => contradiction
        next => rfl
      · unfold SemanticAssignment.getValues
        simp only [List.mapM_cons, hvalue]
        unfold SemanticAssignment.getValues at hvalues
        simp [hvalues]

private theorem MatchDecl.models_apply_right
    {ctx ctx' : HandleContext} {decl : MatchDecl OpCode}
    {left right : SemanticAssignment} {next : SemanticAssignment → Prop}
    (hcheck : decl.collectBindings ctx = some ctx')
    (hagrees : SemanticAssignment.AgreeOn ctx left right)
    (hright : decl.ModelsWithAssignment right)
    (hmodels : decl.Models left next) :
    ∃ final, SemanticAssignment.AgreeOn ctx' final right ∧ next final := by
  cases decl with
  | type matcher result =>
    simp only [MatchDecl.collectBindings] at hcheck
    simp only [MatchDecl.ModelsWithAssignment] at hright
    rcases hright with ⟨type, hget, hmatcher⟩
    have hraw := SemanticAssignment.eq_of_getType_eq_some hget
    exact ⟨left.bindType result type,
      hagrees.insertFresh_right hcheck hraw, hmodels type hmatcher⟩
  | value typeHandle result =>
    simp only [MatchDecl.collectBindings, guard] at hcheck
    by_cases hrequire : ctx.require typeHandle = true
    · simp only [hrequire, if_true, pure_bind] at hcheck
      simp only [MatchDecl.ModelsWithAssignment] at hright
      rcases hright with ⟨type, value, htype, hvalue, hconforms⟩
      have hlookup : ctx.lookup typeHandle.id = some .type :=
        (of_decide_eq_true hrequire).1
      have hleftType : left.getType typeHandle = some type := by
        rw [hagrees.getType hlookup, htype]
      simp only [MatchDecl.Models, hleftType] at hmodels
      have hraw := SemanticAssignment.eq_of_getValue_eq_some hvalue
      exact ⟨left.bindValue result value,
        hagrees.insertFresh_right hcheck hraw, hmodels value hconforms⟩
    · simp only [hrequire] at hcheck
      contradiction

  | operation opCode operands resultTypes property propertyHandle opHandle resultHandles nested =>
    simp only [MatchDecl.collectBindings, guard] at hcheck
    by_cases hoperandsRequire : ctx.requireMany operands.toList = true
    · by_cases htypesRequire : ctx.requireMany resultTypes.toList = true
      · simp only [hoperandsRequire, htypesRequire, if_true, pure_bind] at hcheck
        cases hresultsInsert : ctx.insertManyFresh resultHandles.toList with
        | none => simp [hresultsInsert] at hcheck
        | some resultsCtx =>
          simp [hresultsInsert] at hcheck
          cases hpropertyInsert : resultsCtx.insertFresh propertyHandle with
          | none => simp [hpropertyInsert] at hcheck
          | some propertyCtx =>
            simp [hpropertyInsert] at hcheck
            simp only [MatchDecl.ModelsWithAssignment] at hright
            rcases hright with
              ⟨operandValues, actualResultTypes, results, actualProperty,
                hoperands, htypes, hproperty, hresults, hpropertyPred, hinterp⟩
            have hleftOperands : left.getValues operands.toList = some operandValues := by
              rw [hagrees.getValues hoperandsRequire, hoperands]
            have hleftTypes : left.getTypes resultTypes.toList = some actualResultTypes := by
              rw [hagrees.getTypes htypesRequire, htypes]
            simp only [MatchDecl.Models, hleftOperands, hleftTypes] at hmodels
            rcases SemanticAssignment.forallValues_apply_right hagrees hresultsInsert hresults
                (hmodels actualProperty) with ⟨withResults, hagreesResults, hnext⟩
            have hrawProperty := SemanticAssignment.eq_of_getProperty_eq_some hproperty
            have hagreesProperty :=
              hagreesResults.insertFresh_right hpropertyInsert hrawProperty
            have hagreesFinal := hagreesProperty.insertOp hcheck
            exact ⟨withResults.bindProperty propertyHandle actualProperty,
              hagreesFinal, hnext hpropertyPred (by simpa using hinterp)⟩
      · simp only [hoperandsRequire, htypesRequire, if_true] at hcheck
        contradiction
    · simp only [hoperandsRequire] at hcheck
      contradiction
  | @applyNative Inputs inputBundle inputs predicate =>
    simp only [MatchDecl.collectBindings, guard] at hcheck
    by_cases hrequire : inputBundle.shape.requireBindings ctx inputs = true
    · simp only [hrequire, if_true] at hcheck
      simp at hcheck
      subst ctx'
      simp only [MatchDecl.ModelsWithAssignment] at hright
      rcases hright with ⟨values, hrightResolve, hpredicate⟩
      have hleftResolve :
          MetadataTuple.resolveSemantic (self := inputBundle) left inputs = some values := by
        unfold MetadataTuple.resolveSemantic
        rw [MetadataTuple.Shape.resolveSemantic_eq inputBundle.shape inputs hagrees hrequire,
          show inputBundle.shape.resolveSemantic right inputs = some values by
            exact hrightResolve]
      simp only [MatchDecl.Models, hleftResolve] at hmodels
      exact ⟨left, hagrees, hmodels hpredicate⟩
    · simp only [hrequire] at hcheck
      contradiction

private theorem MatchProg.modelsDecls_apply_right
    {decls : List (MatchDecl OpCode)} {ctx ctx' : HandleContext}
    {left right : SemanticAssignment} {next : SemanticAssignment → Prop}
    (hcollect : MatchProg.collectDeclBindings decls ctx = some ctx')
    (hagrees : SemanticAssignment.AgreeOn ctx left right)
    (hright : ∀ decl ∈ decls, decl.ModelsWithAssignment right)
    (hmodels : MatchProg.modelsDecls decls left next) :
    ∃ final, SemanticAssignment.AgreeOn ctx' final right ∧ next final := by
  induction decls generalizing ctx left next with
  | nil =>
    simp only [MatchProg.collectDeclBindings, Option.some.injEq] at hcollect
    subst ctx'
    exact ⟨left, hagrees, hmodels⟩
  | cons decl decls ih =>
    simp only [MatchProg.collectDeclBindings] at hcollect
    cases hdecl : decl.collectBindings ctx with
    | none => simp [hdecl] at hcollect
    | some nextCtx =>
      simp [hdecl] at hcollect
      simp only [MatchProg.modelsDecls] at hmodels
      rcases MatchDecl.models_apply_right hdecl hagrees (hright decl (by simp)) hmodels with
        ⟨afterDecl, hagreesDecl, hrestModels⟩
      have hrightRest : ∀ restDecl ∈ decls, restDecl.ModelsWithAssignment right := by
        intro restDecl hmem
        exact hright restDecl (by simp [hmem])
      exact ih hcollect hagreesDecl hrightRest hrestModels

private theorem SemanticAssignment.Realizes.getProperty
    {ctx : HandleContext} {assignment : SemanticAssignment} {opCode : OpCode}
    {handle : Handle OpCode (.prop opCode)} (hrealizes : Realizes ctx assignment)
    (hlookup : ctx.lookup handle.id = some (.prop opCode)) :
    ∃ value, assignment.getProperty handle = some value := by
  rcases hrealizes handle.id (.prop opCode) hlookup (by simp) with ⟨binding, hbinding, hkind⟩
  cases binding <;> simp [SemanticBinding.HasKind] at hkind
  subst opCode
  rename_i actual value
  exact ⟨value, by simp [SemanticAssignment.getProperty, hbinding]⟩

private theorem MetadataTuple.Shape.resolveSemantic_exists
    {ctx : HandleContext} {assignment : SemanticAssignment}
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles)
    (hrealizes : SemanticAssignment.Realizes ctx assignment)
    (hrequire : shape.requireBindings ctx handles = true) :
    ∃ values, shape.resolveSemantic assignment handles = some values := by
  induction shape with
  | unit => exact ⟨(), rfl⟩
  | atom atom =>
    cases atom with
    | type => exact hrealizes.getType (of_decide_eq_true hrequire).1
    | property op => exact hrealizes.getProperty (of_decide_eq_true hrequire).1
  | cons head tail ih =>
    cases head <;>
      simp only [MetadataTuple.Shape.requireBindings, Bool.and_eq_true] at hrequire
    · obtain ⟨v, hv⟩ := hrealizes.getType (of_decide_eq_true hrequire.1).1
      obtain ⟨vs, hvs⟩ := ih handles.2 hrequire.2
      exact ⟨(v, vs), by simp [MetadataTuple.Shape.resolveSemantic,
        MetadataTuple.Atom.resolveSemantic, hv, hvs]⟩
    · obtain ⟨v, hv⟩ := hrealizes.getProperty (of_decide_eq_true hrequire.1).1
      obtain ⟨vs, hvs⟩ := ih handles.2 hrequire.2
      exact ⟨(v, vs), by simp [MetadataTuple.Shape.resolveSemantic,
        MetadataTuple.Atom.resolveSemantic, hv, hvs]⟩

private theorem MatchDecl.models_generated
    {ctx ctx' : HandleContext} {decl : MatchDecl OpCode} {assignment : SemanticAssignment}
    (hrealizes : SemanticAssignment.Realizes ctx assignment)
    (hcheck : decl.collectBindings ctx = some ctx') :
    decl.Models assignment fun final =>
      SemanticAssignment.Realizes ctx' final ∧
        SemanticAssignment.AgreeOn ctx assignment final ∧
        ∀ right, SemanticAssignment.AgreeOn ctx' final right →
          decl.ModelsWithAssignment right := by
  cases decl with
  | type matcher result =>
    simp only [MatchDecl.collectBindings] at hcheck
    intro type hmatcher
    refine ⟨hrealizes.insertFresh (binding := .type type) trivial hcheck,
      (SemanticAssignment.AgreeOn.bindFresh_preserves
        (assignment := assignment) (binding := .type type) hcheck).symm, ?_⟩
    · intro right hagrees
      refine ⟨type, ?_, hmatcher⟩
      rw [← hagrees.getType (HandleContext.lookup_insertFresh_self hcheck)]
      simp [SemanticAssignment.bindType, SemanticAssignment.getType,
        SemanticAssignment.bind]
  | value typeHandle result =>
    simp only [MatchDecl.collectBindings, guard] at hcheck
    by_cases hrequire : ctx.require typeHandle = true
    · simp only [hrequire, if_true, pure_bind] at hcheck
      have hlookup : ctx.lookup typeHandle.id = some .type :=
        (of_decide_eq_true hrequire).1
      rcases hrealizes.getType hlookup with ⟨type, htype⟩
      simp only [MatchDecl.Models, htype]
      intro value hconforms
      refine ⟨hrealizes.insertFresh (binding := .value value) trivial hcheck,
        (SemanticAssignment.AgreeOn.bindFresh_preserves
          (assignment := assignment) (binding := .value value) hcheck).symm, ?_⟩
      · intro right hagrees
        have hpreserves := SemanticAssignment.AgreeOn.bindFresh_preserves
          (assignment := assignment) (binding := .value value) hcheck
        have hleftRight := hpreserves.symm.trans
          (hagrees.mono (HandleContext.Extends.insertFresh hcheck))
        refine ⟨type, value, ?_, ?_, hconforms⟩
        · rw [← hleftRight.getType hlookup]
          exact htype
        · rw [← hagrees.getValue (HandleContext.lookup_insertFresh_self hcheck)]
          simp [SemanticAssignment.bindValue, SemanticAssignment.getValue,
            SemanticAssignment.bind]
    · simp only [hrequire] at hcheck
      contradiction
  | operation opCode operands resultTypes property propertyHandle opHandle resultHandles nested =>
    simp only [MatchDecl.collectBindings, guard] at hcheck
    by_cases hoperandsRequire : ctx.requireMany operands.toList = true
    · by_cases htypesRequire : ctx.requireMany resultTypes.toList = true
      · simp only [hoperandsRequire, htypesRequire, if_true, pure_bind] at hcheck
        cases hresultsInsert : ctx.insertManyFresh resultHandles.toList with
        | none => simp [hresultsInsert] at hcheck
        | some resultsCtx =>
          simp [hresultsInsert] at hcheck
          cases hpropertyInsert : resultsCtx.insertFresh propertyHandle with
          | none => simp [hpropertyInsert] at hcheck
          | some propertyCtx =>
            simp [hpropertyInsert] at hcheck
            rcases hrealizes.getValues hoperandsRequire with ⟨operandValues, hoperands⟩
            rcases hrealizes.getTypes htypesRequire with ⟨actualResultTypes, htypes⟩
            simp only [MatchDecl.Models, hoperands, htypes]
            intro actualProperty
            apply SemanticAssignment.forallValues_mono _
              (SemanticAssignment.forallValues_and
                (SemanticAssignment.forallValues_realizes hrealizes hresultsInsert)
                (SemanticAssignment.forallValues_generated hresultsInsert))
            intro results withResults hgenerated hpropertyPred hinterp
            rcases hgenerated with ⟨hrealizesResults, hgenerated⟩
            let withProperty := withResults.bindProperty propertyHandle actualProperty
            let final := withProperty
            have hrealizesProperty := hrealizesResults.insertFresh
              (handle := propertyHandle) (binding := .property opCode actualProperty)
              (by simp [SemanticBinding.HasKind]) hpropertyInsert
            have hrealizesFinal := hrealizesProperty.insertOp hcheck
            have hafterWithProperty :
                SemanticAssignment.AgreeOn resultsCtx withResults withProperty :=
              (SemanticAssignment.AgreeOn.bindFresh_preserves
                (assignment := withResults) (binding := .property opCode actualProperty)
                hpropertyInsert).symm
            have hwithPropertyFinal :
                SemanticAssignment.AgreeOn propertyCtx withProperty final :=
              SemanticAssignment.AgreeOn.refl propertyCtx withProperty
            have hresultsFinal := hafterWithProperty.trans
              (hwithPropertyFinal.mono (HandleContext.Extends.insertFresh hpropertyInsert))
            refine ⟨hrealizesFinal, ?_, ?_⟩
            · exact (hgenerated final hresultsFinal).1
            · intro right hagrees
              have hresultsRight := hresultsFinal.trans
                (hagrees.mono ((HandleContext.Extends.insertFresh hpropertyInsert).trans
                  (HandleContext.Extends.insertFresh hcheck)))
              rcases hgenerated right hresultsRight with ⟨hleftRight, hresultValues⟩
              refine ⟨operandValues, actualResultTypes, results.toArray, actualProperty,
                ?_, ?_, ?_, ?_, hpropertyPred, hinterp⟩
              · rw [← hleftRight.getValues hoperandsRequire]
                exact hoperands
              · rw [← hleftRight.getTypes htypesRequire]
                exact htypes
              · have hpropertyLookup := HandleContext.lookup_insertFresh_self hpropertyInsert
                rw [← hagrees.getProperty
                  ((HandleContext.Extends.insertFresh hcheck) propertyHandle.id _ hpropertyLookup)]
                change final.getProperty propertyHandle = some actualProperty
                rw [← hwithPropertyFinal.getProperty hpropertyLookup]
                simp [withProperty, SemanticAssignment.bindProperty,
                  SemanticAssignment.getProperty]
              · simpa using hresultValues
      · simp only [hoperandsRequire, htypesRequire, if_true] at hcheck
        contradiction
    · simp only [hoperandsRequire] at hcheck
      contradiction
  | @applyNative Inputs inputBundle inputs predicate =>
    simp only [MatchDecl.collectBindings, guard] at hcheck
    by_cases hrequire : inputBundle.shape.requireBindings ctx inputs = true
    · simp only [hrequire, if_true] at hcheck
      simp at hcheck
      subst ctx'
      obtain ⟨values, hresolve⟩ :=
        MetadataTuple.Shape.resolveSemantic_exists inputBundle.shape inputs hrealizes hrequire
      simp only [MatchDecl.Models, MetadataTuple.resolveSemantic, hresolve]
      intro hpredicate
      refine ⟨hrealizes, SemanticAssignment.AgreeOn.refl ctx assignment, ?_⟩
      intro right hagrees
      refine ⟨values, ?_, hpredicate⟩
      unfold MetadataTuple.resolveSemantic
      rw [← MetadataTuple.Shape.resolveSemantic_eq inputBundle.shape inputs hagrees hrequire]
      exact hresolve
    · simp only [hrequire] at hcheck
      contradiction

private theorem MatchDecl.models_mono
    {decl : MatchDecl OpCode} {assignment : SemanticAssignment}
    {first second : SemanticAssignment → Prop}
    (hnext : ∀ final, first final → second final)
    (hmodels : decl.Models assignment first) : decl.Models assignment second := by
  cases decl with
  | type matcher result =>
    intro type hmatcher
    exact hnext _ (hmodels type hmatcher)
  | value typeHandle result =>
    cases htype : assignment.getType typeHandle with
    | none =>
      simp only [MatchDecl.Models, htype] at hmodels ⊢
    | some type =>
      simp only [MatchDecl.Models, htype] at hmodels ⊢
      intro value hconforms
      exact hnext _ (hmodels value hconforms)
  | operation opCode operands resultTypes property propertyHandle opHandle resultHandles nested =>
    cases hoperands : assignment.getValues operands.toList <;>
      cases htypes : assignment.getTypes resultTypes.toList
    all_goals simp [MatchDecl.Models, hoperands, htypes] at hmodels ⊢
    next operandValues actualResultTypes =>
      intro actualProperty
      apply SemanticAssignment.forallValues_mono _ (hmodels actualProperty)
      intro results final h hproperty hinterp
      exact hnext _ (h hproperty hinterp)
  | applyNative inputs predicate =>
    cases hresolve : MetadataTuple.resolveSemantic assignment inputs <;>
      simp only [MatchDecl.Models, hresolve] at hmodels ⊢
    intro hpredicate
    exact hnext _ (hmodels hpredicate)

private theorem MatchProg.modelsDecls_mono
    {decls : List (MatchDecl OpCode)} {assignment : SemanticAssignment}
    {first second : SemanticAssignment → Prop}
    (hnext : ∀ final, first final → second final)
    (hmodels : MatchProg.modelsDecls decls assignment first) :
    MatchProg.modelsDecls decls assignment second := by
  induction decls generalizing assignment first second with
  | nil => exact hnext _ hmodels
  | cons decl decls ih =>
    simp only [MatchProg.modelsDecls] at hmodels ⊢
    apply MatchDecl.models_mono _ hmodels
    intro afterDecl hrest
    exact ih hnext hrest

private theorem MatchProg.modelsDecls_generated
    {decls : List (MatchDecl OpCode)} {ctx ctx' : HandleContext}
    {assignment : SemanticAssignment}
    (hrealizes : SemanticAssignment.Realizes ctx assignment)
    (hcollect : MatchProg.collectDeclBindings decls ctx = some ctx') :
    MatchProg.modelsDecls decls assignment fun final =>
      SemanticAssignment.Realizes ctx' final ∧
        SemanticAssignment.AgreeOn ctx assignment final ∧
        (∀ decl ∈ decls, decl.ModelsWithAssignment final) := by
  induction decls generalizing ctx assignment with
  | nil =>
    simp only [MatchProg.collectDeclBindings, Option.some.injEq] at hcollect
    subst ctx'
    exact ⟨hrealizes, SemanticAssignment.AgreeOn.refl ctx assignment, by simp⟩
  | cons decl decls ih =>
    simp only [MatchProg.collectDeclBindings] at hcollect
    cases hdecl : decl.collectBindings ctx with
    | none => simp [hdecl] at hcollect
    | some nextCtx =>
      simp [hdecl] at hcollect
      simp only [MatchProg.modelsDecls]
      apply MatchDecl.models_mono _ (MatchDecl.models_generated hrealizes hdecl)
      intro afterDecl hgeneratedDecl
      rcases hgeneratedDecl with ⟨hrealizesDecl, hagreesDecl, hdeclModel⟩
      apply MatchProg.modelsDecls_mono _ (ih hrealizesDecl hcollect)
      intro final hgeneratedRest
      rcases hgeneratedRest with ⟨hrealizesFinal, hagreesRest, hrestModels⟩
      refine ⟨hrealizesFinal,
        hagreesDecl.trans (hagreesRest.mono (MatchDecl.collectBindings_extends hdecl)), ?_⟩
      intro matchedDecl hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hdeclModel final hagreesRest
      · exact hrestModels matchedDecl hmem

private theorem SemanticAssignment.bindValues_isSome
    (left right : SemanticAssignment) (handles : List (Handle OpCode .value))
    (values : List RuntimeValue) :
    (left.bindValues handles values).isSome = (right.bindValues handles values).isSome := by
  induction handles generalizing left right values with
  | nil => cases values <;> rfl
  | cons handle handles ih =>
    cases values with
    | nil => rfl
    | cons value values => exact ih _ _ _

/-- Binding disjoint handles commutes, independently of their kinds. -/
theorem SemanticAssignment.bind_comm (assignment : SemanticAssignment)
    (first second : Nat) (a b : SemanticBinding) (hne : first ≠ second) :
    (assignment.bind first a).bind second b = (assignment.bind second b).bind first a := by
  funext id
  simp only [SemanticAssignment.bind]
  grind

/-- Fresh result handles differ from all previously allocated handles. -/
private theorem HandleContext.insertManyFresh_ne_bound
    {ctx ctx' : HandleContext} {handles : List (Handle OpCode .value)}
    {id : Nat} {kind : HandleType OpCode}
    (hinsert : ctx.insertManyFresh handles = some ctx')
    (hlookup : ctx.lookup id = some kind) : ∀ handle ∈ handles, handle.id ≠ id := by
  induction handles generalizing ctx with
  | nil => simp
  | cons handle handles ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons] at hinsert
    cases hhead : ctx.insertFresh handle with
    | none => simp [hhead] at hinsert
    | some nextCtx =>
      simp [hhead] at hinsert
      have hne : handle.id ≠ id := by
        intro heq
        simp [HandleContext.insertFresh, heq, hlookup] at hhead
      have htail := ih hinsert ((HandleContext.Extends.insertFresh hhead) id kind hlookup)
      simpa using And.intro hne htail

private theorem CreateDecl.eval_agrees
    {ctx ctx' : HandleContext} {decl : CreateDecl OpCode}
    {left right : SemanticAssignment}
    (hagrees : SemanticAssignment.AgreeOn ctx left right)
    (hcheck : decl.checkBindings ctx = some ctx') :
    Option.Rel (SemanticAssignment.AgreeOn ctx') (decl.eval left) (decl.eval right) := by
  cases decl with
  | type value result =>
    simp only [CreateDecl.checkBindings] at hcheck
    simp only [CreateDecl.eval]
    exact .some (hagrees.insertFresh hcheck)
  | property opCode value result =>
    simp only [CreateDecl.checkBindings] at hcheck
    simp only [CreateDecl.eval]
    exact .some (hagrees.insertFresh hcheck)
  | operation opCode operands resultTypes property opHandle resultHandles =>
    simp only [CreateDecl.checkBindings] at hcheck
    simp only [CreateDecl.eval]
    simp only [guard] at hcheck
    by_cases hoperands : ctx.requireMany operands.toList = true
    · by_cases htypes : ctx.requireMany resultTypes.toList = true
      · by_cases hproperty : ctx.require property = true
        · by_cases hsize : resultHandles.size = resultTypes.size
          · simp only [hoperands, htypes, hproperty, hsize, if_true, pure_bind] at hcheck
            have hpropertyLookup : ctx.lookup property.id = some (.prop opCode) :=
              (of_decide_eq_true hproperty).1
            rw [hagrees.getValues hoperands, hagrees.getTypes htypes,
              hagrees.getProperty hpropertyLookup]
            cases hop : ctx.insertFresh opHandle with
            | none => simp [hop] at hcheck
            | some nextCtx =>
              simp [hop] at hcheck
              cases hvalues : right.getValues operands.toList <;>
                cases hresultTypes : right.getTypes resultTypes.toList <;>
                cases hprop : right.getProperty property <;> simp_all
              rename_i values actualResultTypes actualProperty
              cases hinterp : interpretOp' opCode actualProperty actualResultTypes.toArray
                values.toArray #[] .empty
              next => exact .none
              next => exact .none
              next result =>
                rcases result with ⟨results, memory, action⟩
                cases action
                next =>
                  dsimp only
                  by_cases hsem : InterpretsTo opCode actualProperty actualResultTypes.toArray
                    values.toArray results
                  case neg => simpa only [if_neg hsem] using
                      (Option.Rel.none : Option.Rel (SemanticAssignment.AgreeOn ctx') none none)
                  simp only [if_pos hsem]
                  cases hleft : left.bindValues
                    resultHandles.toList results.toList with
                  | none =>
                    have hright : right.bindValues
                        resultHandles.toList results.toList = none := by
                      have hs := SemanticAssignment.bindValues_isSome
                        left right
                        resultHandles.toList results.toList
                      rw [hleft] at hs
                      simpa using hs
                    simp [hright]
                  | some left' =>
                    have hrightSome :
                        (right.bindValues resultHandles.toList
                          results.toList).isSome = true := by
                      rw [← SemanticAssignment.bindValues_isSome
                        left right]
                      simp [hleft]
                    rcases Option.isSome_iff_exists.mp hrightSome with ⟨right', hright⟩
                    simp [hright]
                    apply SemanticAssignment.AgreeOn.insertManyFresh
                      (hagrees.insertOp hop) hcheck hleft hright
                next => exact .none
          · simp only [hoperands, htypes, hproperty, hsize, if_true, if_false] at hcheck
            change none = some ctx' at hcheck
            contradiction
        · simp only [hoperands, htypes, hproperty, if_true] at hcheck
          change none = some ctx' at hcheck
          contradiction
      · simp only [hoperands, htypes, if_true] at hcheck
        change none = some ctx' at hcheck
        contradiction
    · simp only [hoperands] at hcheck
      change none = some ctx' at hcheck
      contradiction
  | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
    simp only [CreateDecl.checkBindings, guard] at hcheck
    by_cases hrequire : inputBundle.shape.requireBindings ctx inputs = true
    · simp only [hrequire, if_true] at hcheck
      simp only [CreateDecl.eval, MetadataTuple.resolveSemantic, MetadataTuple.bindSemantic]
      rw [MetadataTuple.Shape.resolveSemantic_eq inputBundle.shape inputs hagrees hrequire]
      cases hresolve : inputBundle.shape.resolveSemantic right inputs with
      | none => simp
      | some inputValues =>
        simp
        cases hrewrite : rewrite inputValues with
        | none => simp
        | some outputValues =>
          simp
          exact MetadataTuple.Shape.bindSemantic_rel outputBundle.shape outputs outputValues
            hagrees hcheck
    · simp only [hrequire] at hcheck
      contradiction

private theorem CreateProg.evalDecls_agrees
    {ctx ctx' : HandleContext} {decls : List (CreateDecl OpCode)}
    {left right : SemanticAssignment}
    (hagrees : SemanticAssignment.AgreeOn ctx left right)
    (hcheck : decls.foldlM CreateDecl.checkBindings ctx = some ctx') :
    Option.Rel (SemanticAssignment.AgreeOn ctx')
      (CreateProg.evalDecls decls left) (CreateProg.evalDecls decls right) := by
  induction decls generalizing ctx left right with
  | nil =>
    change some ctx = some ctx' at hcheck
    injection hcheck with hctx
    subst ctx'
    exact .some hagrees
  | cons decl decls ih =>
    simp only [CreateProg.evalDecls, List.foldlM_cons] at hcheck ⊢
    cases hdeclCheck : decl.checkBindings ctx with
    | none => simp [hdeclCheck] at hcheck
    | some nextCtx =>
      simp [hdeclCheck] at hcheck
      have hdeclEval := CreateDecl.eval_agrees hagrees hdeclCheck
      generalize hleft : decl.eval left = leftEval at hdeclEval ⊢
      generalize hright : decl.eval right = rightEval at hdeclEval ⊢
      cases leftEval <;> cases rightEval <;> cases hdeclEval
      · exact .none
      · exact ih ‹SemanticAssignment.AgreeOn _ _ _› hcheck

private theorem Replacement.refinesRoot_congr
    {matcherCtx finalCtx : HandleContext} {replacement : Replacement OpCode}
    {root : Option (Array (Handle OpCode .value))}
    {matchedLeft matchedRight finalLeft finalRight : SemanticAssignment}
    (hmatched : SemanticAssignment.AgreeOn matcherCtx matchedLeft matchedRight)
    (hroot : ∀ handles, root = some handles →
      ∀ handle ∈ handles.toList, matcherCtx.lookup handle.id = some .value)
    (hfinal : SemanticAssignment.AgreeOn finalCtx finalLeft finalRight)
    (hreplacement : finalCtx.requireMany replacement.values.toList = true) :
    replacement.refinesRoot root matchedLeft finalLeft ↔
      replacement.refinesRoot root matchedRight finalRight := by
  have hvalues (handles : List (Handle OpCode .value))
      (hlookup : ∀ handle ∈ handles, matcherCtx.lookup handle.id = some .value) :
      matchedLeft.getValues handles = matchedRight.getValues handles := by
    induction handles with
    | nil => rfl
    | cons handle handles ih =>
      simp only [SemanticAssignment.getValues, List.mapM_cons]
      rw [hmatched.getValue (hlookup handle (by simp))]
      have htail := ih (by intro h hm; exact hlookup h (by simp [hm]))
      unfold SemanticAssignment.getValues at htail
      rw [htail]
  unfold Replacement.refinesRoot
  rw [hfinal.getValues hreplacement]
  cases root with
  | none => rfl
  | some handles => simp only [Option.bind_some, hvalues handles.toList (hroot handles rfl)]

private theorem SemanticAssignment.existsValues_iff
    (assignment : SemanticAssignment) (handles : List (Handle OpCode .value))
    (next : List RuntimeValue → SemanticAssignment → Prop) :
    assignment.existsValues handles next ↔
      ∃ values final, assignment.bindValues handles values = some final ∧ next values final := by
  induction handles generalizing assignment next with
  | nil =>
    constructor
    · intro h
      exact ⟨[], assignment, rfl, h⟩
    · rintro ⟨values, final, hbind, hnext⟩
      cases values <;> simp [SemanticAssignment.bindValues] at hbind
      subst final
      exact hnext
  | cons handle handles ih =>
    simp only [SemanticAssignment.existsValues]
    constructor
    · rintro ⟨value, hrest⟩
      rcases (ih (assignment.bindValue handle value)
        (fun values assignment => next (value :: values) assignment)).mp hrest with
        ⟨values, final, hbind, hnext⟩
      exact ⟨value :: values, final, hbind, hnext⟩
    · rintro ⟨values, final, hbind, hnext⟩
      cases values with
      | nil => simp [SemanticAssignment.bindValues] at hbind
      | cons value values =>
        refine ⟨value, (ih (assignment.bindValue handle value)
          (fun values assignment => next (value :: values) assignment)).mpr ?_⟩
        exact ⟨values, final, hbind, hnext⟩

private theorem CreateDecl.models_iff_eval
    (decl : CreateDecl OpCode) (assignment : SemanticAssignment)
    (next : SemanticAssignment → Prop) :
    decl.Models assignment next ↔
      ∃ final, decl.eval assignment = some final ∧ next final := by
  cases decl with
  | type value result => simp [CreateDecl.Models, CreateDecl.eval]
  | property opCode value result => simp [CreateDecl.Models, CreateDecl.eval]
  | operation opCode operands resultTypes property opHandle resultHandles =>
    simp only [CreateDecl.Models, CreateDecl.eval]
    cases hoperands : assignment.getValues operands.toList <;>
      cases htypes : assignment.getTypes resultTypes.toList <;>
      cases hproperty : assignment.getProperty property <;> simp_all
    rename_i operandValues actualResultTypes actualProperty
    rw [SemanticAssignment.existsValues_iff]
    constructor
    · rintro ⟨values, generated, hgenerated, hsem, hnext⟩
      refine ⟨generated, ?_, hnext⟩
      simp [hsem.2 .empty, hsem, hgenerated]
    · rintro ⟨final, heval, hnext⟩
      cases hi : interpretOp' opCode actualProperty actualResultTypes.toArray
          operandValues.toArray #[] .empty with
      | fail => simp [hi] at heval
      | ub => simp [hi] at heval
      | ok output =>
        rcases output with ⟨results, memory, action⟩
        cases action with
        | some action => simp [hi] at heval
        | none =>
          by_cases hs : InterpretsTo opCode actualProperty actualResultTypes.toArray
            operandValues.toArray results
          · cases hb : assignment.bindValues resultHandles.toList results.toList with
            | none => simp [hi, hs, hb] at heval
            | some generated =>
              simp [hi, hs, hb] at heval
              subst final
              exact ⟨results.toList, generated, hb, by simpa using hs, hnext⟩
          · simp [hi, hs] at heval
  | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
    simp only [CreateDecl.Models, CreateDecl.eval]
    cases hinput : MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs with
    | none => simp
    | some inputValues =>
      simp
      cases rewrite inputValues <;> simp

private theorem CreateProg.modelsDecls_iff_evalDecls
    (decls : List (CreateDecl OpCode)) (assignment : SemanticAssignment)
    (next : SemanticAssignment → Prop) :
    CreateProg.modelsDecls decls assignment next ↔
      ∃ final, CreateProg.evalDecls decls assignment = some final ∧ next final := by
  induction decls generalizing assignment next with
  | nil => simp [CreateProg.modelsDecls, CreateProg.evalDecls]
  | cons decl decls ih =>
    simp only [CreateProg.modelsDecls]
    simp only [ih]
    rw [CreateDecl.models_iff_eval]
    cases hdecl : CreateDecl.eval assignment decl <;>
      simp [CreateProg.evalDecls, List.foldlM_cons, hdecl, and_comm]

@[simp] theorem MatchProg.mem_bindingDecls {prog : MatchProg OpCode α}
    {decl : MatchDecl OpCode} : decl ∈ prog.bindingDecls ↔ decl ∈ prog.decls := by
  cases decl <;> simp [MatchProg.bindingDecls, List.partition_eq_filter_filter]

private theorem Pattern.structure_components
    {rule : Pattern OpCode} (hstructure : rule.StructurallyWellFormed) :
    ∃ rootResults matcherCtx finalCtx,
      rule.matcher.rootResults? = some rootResults ∧
      MatchProg.collectDeclBindings rule.matcher.bindingDecls .empty = some matcherCtx ∧
      rule.creation.checkBindings
          ((matcherCtx.forbid rule.matcher.rootHandle).forbidMany rootResults.toList) =
        some finalCtx ∧
      rule.replacement.checkBindings finalCtx = true := by
  unfold Pattern.StructurallyWellFormed at hstructure
  rcases Option.isSome_iff_exists.mp hstructure with ⟨checkedCtx, hcheck⟩
  simp only [Pattern.checkStructure, MatchProg.collectBindings] at hcheck
  cases hroot : rule.matcher.rootResults? with
  | none => simp [hroot] at hcheck
  | some rootResults =>
    simp [hroot] at hcheck
    cases hmatcher : MatchProg.collectDeclBindings rule.matcher.bindingDecls .empty with
    | none => simp [hmatcher] at hcheck
    | some matcherCtx =>
      simp [hmatcher] at hcheck
      cases hcreation : rule.creation.checkBindings
          ((matcherCtx.forbid rule.matcher.rootHandle).forbidMany rootResults.toList) with
      | none => simp [hcreation] at hcheck
      | some finalCtx =>
        simp [hcreation] at hcheck
        by_cases hreplacement : rule.replacement.checkBindings finalCtx = true
        · simp [hreplacement] at hcheck
          exact ⟨rootResults, matcherCtx, finalCtx, rfl, rfl, hcreation, hreplacement⟩
        · simp [guard, hreplacement] at hcheck
          change none = some checkedCtx at hcheck
          contradiction

/-- The generated author-facing proposition is equivalent to assignment-quantified preservation
for every structurally well-formed pattern. -/
theorem Pattern.preservesSemantics_iff_withAssignment
    {rule : Pattern OpCode} (hstructure : rule.StructurallyWellFormed) :
    rule.PreservesSemantics ↔ rule.PreservesSemanticsWithAssignment := by
  rcases Pattern.structure_components hstructure with
    ⟨rootResults, matcherCtx, finalCtx, hrootResults, hmatcher, hcreation, hreplacement⟩
  have hrootLookup : ∀ handles, rule.matcher.rootResults? = some handles →
      ∀ result ∈ handles.toList, matcherCtx.lookup result.id = some .value := by
    intro handles hhandles result hmem
    rw [hrootResults] at hhandles
    cases Option.some.inj hhandles
    unfold MatchProg.rootResults? at hrootResults
    cases hdecls : rule.matcher.decls with
    | nil => simp [hdecls] at hrootResults
    | cons rootDecl rest =>
      cases rootDecl with
      | operation opCode operands resultTypes property propertyHandle opHandle results nested =>
        simp only [hdecls] at hrootResults
        split at hrootResults
        next heq =>
          simp only [Option.some.injEq] at hrootResults
          subst rootResults
          subst opHandle
          apply MatchProg.collectDeclBindings_lookup_result
            (decl := .operation opCode operands resultTypes property propertyHandle
              rule.matcher.rootHandle results nested) hmatcher
          · apply MatchProg.mem_bindingDecls.mpr
            simp [hdecls]
          · exact ⟨opCode, operands, resultTypes, property, propertyHandle,
              rule.matcher.rootHandle, results, nested, rfl, hmem⟩
        next => contradiction
      | value => simp [hdecls] at hrootResults
      | type => simp [hdecls] at hrootResults
      | applyNative => simp [hdecls] at hrootResults
  constructor
  · intro hgenerated assignment hmodels
    unfold Pattern.PreservesSemantics at hgenerated
    unfold MatchProg.Models at hgenerated
    have hright : ∀ decl ∈ rule.matcher.bindingDecls,
        decl.ModelsWithAssignment assignment := by
      intro decl hmem
      exact hmodels decl (MatchProg.mem_bindingDecls.mp hmem)
    rcases MatchProg.modelsDecls_apply_right hmatcher
        (SemanticAssignment.AgreeOn.empty SemanticAssignment.empty assignment)
        hright hgenerated with
      ⟨matched, hagreesMatched, hcreationModels⟩
    have hagreesCreation :=
      (hagreesMatched.forbid rule.matcher.rootHandle).forbidMany rootResults.toList
    unfold CreateProg.Models at hcreationModels
    rcases (CreateProg.modelsDecls_iff_evalDecls rule.creation.decls matched
      (fun final => rule.replacement.refinesRoot rule.matcher.rootResults? matched final)).mp
        hcreationModels with ⟨generatedFinal, hevalGenerated, hrefines⟩
    have hevalAgrees := CreateProg.evalDecls_agrees hagreesCreation hcreation
    cases hevalAssignment : CreateProg.evalDecls rule.creation.decls assignment with
    | none => simp [hevalGenerated, hevalAssignment] at hevalAgrees
    | some assignmentFinal =>
      have hagreesFinal : SemanticAssignment.AgreeOn finalCtx generatedFinal assignmentFinal := by
        simpa [hevalGenerated, hevalAssignment] using hevalAgrees
      refine ⟨assignmentFinal, rfl, ?_⟩
      exact (Replacement.refinesRoot_congr hagreesMatched hrootLookup hagreesFinal
        hreplacement).mp hrefines
  · intro hwithAssignment
    unfold Pattern.PreservesSemantics
    unfold MatchProg.Models
    apply MatchProg.modelsDecls_mono _
      (MatchProg.modelsDecls_generated SemanticAssignment.Realizes.empty hmatcher)
    intro matched hgenerated
    rcases hgenerated with ⟨_, _, hmodels⟩
    have hmodelsOriginal : rule.matcher.ModelsWithAssignment matched := by
      intro decl hmem
      exact hmodels decl (MatchProg.mem_bindingDecls.mpr hmem)
    rcases hwithAssignment matched hmodelsOriginal with ⟨final, heval, hrefines⟩
    unfold CreateProg.Models
    exact (CreateProg.modelsDecls_iff_evalDecls rule.creation.decls matched
      (fun final => rule.replacement.refinesRoot rule.matcher.rootResults? matched final)).mpr
        ⟨final, heval, hrefines⟩

end

end Veir.Puddle
