module

public import Veir.PatternRewriter.Puddle.MatcherSemantics
public import Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.PatternRewriter.Puddle.MatcherSemantics
import all Veir.PatternRewriter.Puddle.CTreeValidity

namespace Veir.Puddle

public section

/-- Equal updates preserve agreement on every available handle after fresh insertion. -/
theorem HandleContext.AgreesOn.bind_both_insertFresh {before after : HandleContext}
    {a b : SemanticAssignment} {kind : HandleType OpCode} {handle : Handle OpCode kind}
    (agree : before.AgreesOn [] a b) (inserted : before.insertFresh handle = some after)
    (binding : SemanticBinding) :
    after.AgreesOn [] (a.bind handle.id binding) (b.bind handle.id binding) := by
  intro k queried hnot havail _
  by_cases heq : queried.id = handle.id
  · simp [SemanticAssignment.bind, heq]
  · have havail' : before.require queried = true := by
      rw [← HandleContext.require_of_insertFresh_of_ne inserted heq]
      exact havail
    simpa [SemanticAssignment.bind, heq] using agree k queried hnot havail' (by simp)

/-- Adding a fresh operation handle does not change semantic agreement. -/
theorem HandleContext.AgreesOn.insertFresh_op {before after : HandleContext}
    {a b : SemanticAssignment} {handle : Handle OpCode .op}
    (agree : before.AgreesOn [] a b) (inserted : before.insertFresh handle = some after) :
    after.AgreesOn [] a b := by
  intro k queried hnot havail _
  have hne : queried.id ≠ handle.id := by
    intro heq
    have hk := HandleContext.lookup_of_insertFresh inserted
    simp only [HandleContext.require, decide_eq_true_eq] at havail
    have hl := havail.1
    rw [heq, hk] at hl
    exact hnot (Option.some.inj hl).symm
  exact agree k queried hnot
    (by simpa only [HandleContext.require_of_insertFresh_of_ne inserted hne] using havail) (by simp)

/-- Equal result arrays extend semantic agreement through fresh result-handle allocation. -/
theorem HandleContext.AgreesOn.bindValues_insertManyFresh {before after : HandleContext}
    {a b : SemanticAssignment} (handles : List (Handle OpCode .value))
    (agree : before.AgreesOn [] a b) (inserted : before.insertManyFresh handles = some after)
    (values : Array RuntimeValue) (index : Nat := 0) (types : Array TypeAttr := #[]) :
    after.AgreesOn [] (SemanticAssignment.bindValues values a handles index types)
      (SemanticAssignment.bindValues values b handles index types) := by
  induction handles generalizing before a b index with
  | nil =>
    simp only [HandleContext.insertManyFresh, List.foldlM_nil, Option.pure_def, Option.some.injEq] at inserted
    subst after
    exact agree
  | cons handle handles ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at inserted
    obtain ⟨middle, hh, ht⟩ := inserted
    exact ih (agree.bind_both_insertFresh hh (.value values[index]! types[index]?)) ht (index + 1)

/-- Metadata tuple inputs observe only their statically required handles. -/
theorem MetadataTuple.Shape.resolveSemantic_agreesOn
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles)
    {ctx : HandleContext} {a b : SemanticAssignment} (agree : ctx.AgreesOn [] a b)
    (required : shape.requireBindings ctx handles = true) :
    shape.resolveSemantic a handles = shape.resolveSemantic b handles := by
  apply shape.resolveSemantic_eq_of_agreesOn handles required ?_ agree
  induction shape with
  | unit => trivial
  | atom atom => cases atom <;> simp [MetadataTuple.Shape.Avoids]
  | cons head tail ih => cases head <;> simp_all [MetadataTuple.Shape.Avoids, MetadataTuple.Shape.requireBindings]

/-- Equal metadata outputs extend agreement through fresh output allocation. -/
theorem MetadataTuple.Shape.bindSemantic_agreesOn
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {before after : HandleContext} {a b : SemanticAssignment} (agree : before.AgreesOn [] a b)
    (inserted : shape.insertFreshBindings before handles = some after) :
    after.AgreesOn [] (shape.bindSemantic a handles values) (shape.bindSemantic b handles values) := by
  induction shape generalizing before a b with
  | unit => cases inserted; exact agree
  | atom atom =>
    cases atom <;> exact agree.bind_both_insertFresh inserted _
  | cons head tail ih =>
    cases head <;>
      simp only [MetadataTuple.Shape.insertFreshBindings, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at inserted
    all_goals
      obtain ⟨middle, hh, ht⟩ := inserted
      exact ih _ _ (agree.bind_both_insertFresh hh _) ht

/-- A structurally checked creation declaration observes only available inputs and gives its
continuation assignments that still agree on all available outputs. -/
theorem CTree.CreateDecl.semantics_congr
    (decl : CreateDecl OpCode) {before after : HandleContext} {a b : SemanticAssignment}
    (checked : decl.checkBindings before = some after) (agree : before.AgreesOn [] a b)
    (memory : MemoryState) (next next' : SemanticAssignment → MemoryState → Tree α)
    (hnext : ∀ a b m, after.AgreesOn [] a b → next a m = next' b m) :
    CTree.CreateDecl.semantics decl a memory next = CTree.CreateDecl.semantics decl b memory next' := by
  cases decl with
  | type value result =>
    exact hnext _ _ memory (agree.bind_both_insertFresh checked _)
  | property code value result =>
    exact hnext _ _ memory (agree.bind_both_insertFresh checked _)
  | operation code operands types property op results =>
    simp only [CreateDecl.checkBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨u₁, hoper, u₂, htypes, u₃, hprop, u₄, _, middle, hop, hresults⟩ := checked
    have hoper' : before.requireMany operands.toList = true := by simpa [guard] using hoper
    have htypes' : before.requireMany types.toList = true := by simpa [guard] using htypes
    have hprop' : before.require property = true := by simpa [guard] using hprop
    have ho := agree.getValues operands.toList hoper' (by simp)
    have ht := agree.getTypes types.toList htypes' (by simp)
    have hp := agree.getProperty property hprop' (by simp)
    simp only [CTree.CreateDecl.semantics, ho, ht, hp]
    split
    · congr 1
      funext result
      rcases result with ⟨values, memory', action⟩
      exact hnext _ _ memory'
        ((agree.insertFresh_op hop).bindValues_insertManyFresh results.toList hresults values (types := _))
    · rfl
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.checkBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨u, hrequired, houtputs⟩ := checked
    have hrequired' := hrequired
    simp only [guard] at hrequired'
    have hread : MetadataTuple.resolveSemantic a inputs = MetadataTuple.resolveSemantic b inputs := by
      exact MetadataTuple.Shape.resolveSemantic_agreesOn _ _ agree (by simpa [guard] using hrequired)
    simp only [CTree.CreateDecl.semantics, hread]
    split
    · rfl
    · rename_i values hvalues
      exact hnext _ _ memory (MetadataTuple.Shape.bindSemantic_agreesOn _ _ values agree houtputs)

/-- CPS creation-list semantics is insensitive to unavailable or unused initial slots. -/
theorem CTree.CreateProg.semanticsDecls_congr
    (decls : List (CreateDecl OpCode)) {before after : HandleContext} {a b : SemanticAssignment}
    (checked : decls.foldlM CreateDecl.checkBindings before = some after)
    (agree : before.AgreesOn [] a b) (memory : MemoryState)
    (next next' : SemanticAssignment → MemoryState → Tree α)
    (hnext : ∀ a b m, after.AgreesOn [] a b → next a m = next' b m) :
    CTree.CreateProg.semanticsDecls decls a memory next =
      CTree.CreateProg.semanticsDecls decls b memory next' := by
  induction decls generalizing before a b memory with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at checked
    subst after
    exact hnext _ _ memory agree
  | cons decl decls ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨middle, hd, hr⟩ := checked
    exact CTree.CreateDecl.semantics_congr decl hd agree memory _ _
      (fun a b m hab => ih hr hab m)

/-- A checked creation program and replacement observe only statically available slots. -/
theorem CTree.CreateProg.semantics_congr
    (prog : CreateProg OpCode β) (replacement : Replacement OpCode)
    {before after : HandleContext} {a b : SemanticAssignment}
    (checked : prog.checkBindings before = some after)
    (required : replacement.checkBindings after = true)
    (agree : before.AgreesOn [] a b) (memory : MemoryState) :
    CTree.CreateProg.semantics prog replacement a memory =
      CTree.CreateProg.semantics prog replacement b memory := by
  apply CTree.CreateProg.semanticsDecls_congr prog.decls checked agree memory
  intro a b m hab
  have hv := hab.getValues replacement.values.toList required (by simp)
  rw [hv]

end

end Veir.Puddle
