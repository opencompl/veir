module

public import Veir.PatternRewriter.Puddle.CreationOperationSemantics
import all Veir.PatternRewriter.Puddle.CreationOperationSemantics
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.IR.Basic

public section

namespace Veir.Puddle

/-- Pointer-bearing bindings refer to entities in the context. -/
def Binding.InBounds (binding : Binding OpCode) (ctx : IRContext OpCode) : Prop :=
  match binding with
  | .op operation => operation.InBounds ctx
  | .value pointer => pointer.InBounds ctx
  | _ => True

/-- Every populated assignment slot contains a valid pointer or metadata. -/
def Assignment.InBounds (a : Assignment OpCode) (ctx : IRContext OpCode) : Prop :=
  ∀ (id : Nat) (binding : Binding OpCode),
    a.bindings[id]?.join = some binding → binding.InBounds ctx

theorem Assignment.InBounds.values {a : Assignment OpCode} {ctx : IRContext OpCode}
    (h : a.InBounds ctx) : a.ValuesInBounds ctx := by
  intro id pointer hb
  exact h id (.value pointer) hb

theorem Assignment.empty_inBounds (size : Nat) (ctx : IRContext OpCode) :
    (Assignment.empty OpCode size).InBounds ctx := by
  intro id binding hb
  by_cases hi : id < size <;>
    simp [Assignment.empty, hi] at hb

theorem Assignment.InBounds.bind {a b : Assignment OpCode} {ctx : IRContext OpCode}
    {kind : HandleType OpCode} {handle : Handle OpCode kind} {binding : Binding OpCode}
    (ha : a.InBounds ctx) (h : a.bind handle binding = some b)
    (hb : binding.InBounds ctx) : b.InBounds ctx := by
  intro id existing he
  let other : Handle OpCode .type := ⟨id⟩
  change b.getBinding other = some existing at he
  by_cases heq : other.id = handle.id
  · have installed := Assignment.getBinding_of_bind h
    have eqBinding : binding = existing := by
      have : b.getBinding other = some binding := by
        simpa [Assignment.getBinding, heq] using installed
      exact Option.some.inj (this.symm.trans he)
    exact eqBinding ▸ hb
  · rw [Assignment.getBinding_of_bind_of_ne other h heq] at he
    exact ha id existing he

theorem Assignment.InBounds.getOp {a : Assignment OpCode} {ctx : IRContext OpCode}
    (ha : a.InBounds ctx) {handle : Handle OpCode .op} {op : OperationPtr}
    (h : a.getOp handle = some op) : op.InBounds ctx := by
  unfold Assignment.getOp at h
  split at h <;> try contradiction
  cases h
  exact ha handle.id _ (by assumption)

theorem Assignment.InBounds.getValue {a : Assignment OpCode} {ctx : IRContext OpCode}
    (ha : a.InBounds ctx) {handle : Handle OpCode .value} {value : ValuePtr}
    (h : a.getValue handle = some value) : value.InBounds ctx := by
  unfold Assignment.getValue at h
  split at h <;> try contradiction
  cases h
  exact ha handle.id _ (by assumption)

theorem Assignment.InBounds.findOp {a : Assignment OpCode} {ctx : WfIRContext OpCode}
    (ha : a.InBounds ctx.raw) {handle : Handle OpCode .op}
    {results : Array (Handle OpCode .value)} {op : OperationPtr}
    (h : a.findOp handle results = some op) : op.InBounds ctx.raw := by
  unfold Assignment.findOp at h
  split at h
  · cases h
    exact ha.getOp (by assumption)
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨value, hvalue, h⟩ := h
    obtain ⟨result, _, hresult⟩ := Array.exists_of_findSome?_eq_some hvalue
    have hv := ha.getValue hresult
    cases value <;> simp_all
    grind

theorem Assignment.InBounds.bindValues {a b : Assignment OpCode} {ctx : IRContext OpCode}
    {handles : List (Handle OpCode .value)} {values : List ValuePtr}
    (ha : a.InBounds ctx) (h : a.bindValues handles values = some b)
    (hv : ∀ value ∈ values, value.InBounds ctx) : b.InBounds ctx := by
  induction handles generalizing a values with
  | nil => cases values <;> simp_all [Assignment.bindValues]
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindValues] at h
    | cons value values =>
      simp only [Assignment.bindValues, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hb, hr⟩ := h
      exact ih (ha.bind hb (hv value (by simp))) hr (by intro v hm; exact hv v (by simp [hm]))

theorem Assignment.InBounds.bindTypes {a b : Assignment OpCode} {ctx : IRContext OpCode}
    {handles : List (Handle OpCode .type)} {values : List TypeAttr}
    (ha : a.InBounds ctx) (h : a.bindTypes handles values = some b) : b.InBounds ctx := by
  induction handles generalizing a values with
  | nil => cases values <;> simp_all [Assignment.bindTypes]
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindTypes] at h
    | cons value values =>
      simp only [Assignment.bindTypes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hb, hr⟩ := h
      exact ih (ha.bind hb trivial) hr

theorem MetadataTuple.Shape.inBounds_bind
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {a b : Assignment OpCode} {ctx : IRContext OpCode}
    (ha : a.InBounds ctx) (h : shape.bind a handles values = some b) : b.InBounds ctx := by
  induction shape generalizing a b with
  | unit => cases h; exact ha
  | atom atom => cases atom <;> exact ha.bind h trivial
  | cons head tail ih =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hh, ht⟩ := h
    have hm : middle.InBounds ctx := by
      cases head <;> exact ha.bind hh trivial
    exact ih _ _ hm ht

/-- Successful matching cannot introduce an invalid IR pointer. -/
theorem MatchDecl.inBounds_of_run (decl : MatchDecl OpCode)
    {ctx : WfIRContext OpCode} {a b : Assignment OpCode}
    (ha : a.InBounds ctx.raw) (h : decl.run ctx.raw a = some b) : b.InBounds ctx.raw := by
  cases decl with
  | operation code operands types matcher property op results hsize =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨matched, hmatched, a₁, h₁, a₂, h₂, u₁, _, u₂, _, a₃, h₃, u₃, _, a₄, h₄, u₄, _, h₅⟩ := h
    have hm := ha.findOp hmatched
    have ha₁ := ha.bind h₁ hm
    have ha₂ := ha₁.bindValues h₂ (by intro v hv; grind)
    exact ((ha₂.bind h₃ trivial).bindTypes h₄).bindValues h₅ (by intro v hv; grind)
  | value type value =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    exact ha.bind h trivial
  | type matcher type =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨_, _, _, _, heq⟩ := h
    cases heq
    exact ha
  | inspectOperation op inspect outputs =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h
    exact MetadataTuple.Shape.inBounds_bind _ _ _ ha h
  | applyNative inputs predicate =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨_, _, _, _, heq⟩ := h
    cases heq
    exact ha

theorem MatchProg.inBounds_of_runDecls (decls : List (MatchDecl OpCode))
    {ctx : WfIRContext OpCode} {a b : Assignment OpCode}
    (ha : a.InBounds ctx.raw) (h : MatchProg.runDecls decls ctx.raw a = some b) :
    b.InBounds ctx.raw := by
  induction decls generalizing a with
  | nil => cases h; exact ha
  | cons decl decls ih =>
    simp only [MatchProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hd, hr⟩ := h
    exact ih (decl.inBounds_of_run ha hd) hr

/-- Starting from a valid root, every pointer returned by the matcher is in bounds. -/
theorem MatchProg.inBounds_of_run (prog : MatchProg OpCode α)
    {ctx : WfIRContext OpCode} {root : OperationPtr} {a : Assignment OpCode}
    (hroot : root.InBounds ctx.raw) (h : prog.run ctx.raw root = some a) :
    a.InBounds ctx.raw := by
  unfold MatchProg.run at h
  split at h <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  all_goals
    repeat first | obtain ⟨_, _, h⟩ := h
    exact MatchProg.inBounds_of_runDecls _
      ((Assignment.empty_inBounds prog.numHandles ctx.raw).bind
        (binding := .op root) (by assumption) hroot) h

end Veir.Puddle
