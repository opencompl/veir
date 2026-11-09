module

public import Veir.PatternRewriter.Puddle.Internal.CreationStructure
import all Veir.PatternRewriter.Puddle.Internal.CreationStructure
import all Veir.PatternRewriter.Puddle.Internal.ExecutionBounds
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.IR.Basic

public section
namespace Veir.Puddle

/-- A block argument has no defining operation to enqueue. -/
def ValueOwnerSatisfies (P : OperationPtr → Prop) (v : ValuePtr) : Prop :=
  ∀ op, v.definingOp? = some op → P op

private def Binding.Owners (P : OperationPtr → Prop) : Binding OpCode → Prop
  | .op ptr => P ptr
  | .value v => ValueOwnerSatisfies P v
  | _ => True

private def Assignment.Owners (a : Assignment OpCode) (P : OperationPtr → Prop) : Prop :=
  ∀ (id : Nat) (binding : Binding OpCode), a.bindings[id]?.join = some binding → binding.Owners P

private theorem Assignment.Owners.bind {a b : Assignment OpCode} {P : OperationPtr → Prop}
    (ha : a.Owners P) (h : a.bind handle binding = some b) (hb : binding.Owners P) : b.Owners P := by
  intro id old found
  let other : Handle OpCode .type := ⟨id⟩
  change b.getBinding other = some old at found
  by_cases eq : other.id = handle.id
  · have installed : b.getBinding other = some binding := by
      simpa [Assignment.getBinding, eq] using Assignment.getBinding_of_bind h
    exact Option.some.inj (installed.symm.trans found) ▸ hb
  · rw [Assignment.getBinding_of_bind_of_ne other h eq] at found
    exact ha id old found

private theorem Assignment.Owners.bindValues {a b : Assignment OpCode}
    (ha : a.Owners P) (h : a.bindValues hs vs = some b)
    (ok : ∀ v ∈ vs, ValueOwnerSatisfies P v) : b.Owners P := by
  induction hs generalizing a vs with
  | nil => cases vs <;> simp_all [Assignment.bindValues]
  | cons x xs ih =>
    cases vs with
    | nil => simp [Assignment.bindValues] at h
    | cons v vs =>
      obtain ⟨mid, first, rest⟩ := Option.bind_eq_some_iff.mp h
      exact ih (ha.bind first (ok v (by simp))) rest (fun w hw => ok w (by simp [hw]))

private theorem Assignment.Owners.bindTypes {a b : Assignment OpCode}
    (ha : a.Owners P) (h : a.bindTypes hs vs = some b) : b.Owners P := by
  induction hs generalizing a vs with
  | nil => cases vs <;> simp_all [Assignment.bindTypes]
  | cons x xs ih =>
    cases vs with
    | nil => simp [Assignment.bindTypes] at h
    | cons v vs =>
      obtain ⟨mid, first, rest⟩ := Option.bind_eq_some_iff.mp h
      exact ih (ha.bind first trivial) rest

private theorem MetadataTuple.Shape.owners (shape : MetadataTuple.Shape OpCode H)
    (handles : H) (values : shape.Values) {a b : Assignment OpCode}
    (ha : a.Owners P) (h : shape.bind a handles values = some b) : b.Owners P := by
  induction shape generalizing a b with
  | unit => cases h; exact ha
  | atom atom => cases atom <;> exact ha.bind h trivial
  | cons head tail ih =>
    obtain ⟨mid, first, rest⟩ := Option.bind_eq_some_iff.mp h
    apply ih _ _ (a := mid) ?_ rest
    cases head <;> exact ha.bind first trivial

private theorem Assignment.Owners.value {a : Assignment OpCode} (ha : a.Owners P)
    (h : a.getValue handle = some v) : ValueOwnerSatisfies P v := by
  unfold Assignment.getValue at h
  split at h <;> try contradiction
  cases h
  exact ha handle.id _ (by assumption)

private theorem Assignment.Owners.findOp {a : Assignment OpCode} (ha : a.Owners P)
    (h : a.findOp handle results = some op) : P op := by
  unfold Assignment.findOp at h
  split at h
  · cases h
    rename_i found
    unfold Assignment.getOp at found
    split at found <;> try contradiction
    cases found
    exact ha handle.id _ (by assumption)
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨v, found, h⟩ := h
    obtain ⟨_, _, get⟩ := Array.exists_of_findSome?_eq_some found
    cases v with
    | blockArgument => contradiction
    | opResult r => cases h; exact ha.value get r.op rfl

private theorem ownsResults {ctx : IRContext OpCode} (hop : P op) {v : ValuePtr}
    (mem : v ∈ op.getResults! ctx) : ValueOwnerSatisfies P v := by
  obtain ⟨i, _, rfl⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp mem
  simpa [ValueOwnerSatisfies, OperationPtr.getResult] using hop

private theorem MatchDecl.owners (decl : MatchDecl OpCode) {ctx : WfIRContext OpCode}
    (closed : ∀ op, op.InBounds ctx.raw → P op → ∀ v ∈ op.getOperands! ctx.raw, ValueOwnerSatisfies P v)
    (ha : a.Owners P) (bounds : a.InBounds ctx.raw) (h : decl.run ctx.raw a = some b) : b.Owners P := by
  cases decl with
  | operation code operands types matcher property op results count =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨matched, find, _, h₁, _, h₂, _, _, _, _, _, h₃, _, _, _, h₄, _, _, h₅⟩ := h
    have hm := ha.findOp find
    have ha₂ := (ha.bind h₁ hm).bindValues h₂ (fun _ mem => ownsResults hm (by simpa using mem))
    exact (((ha₂.bind h₃ trivial).bindTypes h₄).bindValues h₅
      (fun v mem => closed _ (bounds.findOp find) hm v (by simpa using mem)))
  | value ty v =>
    obtain ⟨_, _, hb⟩ := Option.bind_eq_some_iff.mp h
    exact ha.bind hb trivial
  | type matcher ty | applyNative _ _ =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    grind
  | inspectOperation op inspect outputs =>
    simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, hb⟩ := h
    exact MetadataTuple.Shape.owners _ _ _ ha hb

private theorem MatchProg.owners {ctx : WfIRContext OpCode} (prog : MatchProg OpCode α) {root : OperationPtr}
    (closed : ∀ op, op.InBounds ctx.raw → P op → ∀ v ∈ op.getOperands! ctx.raw, ValueOwnerSatisfies P v)
    (hr : P root) (hin : root.InBounds ctx.raw) (h : prog.run ctx.raw root = some a) : a.Owners P := by
  have loop (ds : List (MatchDecl OpCode)) {a b : Assignment OpCode} (ha : a.Owners P)
      (bounds : a.InBounds ctx.raw) (run : MatchProg.runDecls ds ctx.raw a = some b) : b.Owners P := by
    induction ds generalizing a with
    | nil => cases run; exact ha
    | cons d ds ih =>
      obtain ⟨mid, hd, rest⟩ := Option.bind_eq_some_iff.mp run
      exact ih (d.owners closed ha bounds hd) (d.inBounds_of_run bounds hd) rest
  have empty : (Assignment.empty OpCode prog.numHandles).Owners P := by
    intro id b hb
    by_cases hi : id < prog.numHandles <;> simp [Assignment.empty, hi] at hb
  unfold MatchProg.run at h
  split at h <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  all_goals
    repeat first | obtain ⟨_, _, h⟩ := h
    exact loop _ (empty.bind (binding := .op root) (by assumption) hr)
      ((Assignment.empty_inBounds prog.numHandles ctx.raw).bind (binding := .op root) (by assumption) hin) h

private theorem CreateDecl.owners (decl : CreateDecl OpCode) (ha : a.Owners P)
    (h : decl.run a ctx = some (next, ops, b)) (fresh : ∀ op ∈ ops, P op) : b.Owners P := by
  cases decl with
  | operation code operandHandles typeHandles prop opHandle results =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := h
    split at h <;> try contradiction
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨_, op⟩, _, _, hb, _, hv, eq⟩ := h
    cases eq
    have ok := fresh op (by simp)
    exact (ha.bind hb ok).bindValues hv (fun _ mem => ownsResults ok (by simpa using mem))
  | type _ _ | property _ _ _ =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, hb, eq⟩ := h
    cases eq
    exact ha.bind hb trivial
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, _, _, _, _, hb, eq⟩ := h
    cases eq
    exact MetadataTuple.Shape.owners _ _ _ ha hb

theorem Pattern.replacementOwners (rule : Pattern OpCode) {ctx : WfIRContext OpCode}
    (closed : ∀ op, op.InBounds ctx.raw → P op → ∀ v ∈ op.getOperands! ctx.raw, ValueOwnerSatisfies P v)
    (hr : P root) (hin : root.InBounds ctx.raw)
    (run : rule.interpret ctx root = some (next, some (ops, values))) (fresh : ∀ op ∈ ops, P op) :
    ∀ v ∈ values, ValueOwnerSatisfies P v := by
  have create (ds : List (CreateDecl OpCode)) {a b : Assignment OpCode} {ctx next ops}
      (ha : a.Owners P) (h : CreateProg.runDecls ds ctx a = some (next, ops, b))
      (fresh : ∀ op ∈ ops, P op) : b.Owners P := by
    induction ds generalizing ctx a ops with
    | nil => cases h; exact ha
    | cons d ds ih =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨⟨_, _, _⟩, hd, ⟨_, _, _⟩, rest, eq⟩ := h
      cases eq
      exact ih (d.owners ha hd (fun _ hm => fresh _ (by simp [hm]))) rest (fun _ hm => fresh _ (by simp [hm]))
  unfold Pattern.interpret at run
  split at run
  · cases run
  rename_i a matched
  split at run <;> try contradiction
  rename_i _ _ b created
  split at run <;> try contradiction
  rename_i _ returned
  cases run
  have final :=  create _ (rule.matcher.owners closed hr hin matched) created fresh
  intro v member
  simp only [Assignment.getValues, Array.mapM_eq_mapM_toList] at returned
  cases hm : rule.replacement.values.toList.mapM b.getValue with
  | none => simp [hm] at returned
  | some vs =>
    rw [hm] at returned
    change some vs.toArray = some _ at returned
    cases returned
    have go (hs : List (Handle OpCode .value)) (vs : List ValuePtr) (h : hs.mapM b.getValue = some vs)
        (mem : v ∈ vs) : ValueOwnerSatisfies P v := by
      induction hs generalizing vs with
      | nil => simp_all
      | cons head tail ih =>
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
        obtain ⟨w, hw, ws, ht, eq⟩ := h
        cases eq
        rcases List.mem_cons.mp mem with rfl | mem
        · exact final.value hw
        · exact ih _ ht mem
    exact go _ _ hm (by simpa using member)

end Veir.Puddle
