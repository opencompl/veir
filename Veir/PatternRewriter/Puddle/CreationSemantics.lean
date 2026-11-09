module

public import Veir.PatternRewriter.Puddle.SemanticAssignmentLemmas
public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.Rewriter.WfRewriter.GetSet
public import Veir.Rewriter.WfRewriter.InBounds
import all Veir.IR.Basic
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.PatternRewriter.Puddle.CTreeValidity

namespace Veir.Puddle

public section

/-- A runtime interpretation of SSA value pointers. -/
abbrev ValueResolver := ValuePtr → Option RuntimeValue

/-- Bind the results of one fresh operation, preserving every other pointer's interpretation. -/
@[expose]
def ValueResolver.setResults (resolve : ValueResolver) (op : OperationPtr)
    (values : Array RuntimeValue) : ValueResolver := fun pointer =>
  match pointer with
  | .opResult result => if result.op = op then values[result.index]? else resolve pointer
  | .blockArgument _ => resolve pointer

@[simp]
theorem ValueResolver.setResults_getResult (resolve : ValueResolver) (op : OperationPtr)
    (values : Array RuntimeValue) (i : Nat) :
    resolve.setResults op values (.opResult (op.getResult i)) = values[i]? := by
  simp [setResults, OperationPtr.getResult]

/-- Result extension for a freshly allocated operation leaves all old pointers unchanged. -/
theorem ValueResolver.setResults_of_inBounds (resolve : ValueResolver) (op : OperationPtr)
    (values : Array RuntimeValue) {ctx : WfIRContext OpCode} {pointer : ValuePtr}
    (hptr : pointer.InBounds ctx.raw) (hfresh : ¬op.InBounds ctx.raw) :
    resolve.setResults op values pointer = resolve pointer := by
  cases pointer with
  | blockArgument => rfl
  | opResult result =>
    have hne : result.op ≠ op := by grind
    simp [setResults, hne]

/-- Concrete binding changes exactly the designated slot. -/
theorem Assignment.getBinding_of_bind_of_ne {a b : Assignment OpCode}
    {kind otherKind : HandleType OpCode} {handle : Handle OpCode kind}
    (other : Handle OpCode otherKind) {binding : Binding OpCode}
    (h : a.bind handle binding = some b) (hne : other.id ≠ handle.id) :
    b.getBinding other = a.getBinding other := by
  unfold Assignment.bind at h
  split at h
  · split at h
    · cases h
      simp only [Assignment.getBinding]
      congr 1
      grind
    · split at h
      · cases h; rfl
      · contradiction
  · cases h
    simp only [Assignment.getBinding, Array.getElem?_push, Array.getElem?_append,
      Array.size_append, Array.size_replicate]
    repeat split
    all_goals simp_all
    all_goals grind

/-- A successful concrete type binding commutes with semantic denotation. -/
theorem Assignment.denote_bindType {a b : Assignment OpCode} {handle : Handle OpCode .type}
    {value : TypeAttr} (resolve : ValuePtr → Option RuntimeValue)
    (h : a.bindType handle value = some b)
    (typeOf : ValuePtr → TypeAttr) :
    b.denote resolve typeOf = (a.denote resolve typeOf).bindType handle value := by
  funext id
  by_cases heq : id = handle.id
  · subst id
    change (b.getBinding handle >>= Binding.denote resolve typeOf) = _
    rw [Assignment.getBinding_of_bind h]
    simp [Binding.denote, SemanticAssignment.bindType, SemanticAssignment.bind]
  · have hn := Assignment.getBinding_of_bind_of_ne (other := Handle.mk (handleType := .type) id) h heq
    change (b.getBinding (Handle.mk (handleType := .type) id) >>= Binding.denote resolve typeOf) = _
    rw [hn]
    simp [SemanticAssignment.bindType, SemanticAssignment.bind, heq, Assignment.denote,
      Assignment.getBinding]

/-- A successful concrete property binding commutes with semantic denotation. -/
theorem Assignment.denote_bindProperty {a b : Assignment OpCode} {code : OpCode}
    {handle : Handle OpCode (.prop code)} {value : propertiesOf code}
    (resolve : ValuePtr → Option RuntimeValue)
    (h : a.bindProperty handle value = some b)
    (typeOf : ValuePtr → TypeAttr) :
    b.denote resolve typeOf = (a.denote resolve typeOf).bindProperty handle value := by
  funext id
  by_cases heq : id = handle.id
  · subst id
    change (b.getBinding handle >>= Binding.denote resolve typeOf) = _
    rw [Assignment.getBinding_of_bind h]
    simp [Binding.denote, SemanticAssignment.bindProperty, SemanticAssignment.bind]
  · have hn := Assignment.getBinding_of_bind_of_ne (other := Handle.mk (handleType := .type) id) h heq
    change (b.getBinding (Handle.mk (handleType := .type) id) >>= Binding.denote resolve typeOf) = _
    rw [hn]
    simp [SemanticAssignment.bindProperty, SemanticAssignment.bind, heq, Assignment.denote,
      Assignment.getBinding]

/-- Operation handles carry no runtime semantic value, so binding one leaves denotation unchanged. -/
theorem Assignment.denote_bindOp {a b : Assignment OpCode} {handle : Handle OpCode .op}
    {op : OperationPtr} (resolve : ValueResolver) (h : a.bindOp handle op = some b)
    (typeOf : ValuePtr → TypeAttr) :
    b.denote resolve typeOf = a.denote resolve typeOf := by
  have hbinding := Assignment.getBinding_of_bind h
  have hold : (a.denote resolve typeOf) handle.id = none := by
    unfold Assignment.bindOp Assignment.bind at h
    split at h
    · split at h
      · simp_all [Assignment.denote, getElem?_pos]
      · split at h
        · cases h
          change (a.getBinding handle >>= Binding.denote resolve typeOf) = none
          rw [hbinding]
          rfl
        · contradiction
    · simp_all [Assignment.denote, getElem?_neg]
  funext id
  by_cases heq : id = handle.id
  · subst id
    change (b.getBinding handle >>= Binding.denote resolve typeOf) = _
    rw [Assignment.getBinding_of_bind h, hold]
    rfl
  · have hn := Assignment.getBinding_of_bind_of_ne
      (other := Handle.mk (handleType := .type) id) h heq
    change (b.getBinding (Handle.mk (handleType := .type) id) >>= Binding.denote resolve typeOf) = _
    rw [hn]
    rfl

/-- A successfully resolved concrete value binding agrees with semantic value binding. -/
theorem Assignment.denote_bindValue {a b : Assignment OpCode} {handle : Handle OpCode .value}
    {pointer : ValuePtr} {value : RuntimeValue} (resolve : ValuePtr → Option RuntimeValue)
    (h : a.bindValue handle pointer = some b) (hresolve : resolve pointer = some value)
    (typeOf : ValuePtr → TypeAttr) :
    b.denote resolve typeOf = (a.denote resolve typeOf).bindValue handle value (typeOf pointer) := by
  funext id
  by_cases heq : id = handle.id
  · subst id
    change (b.getBinding handle >>= Binding.denote resolve typeOf) = _
    rw [Assignment.getBinding_of_bind h]
    simp [Binding.denote, hresolve, SemanticAssignment.bindValue, SemanticAssignment.bind]
  · have hn := Assignment.getBinding_of_bind_of_ne
      (other := Handle.mk (handleType := .type) id) h heq
    change (b.getBinding (Handle.mk (handleType := .type) id) >>= Binding.denote resolve typeOf) = _
    rw [hn]
    simp [SemanticAssignment.bindValue, SemanticAssignment.bind, heq, Assignment.denote,
      Assignment.getBinding]

/-- Successful result-handle binding translates to typed semantic result binding. -/
theorem Assignment.denote_bindValues {a b : Assignment OpCode}
    {handles : List (Handle OpCode .value)} {pointers : List ValuePtr}
    (resolve : ValuePtr → Option RuntimeValue) (values : Array RuntimeValue) (index : Nat)
    (h : a.bindValues handles pointers = some b)
    (hresolve : ∀ i, i < handles.length → resolve pointers[i]! = some values[index + i]!)
    (typeOf : ValuePtr → TypeAttr) :
    SemanticAssignment.bindValues values (a.denote resolve typeOf) handles (pointers.map typeOf) index =
      some (b.denote resolve typeOf) := by
  induction handles generalizing a pointers index with
  | nil =>
    cases pointers <;> simp_all [Assignment.bindValues, SemanticAssignment.bindValues]
  | cons handle handles ih =>
    cases pointers with
    | nil => simp [Assignment.bindValues] at h
    | cons pointer pointers =>
      simp only [Assignment.bindValues, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hb, hr⟩ := h
      have hfirst : resolve pointer = some values[index]! := by simpa using hresolve 0 (by simp)
      have hrest : ∀ i, i < handles.length →
          resolve pointers[i]! = some values[index + 1 + i]! := by
        intro i hi
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresolve (i + 1) (by simpa using hi)
      simp only [List.map_cons, SemanticAssignment.bindValues]
      rw [← Assignment.denote_bindValue resolve hb hfirst typeOf]
      exact ih (index := index + 1) hr hrest

/-- Result binding preserves the supplied declared types and rejects mismatched lengths. -/
theorem Assignment.denote_bindValues_typed {a b : Assignment OpCode}
    {handles : List (Handle OpCode .value)} {pointers : List ValuePtr}
    (resolve : ValuePtr → Option RuntimeValue) (values : Array RuntimeValue) (index : Nat)
    (h : a.bindValues handles pointers = some b)
    (hresolve : ∀ i, i < handles.length → resolve pointers[i]! = some values[index + i]!)
    (typeOf : ValuePtr → TypeAttr) (types : List TypeAttr)
    (htypes : pointers.map typeOf = types) :
    SemanticAssignment.bindValues values (a.denote resolve typeOf) handles types index =
      some (b.denote resolve typeOf) := by
  rw [← htypes]
  exact Assignment.denote_bindValues resolve values index h hresolve typeOf

/-- Changing the resolver outside pointers present in an assignment leaves its denotation unchanged. -/
theorem Assignment.denote_congr_resolve (a : Assignment OpCode)
    (resolve resolve' : ValuePtr → Option RuntimeValue)
    (h : ∀ (id : Nat) (pointer : ValuePtr), a.bindings[id]?.join = some (.value pointer) →
      resolve pointer = resolve' pointer)
    (typeOf : ValuePtr → TypeAttr) :
    a.denote resolve typeOf = a.denote resolve' typeOf := by
  funext id
  unfold Assignment.denote
  cases hb : a.bindings[id]?.join with
  | none => rfl
  | some binding =>
    cases binding with
    | value pointer =>
      change (resolve pointer).map (fun value => SemanticBinding.value value (typeOf pointer)) = (resolve' pointer).map (fun value => SemanticBinding.value value (typeOf pointer))
      rw [h id pointer hb]
    | op _ => rfl
    | type _ => rfl
    | property _ _ => rfl

/-- Denotation depends only on types of pointers present in the assignment. -/
theorem Assignment.denote_congr_typeOf (a : Assignment OpCode) (resolve : ValueResolver)
    (typeOf typeOf' : ValuePtr → TypeAttr)
    (h : ∀ (id : Nat) (pointer : ValuePtr), a.bindings[id]?.join = some (.value pointer) →
      typeOf pointer = typeOf' pointer) :
    a.denote resolve typeOf = a.denote resolve typeOf' := by
  funext id
  unfold Assignment.denote
  cases hb : a.bindings[id]?.join with
  | none => rfl
  | some binding =>
    cases binding with
    | value pointer =>
      change (resolve pointer).map (fun v => SemanticBinding.value v (typeOf pointer)) =
        (resolve pointer).map (fun v => SemanticBinding.value v (typeOf' pointer))
      rw [h id pointer hb]
    | op _ => rfl
    | type _ => rfl
    | property _ _ => rfl

/-- Fresh-result extension preserves the denotation of any bounds-respecting old assignment. -/
theorem Assignment.denote_setResults_of_fresh (a : Assignment OpCode) (resolve : ValueResolver)
    (op : OperationPtr) (values : Array RuntimeValue) {ctx : WfIRContext OpCode}
    (hbound : ∀ (id : Nat) (pointer : ValuePtr), a.bindings[id]?.join = some (.value pointer) →
      pointer.InBounds ctx.raw) (hfresh : ¬op.InBounds ctx.raw)
    (typeOf : ValuePtr → TypeAttr) :
    a.denote (resolve.setResults op values) typeOf = a.denote resolve typeOf := by
  apply Assignment.denote_congr_resolve
  intro id pointer hb
  exact ValueResolver.setResults_of_inBounds resolve op values (hbound id pointer hb) hfresh

/-- Resolving freshly bound result handles reads the new result array and its declared types. -/
theorem Assignment.denote_bindOpResults {a middle b : Assignment OpCode}
    {opHandle : Handle OpCode .op} {handles : Array (Handle OpCode .value)}
    {op : OperationPtr} {ctx : IRContext OpCode}
    (resolve : ValueResolver) (values : Array RuntimeValue)
    (hop : a.bindOp opHandle op = some middle)
    (hbind : middle.bindValues handles.toList (op.getResults! ctx).toList = some b)
    (hsize : values.size = op.getNumResults! ctx) (typeOf : ValuePtr → TypeAttr) :
    SemanticAssignment.bindValues values (a.denote (resolve.setResults op values) typeOf)
      handles.toList ((op.getResults! ctx).toList.map typeOf) =
      some (b.denote (resolve.setResults op values) typeOf) := by
  have hresolve : ∀ i, i < handles.toList.length →
      resolve.setResults op values (op.getResults! ctx).toList[i]! = some values[0 + i]! := by
    intro i hi
    have hlen := Assignment.bindValues_length hbind
    have hopi : i < op.getNumResults! ctx := by
      simp only [Array.length_toList, OperationPtr.getResults!.size_eq_getNumResults!] at hlen hi
      omega
    have hvali : i < values.size := by omega
    simpa only [Array.getElem!_toList, OperationPtr.getResults!.getElem!_eq_getResult hopi,
      ValueResolver.setResults_getResult, Nat.zero_add]
      using (show values[i]? = some values[i]! from by simp [hvali])
  simpa only [Assignment.denote_bindOp _ hop typeOf] using
    Assignment.denote_bindValues (resolve.setResults op values) values 0 hbind hresolve typeOf

/-- New typed result bindings preserve the denotation of existing SSA values. -/
theorem Assignment.denote_bindFreshOpResults {a middle b : Assignment OpCode}
    {opHandle : Handle OpCode .op} {handles : Array (Handle OpCode .value)}
    {op : OperationPtr} {oldCtx newCtx : WfIRContext OpCode}
    (resolve : ValueResolver) (values : Array RuntimeValue)
    (hop : a.bindOp opHandle op = some middle)
    (hbind : middle.bindValues handles.toList (op.getResults! newCtx.raw).toList = some b)
    (hsize : values.size = op.getNumResults! newCtx.raw)
    (hbound : ∀ (id : Nat) (pointer : ValuePtr), a.bindings[id]?.join = some (.value pointer) →
      pointer.InBounds oldCtx.raw) (hfresh : ¬op.InBounds oldCtx.raw)
    (typeOf : ValuePtr → TypeAttr) :
    SemanticAssignment.bindValues values (a.denote resolve typeOf) handles.toList
      ((op.getResults! newCtx.raw).toList.map typeOf) =
      some (b.denote (resolve.setResults op values) typeOf) := by
  simpa only [Assignment.denote_setResults_of_fresh a resolve op values hbound hfresh typeOf] using
    Assignment.denote_bindOpResults resolve values hop hbind hsize typeOf

/-- Resolving any metadata tuple commutes with runtime-value denotation. -/
theorem MetadataTuple.Shape.resolve_denote
    (shape : MetadataTuple.Shape OpCode Handles) (a : Assignment OpCode) (handles : Handles)
    (resolve : ValuePtr → Option RuntimeValue)
    (typeOf : ValuePtr → TypeAttr) :
    shape.resolveSemantic (a.denote resolve typeOf) handles = shape.resolve a handles := by
  induction shape with
  | unit => rfl
  | atom atom =>
    cases atom
    · exact Assignment.denote_getType _ _ _ typeOf
    · exact Assignment.denote_getProperty _ _ _ typeOf
  | cons head tail ih =>
    cases head <;> simp only [MetadataTuple.Shape.resolveSemantic, MetadataTuple.Shape.resolve,
      MetadataTuple.Atom.resolveSemantic, MetadataTuple.Atom.resolve, Assignment.denote_getType,
      Assignment.denote_getProperty, ih]

/-- Successful metadata tuple binding agrees exactly with semantic tuple binding. -/
theorem MetadataTuple.Shape.denote_bind
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {a b : Assignment OpCode} (resolve : ValuePtr → Option RuntimeValue)
    (h : shape.bind a handles values = some b)
    (typeOf : ValuePtr → TypeAttr) :
    b.denote resolve typeOf = shape.bindSemantic (a.denote resolve typeOf) handles values := by
  induction shape generalizing a b with
  | unit => cases h; rfl
  | atom atom =>
    cases atom
    · exact Assignment.denote_bindType resolve h typeOf
    · exact Assignment.denote_bindProperty resolve h typeOf
  | cons head tail ih =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hh, ht⟩ := h
    rw [ih _ _ ht]
    cases head
    · rw [Assignment.denote_bindType resolve hh typeOf]; rfl
    · rw [Assignment.denote_bindProperty resolve hh typeOf]; rfl

/-- Metadata resolution ignores the runtime values assigned to SSA pointers. -/
theorem MetadataTuple.resolve_denote {Handles : Type} [self : IsMetadataTuple OpCode Handles]
    (a : Assignment OpCode) (handles : Handles) (resolve : ValuePtr → Option RuntimeValue)
    (typeOf : ValuePtr → TypeAttr) :
    MetadataTuple.resolveSemantic (a.denote resolve typeOf) handles = MetadataTuple.resolve a handles :=
  self.shape.resolve_denote a handles resolve typeOf

/-- A successful concrete metadata binding translates to the semantic metadata binding. -/
theorem MetadataTuple.denote_bind {Handles : Type} [self : IsMetadataTuple OpCode Handles]
    {a b : Assignment OpCode} (handles : Handles) (values : MetadataValues OpCode Handles)
    (resolve : ValuePtr → Option RuntimeValue)
    (h : MetadataTuple.bind a handles values = some b)
    (typeOf : ValuePtr → TypeAttr) :
    b.denote resolve typeOf = MetadataTuple.bindSemantic (a.denote resolve typeOf) handles values :=
  self.shape.denote_bind handles values resolve h typeOf

/-- Successful metadata-only creation has exactly the CPS semantics of its final denotation. -/
theorem CTree.CreateDecl.semantics_of_run_metadata
    (decl : CreateDecl OpCode) {a b : Assignment OpCode} {ctx newCtx : WfIRContext OpCode}
    {newOps : Array OperationPtr} (resolve : ValuePtr → Option RuntimeValue)
    (memory : MemoryState) (next : SemanticAssignment → MemoryState → Tree α)
    (hmeta : match decl with | .operation .. => False | _ => True)
    (h : decl.run a ctx = some (newCtx, newOps, b))
    (typeOf : ValuePtr → TypeAttr) :
    newCtx = ctx ∧ newOps = #[] ∧
      CTree.CreateDecl.semantics decl (a.denote resolve typeOf) memory next =
        next (b.denote resolve typeOf) memory := by
  cases decl with
  | operation => contradiction
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨bound, hb, heq⟩ := h
    cases heq
    exact ⟨rfl, rfl, congrArg (fun s => next s memory) (Assignment.denote_bindType resolve hb typeOf).symm⟩
  | property code value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨bound, hb, heq⟩ := h
    cases heq
    exact ⟨rfl, rfl, congrArg (fun s => next s memory) (Assignment.denote_bindProperty resolve hb typeOf).symm⟩
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨values, hresolve, outValues, hrewrite, bound, hbind, heq⟩ := h
    cases heq
    refine ⟨rfl, rfl, ?_⟩
    simp only [CTree.CreateDecl.semantics, MetadataTuple.resolve_denote,
      hresolve, Option.bind_eq_bind, Option.bind_some, hrewrite]
    rw [MetadataTuple.denote_bind outputs outValues resolve hbind typeOf]

/-- The runtime/semantic bridge for complete metadata-only creation lists. -/
theorem CTree.CreateProg.semanticsDecls_of_run_metadata
    (decls : List (CreateDecl OpCode)) {a b : Assignment OpCode}
    {ctx newCtx : WfIRContext OpCode} {newOps : Array OperationPtr}
    (resolve : ValuePtr → Option RuntimeValue) (memory : MemoryState)
    (next : SemanticAssignment → MemoryState → Tree α)
    (hmeta : ∀ decl ∈ decls, match decl with | .operation .. => False | _ => True)
    (h : CreateProg.runDecls decls ctx a = some (newCtx, newOps, b))
    (typeOf : ValuePtr → TypeAttr) :
    newCtx = ctx ∧ newOps = #[] ∧
      CTree.CreateProg.semanticsDecls decls (a.denote resolve typeOf) memory next =
        next (b.denote resolve typeOf) memory := by
  induction decls generalizing a ctx newOps with
  | nil =>
    simp only [CreateProg.runDecls, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | cons decl decls ih =>
    simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨middleCtx, created, middle⟩, hd, ⟨finalCtx, restOps, final⟩, hr, heq⟩ := h
    cases heq
    have hdsem := CTree.CreateDecl.semantics_of_run_metadata decl resolve memory
      (fun s m => CTree.CreateProg.semanticsDecls decls s m next)
      (hmeta decl (by simp)) hd typeOf
    obtain ⟨rfl, rfl, hdsem⟩ := hdsem
    obtain ⟨hctx, hops, hrsem⟩ := ih (fun d hd => hmeta d (by simp [hd])) hr
    refine ⟨hctx, by simpa using hops, ?_⟩
    exact hdsem.trans hrsem

/-- The operation allocated by the creation runner has exactly its requested semantic fields. -/
theorem CTree.createOp_semantic_fields
    {ctx newCtx : WfIRContext OpCode} {code : OpCode}
    {types : Array TypeAttr} {operands : Array ValuePtr} {properties : propertiesOf code}
    {newOp : OperationPtr} {hin : ∀ operand ∈ operands, operand.InBounds ctx.raw}
    (h : WfRewriter.createOp ctx code types operands #[] #[] properties none hin =
      some (newCtx, newOp)) :
    newOp.getOpType! newCtx.raw = code ∧
    newOp.getResultTypes! newCtx.raw = types ∧
    newOp.getOperands! newCtx.raw = operands ∧
    newOp.getProperties! newCtx.raw code = properties := by
  have hcode := OperationPtr.getOpType!_WfRewriter_createOp h (operation := newOp)
  have htypes := OperationPtr.getResultTypes!_WfRewriter_createOp h (operation := newOp)
  have hoperands := OperationPtr.getOperands!_WfRewriter_createOp h (operation := newOp)
  have hproperties := OperationPtr.getProperties!_WfRewriter_createOp h
    (operation := newOp) (dialectOpType := code)
  simpa using And.intro hcode (And.intro htypes (And.intro hoperands hproperties))

end

end Veir.Puddle
